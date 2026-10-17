# SPDX-License-Identifier: Apache-2.0
"""The counting index, checked the way `rust/crates/algodesign/src/strings/count_index.rs` checks it.

The property tests mirror that module's proptests and the fixed cases mirror the ones it pins.
`_naive_select` lives here for the reason `test_bwt`'s `walk_from` does: it is the other side of
one differential and not a function the chapter ships.

**Every test here reaches past block 0 of superblock 0**, or it would test the fallback scan and
nothing else: a query inside the first block never consults the superblock and block lists. So the
generators draw the query position inside the input (`bits_and_position`, `text_and_position`),
and the deterministic probes run on `_long_bits`, three superblocks and more, at every block and
superblock boundary. The generated rows supply variety; the fixed probes supply repeatability, a
fixed vector and probe list that either always catch a fault or never do. `_long_bits` says what
those probes cannot see.

**Four of the Rust's tests have nothing to mirror**: `a_partial_last_word_is_masked` (a bitvector
here is one entry per bit, so there is no partial word), `select_in_word_matches_a_bit_scan` (no
word to search inside), `alphabet_is_a_dense_ascending_bijection` (no dense-index map --
`symbols` being ascending is checked instead, since the FM-index's `C` array reads it), and the two
`overhead_bytes` tests (they measure a packed layout, and this is not one).
"""

from collections.abc import Sequence

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.strings import naive
from algodesign.strings.count_index import (
    BLOCK,
    BLOCKS_PER_SUPERBLOCK,
    SUPERBLOCK,
    BitIndex,
    ByteIndex,
)

from .cost_probes import CountingBits, RecordingBytes
from .reach import inputs_reaching

# Long enough to cross several superblocks at the widths this module ships, and not a multiple of
# either, so the last block and the last superblock are both partial.
LONG = 3 * SUPERBLOCK + 5

# Every boundary a query can land on or just beside, plus the ends.
BOUNDARIES = sorted(
    probe
    for probe in (
        {0, 1, LONG - 1, LONG, LONG + 7}
        | {at + step for at in range(0, LONG + 1, BLOCK) for step in (-1, 0, 1)}
        | {at + step for at in range(0, LONG + 1, SUPERBLOCK) for step in (-1, 0, 1)}
    )
    if probe >= 0
)

bit_lists = st.lists(st.integers(min_value=0, max_value=1), max_size=200)
"""Bitvectors as one entry per bit, up to 200 of them -- three superblocks and a bit."""

texts = st.binary(max_size=200)
"""Texts, at the same length."""


@st.composite
def bits_and_position(draw: st.DrawFn) -> tuple[list[int], int]:
    """A bitvector and a position **inside it**: `0 <= i <= len(bits)`.

    A position drawn from a fixed range, independently of the vector, would land past the end
    most of the time, where `rank` takes its saturating early return and never consults the
    directory. Tying the position to the input is what makes the generated rows reach it.

    The out-of-range case is real behaviour and is kept, deliberately and on its own, in
    `test_rank_and_occ_saturate_past_the_end`. It just should not be four draws in five of the
    differential.
    """
    bits = draw(bit_lists)
    return bits, draw(st.integers(min_value=0, max_value=len(bits)))


@st.composite
def bits_and_two_positions(draw: st.DrawFn) -> tuple[list[int], int, int]:
    """A bitvector and two positions inside it, in order. See `bits_and_position`."""
    bits = draw(bit_lists)
    inside = st.integers(min_value=0, max_value=len(bits))
    first, second = draw(inside), draw(inside)
    return bits, min(first, second), max(first, second)


@st.composite
def text_and_position(draw: st.DrawFn) -> tuple[bytes, int]:
    """A text and a position inside it. See `bits_and_position`; the same sampling put **95 %** of
    `st.binary(max_size=250)` draws past the end and 0.3 % on a non-zero block term."""
    text = draw(texts)
    return text, draw(st.integers(min_value=0, max_value=len(text)))


def _long_bits() -> list[int]:
    """A deterministic bitvector of `LONG` bits with set bits at irregular spacing.

    Irregular on purpose: a pattern whose period divides `BLOCK` gives every block the same
    count, and a directory that mixed its two levels up would still answer correctly against it.
    Period 7 against a block of 8 means the per-block counts vary, and `(i * i) % 7 < 3` leaves
    `select` plenty to find.

    **What it cannot see, stated rather than left to be found.** This vector is *dense* -- every
    one of its 25 blocks holds at least four set bits, none is empty. A directory fault that only
    shows up when a superblock *begins* with empty blocks is therefore invisible to both
    `test_rank_is_probed_at_every_boundary` and `test_occ_is_probed_at_every_boundary`, however
    many boundaries they probe: `locate` returning the first block when `j == base` is one such
    fault. The fixed case that catches it deterministically is
    `test_select_past_the_last_set_bit_is_none`, whose vector is 19 empty blocks out of 21. So
    "the boundary probes are the deterministic half" is true of the two faults they are aimed at
    and is not a general backstop; sparse vectors are a different shape and need their own fixed
    case.
    """
    return [1 if (i * i) % 7 < 3 else 0 for i in range(LONG)]


def _long_text() -> bytes:
    """A deterministic text of `LONG` bytes over five symbols, unevenly distributed."""
    return bytes(2 + (i * i + i // 3) % 5 for i in range(LONG))


def _naive_select(bits: Sequence[int], j: int) -> int | None:
    """The `j`-th set position by scanning, the differential for `select` the way `naive.rank` is
    the differential for `rank`."""
    seen = 0
    for position, bit in enumerate(bits):
        if bit:
            if seen == j:
                return position
            seen += 1
    return None


def test_the_widths_are_a_whole_number_of_blocks() -> None:
    """A superblock that was not a whole number of blocks would give its last block a relative
    count taken against the wrong base. The Rust checks this at compile time."""
    assert SUPERBLOCK % BLOCK == 0
    assert BLOCKS_PER_SUPERBLOCK == SUPERBLOCK // BLOCK


@given(bits_and_position())
def test_rank_matches_the_naive_count(case: tuple[list[int], int]) -> None:
    """The refinement as a differential: this two-level table computes the definitional count
    `naive.rank` spells out one bit at a time. `rankTwoLevel_eq` proves it for a `List Nat` model
    of this directory at any block width; this test is what reaches the code.

    The position is drawn inside the vector, which is what makes this a differential over the
    *directory* rather than over its saturating early return. `bits_and_position` records what
    that was worth.
    """
    bits, i = case
    assert BitIndex(bits).rank(i) == naive.rank(bits, i)


def test_rank_is_probed_at_every_boundary() -> None:
    """`rank` against `naive.rank` at every block and superblock boundary of a long vector.

    **Deterministic, which is the whole of its job**: a fixed vector and a fixed probe list catch
    a directory fault on every run, where a generated row has quiet runs. `_long_bits` says what
    this probe cannot see.
    """
    bits = _long_bits()
    index = BitIndex(bits)
    for i in BOUNDARIES:
        assert index.rank(i) == naive.rank(bits, i), f"rank({i})"
    assert max(BOUNDARIES) > BLOCK
    assert max(BOUNDARIES) > SUPERBLOCK


@given(bits_and_two_positions())
def test_rank_never_runs_backwards(case: tuple[list[int], int, int]) -> None:
    """Lean: `rank_mono`. It is also what makes both levels binary-searchable."""
    bits, low, high = case
    index = BitIndex(bits)
    assert index.rank(low) <= index.rank(high)


@given(bits_and_position())
def test_rank_counts_a_subset_of_what_it_looked_at(case: tuple[list[int], int]) -> None:
    """Lean: `rank_le` -- `rank b i <= i`."""
    bits, i = case
    assert BitIndex(bits).rank(i) <= i


@given(bit_lists, texts, st.integers(min_value=1, max_value=300))
def test_rank_and_occ_saturate_past_the_end(bits: list[int], text: bytes, over: int) -> None:
    """A position past the end answers with the count over the whole input, as the Lean's
    `List.take` does -- `rank [true, false] 100 = 1`.

    Pinned here, on its own, so that the generators above can spend their draws inside the input.
    """
    index = BitIndex(bits)
    assert index.rank(len(bits) + over) == index.rank(len(bits))
    byte_index = ByteIndex(text)
    for c in byte_index.symbols():
        assert byte_index.occ(c, len(text) + over) == byte_index.occ(c, len(text))


@given(bit_lists)
def test_rank_rises_by_exactly_the_bit_at_each_step(bits: list[int]) -> None:
    """Lean: `rank_succ`, which is the tail loop written out. Stated in the Lean for **every**
    `k`, including one past the end, where the bit reads `false` and neither side moves -- so the
    range below runs one step past `len(bits)` too."""
    index = BitIndex(bits)
    for k in range(len(bits) + 2):
        bit = bits[k] if k < len(bits) else 0
        assert index.rank(k + 1) == index.rank(k) + bit


@given(bit_lists)
def test_select_lands_on_a_set_bit_whose_rank_is_j(bits: list[int]) -> None:
    """Lean: `rank_select`, **both halves**. It is a conjunction -- the position `select` returns
    holds a set bit *and* its `rank` is `j` -- and a `select` answering with the clear position
    just before the right one passes the second half alone. The comparison against the scan pins
    uniqueness besides."""
    index = BitIndex(bits)
    total = index.rank(len(bits))
    for j in range(total):
        position = index.select(j)
        assert position is not None
        assert bits[position] == 1
        assert index.rank(position) == j
        assert position == _naive_select(bits, j)
    assert index.select(total) is None


@given(bit_lists)
def test_select_of_rank_returns_the_set_bit_it_was_asked_about(bits: list[int]) -> None:
    """The other direction of the round trip: at a set bit `i`, `select(rank(i)) == i`.

    **Lean: `select_rank`**, one line off the proved `select_eq_some_iff` (`RankSelect/`):
    its backward direction at `j := rank b i`. The Rust's test of the same name cites the same.
    """
    index = BitIndex(bits)
    for i, bit in enumerate(bits):
        if bit:
            assert index.select(index.rank(i)) == i


def test_select_is_probed_across_blocks_and_superblocks() -> None:
    """`select` over a long vector, against the scan, at every index -- so the sample-free
    two-level search is exercised in every superblock it has."""
    bits = _long_bits()
    index = BitIndex(bits)
    total = index.rank(len(bits))
    assert total > 2 * SUPERBLOCK // BLOCK
    for j in range(total):
        assert index.select(j) == _naive_select(bits, j), f"select({j})"
    assert index.select(total) is None


def test_select_reads_one_block_of_bits_at_most() -> None:
    """The directory finds the block; only that block's bits are read. A `select` that scans the
    vector for the `j`-th set bit gives the same answers and reads up to `n` bits, which is the
    algorithm the directory exists to replace. So every `select` here, the last set bit in the
    last superblock included, reads at most `BLOCK` bits."""
    bits = _long_bits()
    index = BitIndex(bits)
    counted = CountingBits(bits)
    index._bits = counted  # the same bits, read through a counter
    total = index.rank(len(bits))
    for j in range(total + 1):
        counted.reads = 0
        assert index.select(j) == _naive_select(bits, j), f"select({j})"
        assert counted.reads <= BLOCK, (j, counted.reads)


@given(bits_and_position())
def test_occ_is_rank_over_two_symbols(case: tuple[list[int], int]) -> None:
    """Lean: `occ_eq_rank` -- mapping a bitvector to the bytes `0`/`1` and asking `occ` for the
    symbol `1` gives back `rank`. This is the theorem that licenses one structure answering both.

    Both sides are held to the *definition* of rank, the set bits counted by a scan, and not to
    each other: the two classes share `_TwoLevel`, so comparing one with the other would pass
    whatever that shared directory did wrong. Symbol `0` is the complement."""
    bits, i = case
    definitional_rank = sum(bits[:i])
    assert BitIndex(bits).rank(i) == definitional_rank
    assert ByteIndex(bytes(bits)).occ(1, i) == definitional_rank
    assert ByteIndex(bytes(bits)).occ(0, i) == min(i, len(bits)) - definitional_rank


def test_occ_scans_forwards_from_the_checkpoint_below() -> None:
    """The tail of `occ(c, i)` reads exactly the positions from the start of `i`'s block up to
    `i`, forwards, and nothing else: the directory's checkpoint *below* `i`, then a scan, which is
    what makes `occ` literally `rank` over one more symbol. Scanning back from the next
    checkpoint when it is nearer gives the same answers from positions at or past `i`; it is a
    different procedure, and no source this chapter follows uses it.

    Every position of every block of the long text is probed, the upper half of each block --
    where a nearer-checkpoint scan would turn round -- included."""
    text = _long_text()
    index = ByteIndex(text)
    recorded = RecordingBytes(index.text())
    index._text = recorded
    for c in index.symbols():
        for i in range(len(text)):
            recorded.positions = []
            assert index.occ(c, i) == text[:i].count(bytes([c])), (c, i)
            start = i // BLOCK * BLOCK
            assert recorded.positions == list(range(start, i)), (c, i, recorded.positions)


@given(text_and_position())
def test_occ_matches_the_definition(case: tuple[bytes, int]) -> None:
    """`occ` over a real alphabet, against the count it is defined as."""
    text, i = case
    index = ByteIndex(text)
    for c in index.symbols():
        assert index.occ(c, i) == text[:i].count(bytes([c]))


def test_occ_is_probed_at_every_boundary() -> None:
    """`occ` at every block and superblock boundary of a long text: the `ByteIndex` half of the
    boundary probes."""
    text = _long_text()
    index = ByteIndex(text)
    assert len(index.symbols()) == 5
    for c in index.symbols():
        for i in BOUNDARIES:
            assert index.occ(c, i) == text[: min(i, len(text))].count(bytes([c])), f"occ({c},{i})"


@given(texts)
def test_symbols_are_the_distinct_bytes_ascending(text: bytes) -> None:
    """The FM-index's `C` array is a prefix sum of symbol counts *in symbol order*, so it will be
    built by walking this list left to right."""
    index = ByteIndex(text)
    assert index.symbols() == sorted(set(text))
    assert len(index) == len(text)
    assert index.text() == text


def test_the_empty_bitvector_answers_both_questions() -> None:
    index = BitIndex([])
    assert len(index) == 0
    assert index.rank(0) == 0
    assert index.rank(99) == 0  # saturating, as the Lean's `take` is
    assert index.select(0) is None


def test_all_zeros_has_no_set_bit_to_select() -> None:
    """Long enough that the directory really is built and really is empty."""
    index = BitIndex([0] * LONG)
    assert index.rank(LONG) == 0
    assert index.select(0) is None
    assert index.select(1_000_000) is None


def test_select_past_the_last_set_bit_is_none() -> None:
    """The Rust's fixed case, at these widths: set bits at 0, 1, 3 and inside the third
    superblock, so both levels are crossed to reach the last one."""
    bits = [0] * (2 * SUPERBLOCK + 40)
    for position in (0, 1, 3, 2 * SUPERBLOCK + 9):
        bits[position] = 1
    index = BitIndex(bits)
    assert index.rank(len(bits)) == 4
    assert [index.select(j) for j in range(5)] == [0, 1, 3, 2 * SUPERBLOCK + 9, None]
    assert index.select(10**6) is None


def test_a_symbol_outside_the_alphabet_never_occurs() -> None:
    index = ByteIndex(b"banana")
    assert index.occ(ord("z"), 6) == 0
    assert index.occ(ord("a"), 6) == 3
    assert index.occ(ord("a"), 99) == 3  # saturating
    empty = ByteIndex(b"")
    assert len(empty) == 0
    assert empty.symbols() == []
    assert empty.occ(ord("a"), 0) == 0


def test_a_negative_position_is_refused() -> None:
    """Lean's positions are `Nat`, so there is no saturating answer to mirror; Python would
    otherwise index from the right and answer a different question than the one asked."""
    with pytest.raises(ValueError, match="negative"):
        BitIndex([1, 0, 1]).rank(-1)
    with pytest.raises(ValueError, match="negative"):
        ByteIndex(b"banana").occ(ord("a"), -1)


def test_an_entry_that_is_not_a_bit_is_refused() -> None:
    with pytest.raises(ValueError, match="neither 0 nor 1"):
        BitIndex([0, 1, 2])


def test_the_property_tests_ask_inside_their_input_and_past_block_0() -> None:
    """What `test_rank_matches_the_naive_count` and `test_occ_matches_the_definition` are handed
    when they run, asserted rather than trusted: a position past the end gets the saturating early
    return and never reads the directory. Over 100 fixed runs of each test, every position must lie inside its input, some must
    reach past block 0, and the inputs must mix symbols: bitvectors holding both bits, texts
    holding several bytes. (No generated input reaches a second superblock; the boundary probes
    above are what do.)"""
    ranks = inputs_reaching(
        test_rank_matches_the_naive_count, BitIndex, "rank",
        lambda self, i: (len(self), i, len(set(self._bits))),
    )
    occs = inputs_reaching(
        test_occ_matches_the_definition, ByteIndex, "occ",
        lambda self, c, i: (len(self), i, len(self.symbols())),
    )
    for calls, floor, symbols in ((ranks, 0.10, 2), (occs, 0.05, 3)):
        assert len(calls) >= 50
        assert all(0 <= i <= n for n, i, _ in calls)
        assert sum(i >= BLOCK for _, i, _ in calls) >= floor * len(calls)
        assert sum(k >= symbols for n, _, k in calls if n >= BLOCK) >= 0.5 * sum(
            n >= BLOCK for n, _, _ in calls
        )
