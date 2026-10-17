# SPDX-License-Identifier: Apache-2.0
"""The FM-index: `count`, `locate`, `extract` and `is_valid`.

The generated tests mirror the Rust's proptests in `fm_index.rs`, including how their inputs are
sized (`_texts`), and the fixed cases mirror the ones it pins. Three oracles, one per question:
`naive.search` for `count` and `locate`, `suffix_array` for the sample walk, and slices of the
text for `extract`.

A test cites a theorem of `FMIndex/Search.lean` (`backwardSearch_eq`, `backwardSearch_spec`,
`fmCount_eq`, `fmLocate_perm`) only when its own inputs establish the three hypotheses those rest
on: `Terminated t s`, `SuffixArray.Valid ⟨t, sa⟩` and `s ∉ p.dropLast`. Here that means the test
appends the sentinel itself and draws from `ALPHABET`, which excludes it. A test that does not
cite names its reason:

1. *outside the hypotheses*: a sentinel before the pattern's end, or a text that is not
   terminated;
2. *the Lean states it only for a model*: `extract` and sampling (`fmExtract_eq` takes the row as
   a hypothesis; `locateSampled_eq` is over a `List Nat` model of the marks and values);
3. *nothing is claimed about one object*: two computations of the same suffix array compared.

Counting tests reach past block 0 and superblock 0 of the bitvectors `occ` ranks over, or they
would test only the fallback scan: `_long_text` is three superblocks and more, and `_texts` draws
long texts. The fixed cases on `banana$` and shorter pin refusals, early exits and the worked
example, none of which depends on the directory. The two bounds that keep queries short, the
locate walk and the bytes `extract` discards, are checked by tests of their own.
"""

from __future__ import annotations

from unittest import mock

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings import bwt, naive
from algodesign.strings._constants import SENTINEL
from algodesign.strings.chunked_wavelet import ChunkedWavelet
from algodesign.strings.count_index import SUPERBLOCK, BitIndex
from algodesign.strings.fm_index import SAMPLE, FMIndex
from algodesign.strings.fm_index_plain import PlainFMIndex
from algodesign.strings.rrr import RRR
from algodesign.strings.suffix_array import suffix_array

from .assembly import Index
from .assembly import assemble_fm as _assemble
from .assembly import fm_conjuncts as _conjuncts
from .assembly import fm_kept_parts as _kept_parts
from .assembly import fm_pieces as _pieces
from .reach import inputs_reaching

ALPHABET = (1, 2, 3, 4)
"""The bytes the generated texts and patterns are drawn from.

Four symbols, all of them above `SENTINEL`, which is what makes `s ∉ p.dropLast` hold for every
generated pattern and so makes the Lean cites below legitimate. The Rust draws `1u8..5`, the same
set.
"""


@st.composite
def _texts(draw: st.DrawFn) -> bytes:
    """Sentinel-terminated texts of up to 300 bytes, with the **length drawn first**.

    The Rust's `prop::collection::vec(1u8..5, 1..300)` picks its length uniformly over the range,
    as this does. `st.lists(min_size=1, max_size=299)` would not: Hypothesis biases collection
    sizes small, and its texts (median length about 5) never reach past `SUPERBLOCK`. Drawn this
    way, about two thirds of the `occ` positions a count asks for are past `BLOCK` and between two
    fifths and a half past `SUPERBLOCK`.
    """
    length = draw(st.integers(min_value=1, max_value=299))
    body = draw(st.lists(st.integers(min_value=1, max_value=4), min_size=length, max_size=length))
    return bytes(body) + bytes([SENTINEL])


texts = _texts()
"""Sentinel-terminated texts of up to 300 bytes -- the Rust's range, drawn the Rust's way."""



patterns = st.lists(st.integers(min_value=1, max_value=4), min_size=1, max_size=5).map(bytes)
"""Non-empty patterns over the same alphabet. The empty pattern is a fixed case, not a drawn one:
`naive.search` over the terminated bytes counts one shift more than the index has rows (the one
past the sentinel), so it is pinned against the text length instead."""


def _long_text() -> bytes:
    """A deterministic text of `3 * SUPERBLOCK + 5` bytes plus a sentinel.

    198 positions: three full superblocks of the `occ` directory and into a fourth, and seven
    samples at rate 32. That is what it takes for a probe to reach the two-level
    directory *and* a non-trivial LF walk.

    The body is arithmetic rather than random, so it is the same text on every run and in every
    checkout, and it is **aperiodic** on purpose: the Thue-Morse word -- the parity of the bits of
    the position -- doubled by a slower square wave onto four symbols. A short period would make
    the sweeps below trivial by giving them a handful of distinct substrings to find; this carries
    13 of the 16 two-byte substrings over `ALPHABET` and 26 of the 64 three-byte ones, and it has
    runs like `44` and `33`, which is what gives backward search intervals wider than one row.
    """
    body = bytes(
        1 + bin(index).count("1") % 2 + 2 * (index // 7 % 2)
        for index in range(3 * SUPERBLOCK + 5)
    )
    return body + bytes([SENTINEL])


def _short_patterns(max_length: int) -> list[bytes]:
    """Every pattern of length `1..max_length` over `ALPHABET`, in order. Deterministic."""
    out: list[bytes] = []
    current: list[bytes] = [b""]
    for _ in range(max_length):
        current = [prefix + bytes([symbol]) for prefix in current for symbol in ALPHABET]
        out.extend(current)
    return out


# --- Generated --------------------------------------------------------------------------------


@given(texts, patterns)
@settings(deadline=None)
def test_count_and_locate_match_naive(text: bytes, pattern: bytes) -> None:
    """Generated. Mirrors `count_and_locate_match_naive`.

    Lean: `fmCount_eq` for the count and `fmLocate_perm` for the positions. All three hypotheses
    hold: `Terminated t s` because the test appends exactly one `SENTINEL` and `FMIndex` re-checks
    it through `bwt.encode`, `SuffixArray.Valid ⟨t, sa⟩` for the array `suffix_array` builds inside
    `bwt.encode` -- as far as that module's own citation reaches -- and `s ∉ p.dropLast` because
    `patterns` draws from `ALPHABET`, which excludes the sentinel.

    `fmLocate_perm` concludes a **permutation**, not an equality, which is why this sorts before
    comparing: the interval's rows come out in suffix order, and the fixed case
    `test_locate_reports_in_suffix_order_not_text_order` pins that they really do.
    """
    index = FMIndex(text, SAMPLE)
    expected = naive.search(text, pattern)
    assert index.count(pattern) == len(expected)
    assert sorted(index.locate(pattern)) == expected


@given(texts, st.integers(min_value=0, max_value=300), st.integers(min_value=0, max_value=50))
@settings(deadline=None)
def test_extract_reproduces_the_text(text: bytes, start: int, length: int) -> None:
    """Generated. Mirrors `extract_reproduces_the_text`.

    No Lean cite -- **reason 2**. `fmExtract_eq` proves the walk on the unsampled index from a row
    it is handed; how this index finds that row, its text sample, is not modelled. So a slice of
    the text is the oracle -- which is fair, since reproducing that slice *from the index alone*
    is the whole claim.
    """
    start = min(start, len(text))
    end = min(start + length, len(text))
    index = FMIndex(text, SAMPLE)
    assert index.extract(start, end - start) == text[start:end]


@given(texts, st.integers(min_value=1, max_value=40))
@settings(deadline=None)
def test_the_sample_walk_agrees_with_the_suffix_array(text: bytes, sample: int) -> None:
    """Generated. Mirrors `sample_walk_agrees_with_the_suffix_array`.

    The samples, held to the walk that reads them. `FMIndex` builds one suffix array, inside
    `bwt.encode_with_sa`, and takes both sample arrays off it. This recovers **every** row's text
    position from the finished index -- its own markers, its own LF walk -- and that vector must
    *be* the suffix array of the text.

    No Lean cite -- **reason 3**: `SuffixArray.Valid` is the hypothesis both sides share rather than
    something either side proves, and what is compared here is two computations of the same array.
    """
    index = FMIndex(text, sample)
    walked = [index._position_of(row) for row in range(index.text_len())]
    assert walked == suffix_array(text)


@given(texts, patterns, st.integers(min_value=1, max_value=64))
@settings(deadline=None)
def test_every_sampling_rate_answers_the_same(text: bytes, pattern: bytes, sample: int) -> None:
    """Generated. Mirrors `every_sampling_rate_answers_the_same`.

    The rate is a space/time trade and nothing else: every rate must give the same answers. The two tests above run at the fixed 32, where a text shorter than one sampling
    interval exercises a single sample and no walk at all; these rates make the marker path real.

    Lean: `fmLocate_perm` for the `locate` assertion, as in `test_count_and_locate_match_naive`
    and under the same three hypotheses -- the sampling rate is not one of them, which is exactly
    the point. The `extract` assertion carries no cite -- **reason 2**.
    """
    index = FMIndex(text, sample)
    assert sorted(index.locate(pattern)) == naive.search(text, pattern)
    assert index.extract(0, len(text)) == text


@given(texts, patterns)
@settings(deadline=None)
def test_one_sample_only(text: bytes, pattern: bytes) -> None:
    """Generated. Mirrors `one_sample_only`.

    A rate past the text length leaves exactly one sample -- text position 0, which is a multiple
    of every rate -- so every `locate` walk runs its maximum and every `extract` starts from the
    wrap-around row. The bound is what the sampling rate buys, and this is the degenerate end of
    it.

    Lean: `fmLocate_perm` for the `locate` assertion, under all three hypotheses, exactly as in
    `test_count_and_locate_match_naive` -- the sampling rate is not one of them. The `extract`
    assertion in the same body carries no cite -- **reason 2**.
    """
    index = FMIndex(text, 4096)
    assert sorted(index.locate(pattern)) == naive.search(text, pattern)
    assert index.extract(0, len(text)) == text


# --- Deterministic: the worked example, and what answers nothing -----------------------------


def test_banana() -> None:
    """Deterministic. Mirrors `banana`: the textbook example, end to end, with the text deleted.

    Lean: `fmCount_eq` and `fmLocate_perm`, whose three hypotheses all hold here -- `banana\\0`
    is `Terminated`, the array comes from `suffix_array`, and no pattern carries a sentinel. The
    `extract` assertions carry no cite -- **reason 2**.
    """
    text = b"banana" + bytes([SENTINEL])
    index = FMIndex(text, 2)
    assert index.count(b"ana") == 2
    assert sorted(index.locate(b"ana")) == [1, 3]
    assert index.count(b"na") == 2
    assert index.count(b"banana") == 1
    assert index.extract(0, 6) == b"banana"
    assert index.extract(1, 3) == b"ana"
    assert index.extract(3, 3) == b"ana"
    assert index.extract(0, 7) == text


def test_locate_reports_in_suffix_order_not_text_order() -> None:
    """Deterministic. Why `fmLocate_perm` is a permutation and not an equality.

    The interval's rows are sorted by the *suffix* they name, so `ana$` (position 3) stands above
    `anana$` (position 1) and `locate` hands back `[3, 1]`. Nothing here sorts, and the theorem
    does not promise sorted output; every other test in this file that compares more than one
    position sorts first, and this one exists so that habit is visible as a consequence rather
    than a precaution.

    Lean: `fmLocate`, the **definition** -- `(sa.drop lo).take (hi - lo)`, the interval's rows in
    suffix-array order -- which on `banana$` is `[3, 1]` and `[5, 3, 1]`, the same lists this
    returns. The order is the Lean's own, not an accident of the example. It is `fmLocate_perm`,
    the theorem, that is weaker than both the definition and this code: it concludes a `Perm`,
    because a permutation is all a caller should rely on.
    """
    index = FMIndex(b"banana" + bytes([SENTINEL]), 2)
    assert index.locate(b"ana") == [3, 1]
    assert index.locate(b"a") == [5, 3, 1]


def test_a_pattern_absent_from_the_text() -> None:
    """Deterministic. Mirrors `a_pattern_absent_from_the_text` -- **two** different exits.

    `xyz` leaves `_interval` at the first character, because `x` is outside the text's alphabet
    and has no entry in `C`. `nab` gets three characters in and empties: every character is
    present, the string is not. Both answer nothing, and a test that took only the first exit
    would miss the narrowing loop's own guard entirely.

    Lean: `fmCount_eq` -- `matchCount t p` is `0` for both, and all three hypotheses hold.
    """
    text = b"banana" + bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    assert index.count(b"xyz") == 0
    assert index.locate(b"xyz") == []
    assert index.count(b"nab") == 0
    assert index.locate(b"nab") == []
    assert naive.search(text, b"nab") == []


def test_a_pattern_longer_than_the_text() -> None:
    """Deterministic. Mirrors `a_pattern_longer_than_the_text`.

    The one early return in `_interval` that **agrees** with the Lean rather than leaving or
    contradicting it: no suffix of `t` is long enough to begin with a pattern longer than `t`, so
    `matchCount t p` is `0` and `fmCount_eq` gives `0` too. It is therefore not a convention in
    this package's sense -- nothing was chosen -- and it is not an optimisation either. It is a
    **redundant guard kept for parity with the Rust**: a match longer than the text has to be
    cyclic, so it would carry the sentinel before its end, and `_interval`'s sentinel guard
    already refuses every such pattern.

    Lean: `fmCount_eq`, with all three hypotheses -- `ab\\0` is `Terminated`, the array comes from
    `suffix_array`, and the pattern carries no sentinel.
    """
    text = b"ab" + bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    assert index.count(b"abababab") == 0
    assert index.locate(b"abababab") == []
    assert naive.search(text, b"abababab") == []


def test_the_empty_pattern_occurs_everywhere() -> None:
    """Deterministic. Mirrors `the_empty_pattern_occurs_at_every_position`.

    Every shift of the `n` characters the sentinel ends is a match, `n + 1` of
    them, which are the `text_len()` rows backward search keeps when it reads no character. Pinned
    against the length, not against `naive.search` over the terminated bytes, which counts one
    shift more -- the one past the sentinel, which no row represents.

    Lean: `fmCount_eq`, which proves `fmCount t [] = t.length`, and `fmLocate_perm`, whose
    `fmLocate t sa []` is the whole suffix array. `s ∉ []` holds, so the empty pattern is inside
    all three hypotheses.
    """
    for text in (b"banana" + bytes([SENTINEL]), bytes([SENTINEL]), _long_text()):
        for sample in (1, 3, SAMPLE):
            index = FMIndex(text, sample)
            assert index.count(b"") == len(text)
            assert sorted(index.locate(b"")) == list(range(len(text)))


# --- Deterministic: the sentinel, in the pattern ---------------------------------------------


def test_a_pattern_holding_the_sentinel_occurs_nowhere() -> None:
    """Deterministic. Mirrors `a_pattern_holding_the_sentinel_occurs_nowhere`.

    Lean: `FMIndex.count_of_valid` and `FMIndex.locate_perm_of_valid`: the index answers about the
    text without its sentinel, `banana`, where `na$`, `$` and `a$b` occur nowhere, though the
    stored text ends with `na$`. `count` and `locate` refuse any pattern with a `SENTINEL` in it.
    """
    text = b"banana" + bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    for pattern in [b"na" + bytes([SENTINEL]), bytes([SENTINEL]), b"a" + bytes([SENTINEL]) + b"b"]:
        assert index.count(pattern) == 0
        assert index.locate(pattern) == []
        assert naive.search(b"banana", pattern) == []


def test_end_anchored_patterns_answer_nothing() -> None:
    """Deterministic, and a **count** behind the claim: 21 patterns, all inside
    `FMIndex.count_of_valid`.

    Every pattern of length 1 and 2 over `ALPHABET` with a `SENTINEL` appended, plus the lone
    sentinel -- `4 + 16 + 1 = 21` inputs, on the long fixture: each holds the sentinel, so each
    occurs nowhere in the text without it, though `naive.search` finds most of them in the stored
    text -- Lean: `FMIndex.count_of_valid` -- and each answers nothing.
    """
    text = _long_text()
    index = FMIndex(text, SAMPLE)
    probes = [
        pattern + bytes([SENTINEL]) for pattern in _short_patterns(2)
    ] + [bytes([SENTINEL])]
    assert len(probes) == 21
    assert any(naive.search(text, pattern) for pattern in probes)
    for pattern in probes:
        assert index.count(pattern) == 0, pattern
        assert index.locate(pattern) == [], pattern


def test_pinned_wraparound_match_without_the_guard() -> None:
    """Deterministic. Mirrors `pinned_wraparound_match_without_the_guard` -- the witness the
    generators cannot reach, in the style of `test_bwt`'s `pinned_disagreement_without_a_sentinel`.

    Lean: `FMIndex.count_of_valid`: a pattern holding the sentinel occurs nowhere in the text
    without it.

    Backward search matches **rotations**, and `"\\0a"` is a rotation of `"ab\\0"` without being a
    substring of it. Without the `SENTINEL in pattern[:-1]` guard in `_interval` the raw
    search narrows to the single row `[0, 1)` and reports one occurrence at position 2;
    `count` and `locate` refuse the pattern before they search, holding the sentinel as it does.
    `ALPHABET` excludes the sentinel, so no generated pattern can produce this input.

    The last assertions are the other half of the argument: backward search answers `b$`, a
    substring of the stored text, so its guard stops where it does; `count` refuses it, since the
    text without its sentinel does not hold it.
    """
    text = b"ab" + bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    wrapping = bytes([SENTINEL]) + b"a"
    assert naive.search(text, wrapping) == []
    assert index._interval(wrapping) is None
    assert index.count(wrapping) == 0
    assert index.locate(wrapping) == []
    assert index._interval(b"b" + bytes([SENTINEL])) == (2, 3)
    assert index.count(b"b" + bytes([SENTINEL])) == 0


def test_a_lone_sentinel_is_a_legal_text() -> None:
    """Deterministic. Mirrors `a_lone_sentinel_is_a_legal_text`.

    The shortest text `bwt.encode` accepts: one byte, one row, one sample. The text without its
    sentinel is empty, so the sentinel occurs nowhere and the empty pattern once (Lean:
    `FMIndex.count_of_valid`) -- and `extract` returns the sentinel, which is the degenerate case
    of "a range reaching the text's end is legal" (no cite, **reason 2**).
    """
    text = bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    assert index.text_len() == 1
    assert index.count(text) == 0
    assert index.locate(text) == []
    assert index.count(b"") == 1
    assert index.extract(0, 1) == text


# --- Deterministic: the bounds the sampling rates buy ----------------------------------------



def _lf_steps_to_a_sample(index: FMIndex, row: int) -> int:
    """How many LF steps `FMIndex._position_of` takes from `row` before it lands on a marked row:
    the walk it runs, counted.

    Capped at `n` steps, LF's whole cycle on a valid index: a walk that has met no mark by then
    never will, and the test fails there instead of hanging. The cap is not the claim under test
    -- `worst < sample` is -- so it sits where only a looping defect reaches it."""
    n = index.text_len()
    for steps in range(n + 1):
        if index._marks.access(row):
            return steps
        _, row = index._lf(row)
    pytest.fail(f"an LF walk met no marked row in {n + 1} steps: LF cycles through unmarked rows")


@pytest.mark.parametrize("build", [FMIndex, PlainFMIndex], ids=["FMIndex", "PlainFMIndex"])
def test_a_walk_that_meets_no_mark_raises_instead_of_looping(
    build: type[FMIndex] | type[PlainFMIndex],
) -> None:
    """`_position_of` stops after `min(sample, n)` LF steps, the bound a valid index never
    reaches, as the Rust's `position_of` panics there. A corrupted index -- here, no row marked
    -- makes LF cycle through unmarked rows; unbounded, `locate` would never return."""
    index = build(b"banana\x00", 3)
    index._marks = RRR([0] * 7) if isinstance(index, FMIndex) else BitIndex([0] * 7)
    with pytest.raises(RuntimeError, match="met no sampled row in 3 steps; the index is corrupt"):
        index.locate(b"a")
    index = build(b"banana\x00", 32)
    index._marks = RRR([0] * 7) if isinstance(index, FMIndex) else BitIndex([0] * 7)
    with pytest.raises(RuntimeError, match="met no sampled row in 7 steps"):
        index.locate(b"a")


def test_the_locate_walk_stays_inside_one_sampling_interval() -> None:
    """Deterministic, over **every** row of the long fixture at **five rates**: 198 rows each.

    The bound the module docstring states: at most `sample - 1` LF steps, because text
    position 0 is a multiple of every rate, so its row is always marked and the walk cannot pass
    it. The Rust spells this as a `debug_assert!` inside `position_of`; here the step count comes
    back from the walk and the check is a test, so a reader can see what was probed -- every row,
    not a sample of them -- and at which rate.

    The rate is varied too, because the bound is a claim about *every* rate and not about 32: at
    rate 1 every row is marked and no walk takes a step at all, and at a rate past the text length
    exactly one row is marked and some walk must run the full length.

    No Lean cite -- **reason 2**: `locateSampled_eq` bounds the walk (its fuel is `min(sample, n)`,
    and it answers within it), but for a model of the marks and values, not for this index.
    """
    text = _long_text()
    assert len(text) == 3 * SUPERBLOCK + 6
    for sample in (1, 2, 7, SAMPLE, 4096):
        index = FMIndex(text, sample)
        rows = index.text_len()
        assert rows == len(text)
        worst = max(_lf_steps_to_a_sample(index, row) for row in range(rows))
        assert worst < sample, (sample, worst)
        # And the bound is tight enough to be worth having: at a rate below the text length some
        # walk really does take steps, so this is not passing by walking nowhere.
        if sample > 1:
            assert worst > 0, sample


def test_the_build_takes_its_samples_from_the_suffix_array_without_walking() -> None:
    """The samples are read off the suffix array the BWT was computed through, in one pass: no
    LF step at build time. Rebuilding them by an `n`-step LF walk from the sentinel's row gives
    the same samples -- `test_the_sample_walk_agrees_with_the_suffix_array` cannot tell -- at
    `n` `occ` calls more.

    Counted at `ChunkedWavelet.occ` and `access_occ`, one of which an LF step cannot avoid however
    it is spelled: the build may ask only for `C`, one `occ` per symbol."""
    text = _long_text()
    calls = 0
    occ, access_occ = ChunkedWavelet.occ, ChunkedWavelet.access_occ

    def counted_occ(self: ChunkedWavelet, c: int, i: int) -> int:
        nonlocal calls
        calls += 1
        return occ(self, c, i)

    def counted_access(self: ChunkedWavelet, i: int) -> tuple[int, int]:
        nonlocal calls
        calls += 1
        return access_occ(self, i)

    with (
        mock.patch.object(ChunkedWavelet, "occ", counted_occ),
        mock.patch.object(ChunkedWavelet, "access_occ", counted_access),
    ):
        index = FMIndex(text, SAMPLE)
    assert calls == len(set(text))
    assert sorted(index.locate(text[:5])) == naive.search(text, text[:5])


def test_extract_discards_less_than_one_sampling_interval() -> None:
    """Deterministic, over **1230 ranges** of the long fixture at rate 32.

    `extract` starts from the nearest sampled text position **at or past** the end of the range
    and walks backwards, so the characters it emits past the range are what the final slice
    discards. That count is below `sample` for every range, including the wrap-around branch,
    where a range ending before the last sample would have found one.

    The lengths are not a sample of the possible ones, they are chosen around the rate: `0`, `1`,
    `2`, either side of `SAMPLE`, and two multiples of it. Every start is used. A range whose
    end lands exactly on a sample discards nothing and a range ending one past it discards the
    most, so the extremes of the bound are both in the sweep rather than left to luck.

    The Rust has this as a `debug_assert!` too. Here it is arithmetic on the sampled position,
    which the test recomputes from the rate rather than reading it out of the index -- and the
    extraction itself is checked against the text in the same loop, so a wrong sampled position
    cannot pass by accident.

    No Lean cite -- **reason 2**, for both halves: `extract` and sampling.
    """
    text = _long_text()
    index = FMIndex(text, SAMPLE)
    n = len(text)
    lengths = (0, 1, 2, SAMPLE - 1, SAMPLE, SAMPLE + 1, 2 * SAMPLE, n)
    checked = 0
    for start in range(n):
        for length in lengths:
            if start + length > n:
                continue
            assert index.extract(start, length) == text[start : start + length]
            if length > 0:
                end = start + length
                sample = -(-end // SAMPLE) * SAMPLE
                sampled_position = n if sample >= n else sample
                assert sampled_position - end < SAMPLE, (start, length)
            checked += 1
    assert checked == 1230


# --- Deterministic: the long fixture, the directory, and what is stored -----------------------


def test_every_short_pattern_agrees_with_naive() -> None:
    """Deterministic and exhaustive: **84 patterns** -- every one of length 1 to 3 over
    `ALPHABET` -- against `naive.search`, on the long fixture, at the default chunk length (one
    chunk) and at 13 (sixteen chunks, so every backward-search step and LF walk crosses chunk
    boundaries).

    The generated rows above supply variety; this sweep supplies repeatability: an exhaustive
    deterministic sweep either always catches a fault or never does.

    Lean: `fmCount_eq` and `fmLocate_perm`, with all three hypotheses -- the fixture is
    `Terminated`, its array comes from `suffix_array`, and `ALPHABET` excludes the sentinel.
    """
    text = _long_text()
    probes = _short_patterns(3)
    assert len(probes) == 84
    for chunk in (None, 13):
        index = FMIndex(text, SAMPLE, chunk)
        found = 0
        for pattern in probes:
            expected = naive.search(text, pattern)
            assert index.count(pattern) == len(expected), (chunk, pattern)
            assert sorted(index.locate(pattern)) == expected, (chunk, pattern)
            found += 1 if expected else 0
    # The sweep is only worth its runtime if it takes both roads through the narrowing loop, so
    # the split is pinned: 43 of the 84 occur (4 + 13 + 26, the fixture's distinct substrings at
    # those three lengths), and the other 41 empty the interval partway through. A fixture that
    # made either number zero would be testing one exit and no more.
        assert found == 43
    assert max(index.count(pattern) for pattern in probes) > 1


def test_the_last_column_is_what_is_stored() -> None:
    """Deterministic. The index holds the transform, not the text -- which is the claim.

    `FMIndex` stores the last column exactly once, compressed inside the `ChunkedWavelet` that
    counts over it, and reading every row back out of it gives `bwt.encode` exactly. The text is
    nowhere: the only way back to it is `extract`, which is the previous test's business.

    Lean: `bwt_eq_rotations` is what says that column is the transform, under `Terminated t s` and
    `SuffixArray.Valid ⟨t, sa⟩` -- the cite belongs to `bwt`, and is named here only to say which module
    this assertion leans on.
    """
    text = _long_text()
    index = FMIndex(text, SAMPLE)
    stored = bytes(index._occ.access_occ(row)[0] for row in range(index.text_len()))
    assert stored == bwt.encode(text)
    assert stored != text


# --- Deterministic: what raises -------------------------------------------------------------


def test_an_empty_range_extracts_nothing() -> None:
    """Deterministic. Mirrors `an_empty_range_extracts_nothing`, including at the very end, where
    there is no sample at or past the range and the wrap-around branch would be taken.

    No Lean cite -- **reason 2**.
    """
    text = b"banana" + bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    assert index.extract(0, 0) == b""
    assert index.extract(3, 0) == b""
    assert index.extract(7, 0) == b""


def test_extracting_past_the_end_raises() -> None:
    """Deterministic. Mirrors `extracting_past_the_end_panics`, as a `ValueError`.

    The range is input arriving from outside the program, which is the line this package draws
    (`lcp`'s demand on `sa`, `bwt.decode`'s on the sentinel count). It is deliberately *not* the
    saturating answer `occ` and `rank` give, because a truncated extraction is a wrong answer
    rather than a saturated count.

    No Lean cite -- **reason 2**.
    """
    text = b"banana" + bytes([SENTINEL])
    index = FMIndex(text, SAMPLE)
    with pytest.raises(ValueError, match="runs past the text's 7 bytes"):
        index.extract(5, 5)


def test_a_negative_position_raises() -> None:
    """Deterministic. No Rust mirror -- `u32` has no negatives to reject.

    Python's would index from the right and quietly answer a different question, and Lean's
    positions are `Nat`, so there is no saturating answer to mirror either. `count_index` raises
    on a negative `rank` position for the same two reasons.

    No Lean cite -- **reason 2**.
    """
    index = FMIndex(b"banana" + bytes([SENTINEL]), SAMPLE)
    with pytest.raises(ValueError, match="start -1 is negative"):
        index.extract(-1, 2)
    # Neither endpoint of 2..1 is negative; the length is, and the message says so.
    with pytest.raises(ValueError, match="length -1 is negative"):
        index.extract(2, -1)


def test_the_rate_defaults_to_sample() -> None:
    """Deterministic. Mirrors `new_samples_at_the_default_rate`.

    `FMIndex(text)` keeps the samples `FMIndex(text, SAMPLE)` keeps, not those of a nearby rate,
    and the two-argument form still works.

    No Lean cite -- **reason 2**: a sampling rate has no Lean counterpart.
    """
    assert SAMPLE == 32
    text = b"mississippi banana " * 20 + bytes([SENTINEL])
    default, explicit = FMIndex(text), FMIndex(text, SAMPLE)
    assert default._sample == SAMPLE
    assert default._sa_samples == explicit._sa_samples
    assert default._isa_samples == explicit._isa_samples
    assert len(default._sa_samples) != len(FMIndex(text, 16)._sa_samples)
    assert FMIndex(b"banana\x00", 2).count(b"ana") == 2
    assert FMIndex(b"banana\x00").count(b"ana") == 2


def test_a_zero_sampling_rate_is_rejected() -> None:
    """Deterministic. Mirrors `a_zero_sampling_rate_is_rejected`, as a `ValueError`.

    A rate of zero makes `position % rate` undefined and the whole sampling argument empty.

    No Lean cite -- **reason 2**: a sampling rate has no Lean counterpart.
    """
    text = b"a" + bytes([SENTINEL])
    with pytest.raises(ValueError, match="sampling rate must be positive"):
        FMIndex(text, 0)


def test_an_unterminated_text_is_rejected() -> None:
    """Deterministic. Mirrors `unterminated_text_is_rejected`.

    The rejection is `bwt.encode`'s, not this module's, and that is the point worth seeing: the
    constructor's first statement is what establishes `Terminated t s`, the hypothesis every
    theorem in `FMIndex/Search.lean` takes. All three of `bwt.encode`'s rejections are the hypothesis,
    so all three are checked here.

    No Lean cite -- **reason 1**: these inputs are exactly the ones outside `Terminated t s`.
    """
    with pytest.raises(ValueError, match="must end with SENTINEL"):
        FMIndex(b"banana", SAMPLE)
    with pytest.raises(ValueError, match="cannot end with SENTINEL"):
        FMIndex(b"", SAMPLE)
    with pytest.raises(ValueError, match="before the text's end"):
        FMIndex(b"ba" + bytes([SENTINEL]) + b"na" + bytes([SENTINEL]), SAMPLE)


def test_the_property_tests_reach_past_the_first_superblock_over_the_whole_alphabet() -> None:
    """What `test_count_and_locate_match_naive` is handed when it runs, asserted rather than
    trusted: `_texts`' docstring table is the measurement that found `st.lists` drawing a median
    of 4 to 6 bytes and never a text past `SUPERBLOCK`. Over 100 fixed runs of the test itself,
    the median text must be over 100 bytes, a third must pass one superblock, and half must use
    three or more of the four symbols -- a text of the right length over one symbol would give
    backward search one interval to find."""
    texts_built = inputs_reaching(
        test_count_and_locate_match_naive, FMIndex, "__init__",
        lambda self, text, *rest: bytes(text),
    )
    lengths = sorted(len(text) for text in texts_built)
    assert len(lengths) >= 50
    assert lengths[len(lengths) // 2] > 100, lengths[len(lengths) // 2]
    assert sum(n > SUPERBLOCK for n in lengths) >= len(lengths) // 3
    varied = sum(len(set(text) - {SENTINEL}) >= 3 for text in texts_built)
    assert varied >= len(texts_built) // 2, varied


# -- `is_valid`: the stored pieces agree with each other and with the column ---------------------
# These tests check `FMIndex.Valid` (`FMIndex/Spec.lean`) on built and corrupted indexes. A test
# that builds from a terminated text cites `FMIndex.valid_build`, which covers all six pieces.
# They mirror the Rust's `unit_tests/fm_index.rs` one for one, and run every case on both `FMIndex`
# and `PlainFMIndex`, which must agree. A corrupted index is assembled by writing the private
# fields directly, in `assembly.py`.

BOTH = [FMIndex, PlainFMIndex]


def _all_but(i: int, n: int = 7) -> list[bool]:
    """`n` `True`s with the `i`-th `False`: six for the pieces, three for invariant 2's parts."""
    want = [True] * n
    want[i] = False
    return want


BANANA = b"banana" + bytes([SENTINEL])


@pytest.mark.parametrize("cls", BOTH)
def test_banana_is_valid_at_every_rate(cls: type[Index]) -> None:
    """Lean: `FMIndex.valid_build`, all six pieces."""
    for k in range(1, 9):
        assert cls(BANANA, k).check_valid() is None, k


@given(texts, st.integers(min_value=1, max_value=20))
@settings(deadline=None)
def test_the_build_is_valid(text: bytes, sample: int) -> None:
    """Mirrors `build_is_valid`, on both indexes. Lean: `FMIndex.valid_build`; `texts` appends the
    sentinel to a body that excludes it."""
    assert FMIndex(text, sample).check_valid() is None
    assert PlainFMIndex(text, sample).check_valid() is None


@pytest.mark.parametrize("cls", BOTH)
def test_the_pieces_reassemble_into_a_valid_index(cls: type[Index]) -> None:
    idx = _assemble(cls, *_pieces(BANANA, 2), 2)
    assert idx.is_valid()
    assert sorted(idx.locate(b"ana")) == [1, 3]


@pytest.mark.parametrize("cls", BOTH)
def test_a_zero_rate_breaks_rate_at_least_one_and_the_kept_positions(cls: type[Index]) -> None:
    """Mirrors `a_zero_rate_breaks_rate_at_least_one_and_the_kept_positions`. At rate `n` only
    position 0 is kept; at rate 0 none may be (the Lean's `(n + 0 - 1) / 0` is `0`), yet position
    0's row must be marked (`p % 0 = p`): with the sentinel in the column, rate 0 always breaks
    invariant 2 as well, so `check_valid` names that first. No row is listed at rate 0."""
    last, c, marks, sa, _ = _pieces(BANANA, 7)
    idx = _assemble(cls, last, c, marks, sa, [], 0)
    want = _all_but(0)
    want[6] = False
    assert _conjuncts(idx) == want
    assert _kept_parts(idx) == _all_but(0, 3)
    assert idx.check_valid() == "invariant 2 (positions_kept)"


@pytest.mark.parametrize("cls", BOTH)
def test_a_mark_past_the_rows_breaks_is_positions_kept_alone(cls: type[Index]) -> None:
    """One mark more than rows: no row's mark changes, no rank the samples read moves."""
    last, c, marks, sa, isa = _pieces(BANANA, 2)
    marks.append(0)
    idx = _assemble(cls, last, c, marks, sa, isa, 2)
    assert _conjuncts(idx) == _all_but(0)
    assert _kept_parts(idx) == _all_but(1, 3)
    assert idx.check_valid() == "invariant 2 (positions_kept)"


@pytest.mark.parametrize("cls", BOTH)
def test_positions_swapped_with_their_listed_rows_break_is_positions_kept_alone(
    cls: type[Index],
) -> None:
    """Swap the rows of positions 2 and 4, and the stored positions at those rows to match: the
    marks, the samples and the listed rows agree with each other, but not with the walk."""
    last, c, marks, sa, isa = _pieces(BANANA, 2)
    r1, r2 = sum(marks[: isa[1]]), sum(marks[: isa[2]])
    sa[r1], sa[r2] = sa[r2], sa[r1]
    isa[1], isa[2] = isa[2], isa[1]
    idx = _assemble(cls, last, c, marks, sa, isa, 2)
    assert _conjuncts(idx) == _all_but(0)
    assert _kept_parts(idx) == _all_but(2, 3)
    assert idx.check_valid() == "invariant 2 (positions_kept)"


@pytest.mark.parametrize("cls", BOTH)
def test_a_wrong_c_breaks_is_smaller_letters_counted_alone(cls: type[Index]) -> None:
    last, c, marks, sa, isa = _pieces(BANANA, 2)
    c[ord("a")] += 1
    idx = _assemble(cls, last, c, marks, sa, isa, 2)
    assert _conjuncts(idx) == _all_but(2)
    assert idx.check_valid() == "not in the box (smaller_letters_counted)"


@pytest.mark.parametrize("cls", BOTH)
def test_a_column_with_two_sentinels_breaks_is_sentinel_once_alone(cls: type[Index]) -> None:
    """`ba$$` is the transform of the cyclic text `a$b$`, whose rotations are all distinct: one LF
    cycle, two sentinels. Rotation order is positions 3, 1, 0, 2; at rate 1 all are kept, and the
    walk from the first sentinel's row (2), position 0's, meets every row in turn."""
    idx = _assemble(
        cls, bytes([ord("b"), ord("a"), SENTINEL, SENTINEL]),
        {SENTINEL: 0, ord("a"): 2, ord("b"): 3}, [1, 1, 1, 1], [3, 1, 0, 2], [2, 1, 3, 0], 1,
    )
    assert _conjuncts(idx) == _all_but(1)


@pytest.mark.parametrize("cls", BOTH)
def test_a_column_of_two_cycles_breaks_the_walk_with_the_kept_positions(cls: type[Index]) -> None:
    """`a$a`: LF is 0 -> 1 -> 0 and 2 -> 2. The walk from the sentinel's row comes back to it after
    two steps, where position 1 is expected, so `is_positions_kept` fails, through its last part,
    with `is_walk_visits_every_row`, which with one sentinel never fails alone."""
    idx = _assemble(
        cls, bytes([ord("a"), SENTINEL, ord("a")]), {SENTINEL: 0, ord("a"): 1},
        [0, 1, 0], [0], [1], 3,
    )
    assert _conjuncts(idx) == [False, True, True, False, True, True, True]
    assert _kept_parts(idx) == _all_but(2, 3)


@pytest.mark.parametrize("cls", BOTH)
def test_listed_rows_swapped_break_is_kept_rows_listed_alone(cls: type[Index]) -> None:
    """The rows of positions 2 and 4 listed the wrong way round; the samples are untouched."""
    last, c, marks, sa, isa = _pieces(BANANA, 2)
    isa[1], isa[2] = isa[2], isa[1]
    idx = _assemble(cls, last, c, marks, sa, isa, 2)
    assert _conjuncts(idx) == _all_but(4)
    assert idx.check_valid() == "not in the box (kept_rows_listed)"


@pytest.mark.parametrize("cls", BOTH)
def test_samples_in_the_wrong_order_break_the_walk_and_the_listed_rows(cls: type[Index]) -> None:
    """A reordering of the grid is still the grid, so invariant 2's first part (the Lean's `Perm`)
    passes; its last part and the listed rows both see which row each position belongs to."""
    last, c, marks, sa, isa = _pieces(BANANA, 2)
    sa[0], sa[1] = sa[1], sa[0]
    idx = _assemble(cls, last, c, marks, sa, isa, 2)
    assert _conjuncts(idx) == [False, True, True, True, False, True, True]
    assert _kept_parts(idx) == _all_but(2, 3)


@pytest.mark.parametrize("cls", BOTH)
def test_a_rotated_sample_frame_breaks_is_positions_kept_alone(cls: type[Index]) -> None:
    """`ab$` at rate 1 with every position moved on by one, mod 3, and the listed rows recomputed
    to match: the samples now describe the rotation `b$a`. Every other piece holds; the walk from
    the sentinel's row sees the shift, and `locate` would answer in the wrong frame."""
    text = b"ab" + bytes([SENTINEL])
    last, c, marks, sa, _ = _pieces(text, 1)
    sa = [(p + 1) % 3 for p in sa]
    isa = [0] * 3
    for row, p in enumerate(sa):
        isa[p] = row
    rotated = _assemble(cls, last, c, marks, sa, isa, 1)
    assert _conjuncts(rotated) == _all_but(0)
    assert _kept_parts(rotated) == _all_but(2, 3)
    assert rotated.locate(b"b") != FMIndex(text, 1).locate(b"b")  # what the frame is for


@pytest.mark.parametrize("cls", BOTH)
def test_is_valid_does_not_raise_on_out_of_range_pieces(cls: type[Index]) -> None:
    """Mirrors `is_valid_does_not_panic_on_out_of_range_pieces`, plus the negative entries a
    Python list would read from the end: positions and rows past `n`, a short `C`, short marks,
    a zero rate, and stored values with no column at all."""
    last, c, marks, _, _ = _pieces(BANANA, 2)
    bad = [
        _assemble(cls, last, c, marks, [0, 100, 2, 4], [0, 9, 99, 4], 2),
        _assemble(cls, last, {SENTINEL: 0}, marks[:3], [1000], [1000], 2),
        _assemble(cls, last, c, marks, [0, 2, 4, 6], [3, 4, 5, 6], 0),
        _assemble(cls, b"", {}, [], [5], [5], 1),
        _assemble(cls, last, c, marks, [0, -2, 2, 4], [-1, -7, -3, -2], 2),
        _assemble(cls, last, c, marks, [0, 2, 4, 6], [0, 1, 2, 3], -2),
    ]
    for idx in bad:
        _conjuncts(idx)
        _kept_parts(idx)
        assert not idx.is_valid()


@pytest.mark.parametrize("cls", BOTH)
def test_the_empty_column_fails_only_on_its_sentinel(cls: type[Index]) -> None:
    assert _conjuncts(_assemble(cls, b"", {}, [], [], [], 1)) == _all_but(1)
