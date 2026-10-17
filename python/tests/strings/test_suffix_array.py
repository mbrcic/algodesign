# SPDX-License-Identifier: Apache-2.0
"""Prefix doubling, checked the way `rust/crates/algodesign/src/strings/suffix_array.rs` checks it.

The property test mirrors that module's `matches_the_naive_sort`, and the fixed cases below
mirror the ones it pins, so that the Python rendering and the Rust production layer are held to
the same statements rather than to two independently chosen ones.

`search` mirrors the Rust's `search`: the stretch of `sa` holding the matches, in suffix order.
Its property test sorts that stretch and compares it with `naive.search`, as the Rust's
`search_finds_every_occurrence` does.
"""

import importlib
import math
import random
from unittest import mock

from hypothesis import given
from hypothesis import strategies as st
from sorting_probe import sorts_during

from algodesign.strings import naive
from algodesign.strings.suffix_array import (
    _counting_sort_by,
    _dense_tags,
    check_valid,
    is_each_position_once,
    is_suffixes_sorted,
    is_valid,
    search,
    suffix_array,
)

from .cost_probes import CountingBytes
from .reach import inputs_reaching

# The module itself, for the probe that counts its counting sorts.
sa_module = importlib.import_module("algodesign.strings.suffix_array")

# Alphabet `{0, 1, 2, 3, 4}`, the Rust proptest's `0u8..5`. Small enough that ties survive
# several doubling rounds -- on a wide alphabet round 0 would separate almost everything and the
# loop under test would barely run -- and it includes byte `0`, which is what would notice the
# reserved tag value being confused with a real byte.
SYMBOLS = st.integers(min_value=0, max_value=4)
# Two strategies rather than one: `st.lists(max_size=300)` alone biases short -- measured over
# 400 examples the median length was 5 and only 4 draws reached three doubling rounds, where the
# Rust's `0..300` is uniform. The second strategy keeps the long texts the round count lives in.
texts = st.one_of(
    st.lists(SYMBOLS, max_size=300).map(bytes),
    st.lists(SYMBOLS, min_size=60, max_size=300).map(bytes),
)


@given(texts)
def test_matches_the_naive_sort(text: bytes) -> None:
    """Prefix doubling returns what sorting the suffixes as whole slices returns.

    Mirrors `matches_the_naive_sort`. Lean: `valid_suffixArray`, and `suffixArrayEarly_eq`
    for the early exit on distinct tags.
    """
    assert suffix_array(text) == naive.suffix_array(text)


@given(texts)
def test_suffix_array_passes_is_valid(text: bytes) -> None:
    """Mirrors `suffix_array_passes_is_valid`: the doubling's answer passes the check any
    caller can run. Lean: `SuffixArray.Valid`, which `valid_suffixArray` proves of the Lean's
    own loop, not of this one."""
    assert is_valid(text, suffix_array(text))
    assert check_valid(text, suffix_array(text)) is None


# `is_valid` and its two pieces on "abaa", mirroring the Rust's four fixed cases: each
# half fails alone once, and an entry past the end fails both without raising.


def test_the_suffix_array_of_abaa_is_one() -> None:
    sa = [3, 2, 0, 1]
    assert is_each_position_once(b"abaa", sa)
    assert is_suffixes_sorted(b"abaa", sa)
    assert is_valid(b"abaa", sa)


def test_rotation_order_fails_on_order_alone() -> None:
    """"abaa" ahead of "aa": the order of the rotations, which the no-sentinel array is not."""
    sa = [2, 3, 0, 1]
    assert is_each_position_once(b"abaa", sa)
    assert not is_suffixes_sorted(b"abaa", sa)
    assert not is_valid(b"abaa", sa)
    assert check_valid(b"abaa", sa) == "invariant 2 (suffixes_sorted)"


def test_a_repeated_position_fails_on_permutation_alone() -> None:
    sa = [3, 3, 0, 1]
    assert not is_each_position_once(b"abaa", sa)
    assert is_suffixes_sorted(b"abaa", sa)
    assert not is_valid(b"abaa", sa)
    assert check_valid(b"abaa", sa) == "invariant 1 (each_position_once)"


def test_a_position_past_the_end_fails_both_and_does_not_raise() -> None:
    """Position 9 names the empty suffix, as the Lean's `drop` does, and it sorts below "baa"."""
    sa = [3, 2, 0, 1, 9]
    assert not is_each_position_once(b"abaa", sa)
    assert not is_suffixes_sorted(b"abaa", sa)
    assert not is_valid(b"abaa", sa)


def test_a_negative_position_is_not_a_position() -> None:
    """A Python list reads index `-3` from the end, here as position 1, which is missing; the
    check must not."""
    assert not is_each_position_once(b"abaa", [3, 2, 0, -3])


def test_banana() -> None:
    assert suffix_array(b"banana") == [5, 3, 1, 0, 4, 2]


# --- search ----------------------------------------------------------------------------------

# Alphabet `{0, 1, 2, 3}` and patterns of 1 to 5 bytes, the Rust proptest's `0u8..4` and `1..6`:
# short patterns over few symbols occur often, and longer ones often only partly.
SEARCH_SYMBOLS = st.integers(min_value=0, max_value=3)


@given(
    st.lists(SEARCH_SYMBOLS, min_size=1, max_size=200).map(bytes),
    st.lists(SEARCH_SYMBOLS, min_size=0, max_size=5).map(bytes),
)
def test_search_finds_every_occurrence(text: bytes, pattern: bytes) -> None:
    """Mirrors `search_finds_every_occurrence`: the stretch, sorted, is exactly the positions
    `naive.search` reports. And for a non-empty pattern it is a stretch -- a contiguous slice of
    `sa`; the empty pattern's answer carries `n` too, which `sa` has no entry for."""
    sa = suffix_array(text)
    found = search(text, sa, pattern)
    assert sorted(found) == naive.search(text, pattern)
    if found and pattern:
        start = sa.index(found[0])
        assert sa[start : start + len(found)] == found


def test_search_returns_a_contiguous_run_in_suffix_order() -> None:
    sa = suffix_array(b"banana")
    assert search(b"banana", sa, b"ana") == [3, 1]  # suffix order, not text order
    assert search(b"banana", sa, b"banana") == [0]
    assert search(b"banana", sa, b"bananas") == []
    assert search(b"banana", sa, b"x") == []


def test_search_edge_cases() -> None:
    """The empty pattern, which occurs at every shift `0..n` as `naive.search` says, the empty
    suffix `n` first; the empty text; a pattern longer than the text; and a match that is only the
    text's short last suffix, which sorts first."""
    sa = suffix_array(b"banana")
    assert search(b"banana", sa, b"") == [6, 5, 3, 1, 0, 4, 2]
    assert sorted(search(b"banana", sa, b"")) == naive.search(b"banana", b"")
    assert search(b"", [], b"") == [0]
    assert search(b"", [], b"a") == []
    assert search(b"a", [0], b"a") == [0]
    assert search(b"ab", suffix_array(b"ab"), b"abc") == []
    assert search(b"abcab", suffix_array(b"abcab"), b"b") == [4, 1]
    assert search(b"abcab", suffix_array(b"abcab"), b"cab") == [2]


def test_empty_and_single_byte_texts() -> None:
    """The property test's length range starts at 0, so these are inside it -- but an off-by-one
    in the loop's termination shows up here first, and a named test says where to look."""
    assert suffix_array(b"") == []
    assert suffix_array(b"a") == [0]
    assert suffix_array(bytes([0])) == [0]


def test_a_proper_prefix_sorts_before_its_extension() -> None:
    """The array sorts the text as given, with no terminator appended. The suffixes of "abaa"
    are "abaa", "baa", "aa", "a"; with no terminator "a" < "aa" < "abaa". Appending one would
    reorder these."""
    assert suffix_array(b"abaa") == [3, 2, 0, 1]
    assert suffix_array(b"abaa") == naive.suffix_array(b"abaa")


def test_distinct_bytes_need_no_doubling_round() -> None:
    """Round 0 hands out n distinct tags, so `top == n` and the loop is never entered.
    Correctness here is what says the early exit does not skip necessary work.

    Lean: `suffixArrayEarly_eq` -- the early-exit loop returns `suffixArray`'s array, and
    `AlgoDesignTests/Strings.lean` pins that it takes zero rounds on these two texts.
    """
    assert suffix_array(b"abcdef") == [0, 1, 2, 3, 4, 5]
    assert suffix_array(b"fedcba") == [5, 4, 3, 2, 1, 0]


def test_all_equal_bytes_force_every_round() -> None:
    """The worst case for the early exit: nothing separates until the window covers the text, so
    the loop runs to the other exit -- the one `valid_of_doubling` licenses. On a
    text of one repeated byte the suffixes sort shortest first, by the no-sentinel rule."""
    text = bytes([7]) * 64
    assert suffix_array(text) == naive.suffix_array(text)
    assert suffix_array(text) == list(reversed(range(64)))


def test_counting_sort_is_stable() -> None:
    """Each round's counting sort discards the second-component order unless equal keys keep
    their input order, and an unstable sort fails this silently: the suffix array still comes out
    *sorted*, just wrong.
    Sorting the positions 0, 1, 2, 3 by the key 0, 1, 0, 1 must leave the two 0s and the two 1s
    in the order they arrived -- 0, 2, 1, 3 -- not 2, 0, 3, 1."""
    assert _counting_sort_by([0, 1, 2, 3], [0, 1, 0, 1], 2) == [0, 2, 1, 3]


def test_equal_keys_take_equal_tags_and_tags_start_at_one() -> None:
    """`Doubling.Valid` is an iff: two positions whose keys agree must carry the *same* tag, not
    merely adjacent ones. `0` is left free for "the suffix ends here", so the lowest tag is 1."""
    tag, top = _dense_tags([0, 2, 3, 1], b"abaa")
    assert tag == [1, 2, 1, 1]
    assert top == 2


# --- The procedure, not only the answer ------------------------------------------------------
#
# `sorted(range(n), key=lambda i: text[i:])` gives every answer above right. It is a different
# algorithm, comparing whole suffixes, and the book prints prefix doubling. These two tests tell
# them apart by what the procedure costs.

_rng = random.Random(5)
COST_TEXTS = [
    bytes(_rng.choice(b"ab") for _ in range(n)) for n in (1, 2, 5, 50, 400)
] + [b"a" * 300, b"ab" * 150, bytes(range(256))]


def test_only_round_0_reads_the_text() -> None:
    """Round 0 reads each byte a bounded number of times -- twice in the counting sort, at most
    twice more while tagging -- and every later round works on tags alone: two numbers stand in
    for `2^(k+1)` characters. So the whole construction reads at most `4n` characters, where a
    comparison sort of the suffixes reads about `n^2 / 2` on `b"a" * n`."""
    for text in COST_TEXTS:
        counted = CountingBytes(text)
        assert suffix_array(counted) == naive.suffix_array(text)
        assert counted.reads <= 4 * len(text), (len(text), counted.reads)


def test_each_round_is_one_counting_sort_and_there_are_at_most_log_n_rounds() -> None:
    """Round 0 is one counting sort by byte, and each doubling round one more by the first
    component (the second is read off `sa`). The window doubles from 1 until it covers the text,
    so there are at most `ceil(log2 n)` doubling rounds, and on `b"a" * n` exactly that many."""
    for text in COST_TEXTS:
        with mock.patch.object(
            sa_module, "_counting_sort_by", wraps=sa_module._counting_sort_by
        ) as counting_sort:
            suffix_array(text)
        rounds = math.ceil(math.log2(len(text)))
        assert 1 <= counting_sort.call_count <= rounds + 1, (len(text), counting_sort.call_count)
        if text == b"a" * len(text):
            assert counting_sort.call_count == rounds + 1


def test_no_round_calls_a_comparison_sort() -> None:
    """Neither component of a round's pair is ordered by a comparison sort: the second is read off
    `sa`, the first takes one counting sort. A `sorted()` for either -- the whole pair, or only the
    second component, which leaves the counting-sort count above unchanged -- gives the same array
    at `O(n log n)` comparisons a round, and so does a heap or a run of `insort`s. Every call of
    `sorted`, a list's `sort`, `heapq` or `bisect.insort`, however it is reached, is recorded
    while each array is built, and there must be none."""
    for text in COST_TEXTS:
        with sorts_during() as sorts:
            built = suffix_array(text)
        assert sorts == [], (len(text), sorts[:3])
        assert built == naive.suffix_array(text)


def test_the_property_test_needs_three_doubling_rounds_on_varied_texts() -> None:
    """What `test_matches_the_naive_sort` is handed when it runs, asserted rather than trusted.
    `st.lists(max_size=300)` alone had a median of 5 bytes and put 4 draws in 400 through a third
    doubling round, so the round loop was barely tested. Over 100 fixed runs of the test itself, a
    third of the texts must need three rounds, and half must use three or more symbols -- a long
    run of one byte needs every round and tests nothing else."""
    texts_seen = inputs_reaching(
        test_matches_the_naive_sort, naive, "suffix_array", lambda text: bytes(text)
    )
    assert len(texts_seen) >= 50
    three = 0
    for text in texts_seen:
        with mock.patch.object(
            sa_module, "_counting_sort_by", wraps=sa_module._counting_sort_by
        ) as counting_sort:
            suffix_array(text)
        three += counting_sort.call_count - 1 >= 3
    assert three >= len(texts_seen) // 3, three
    assert sum(len(set(text)) >= 3 for text in texts_seen) >= len(texts_seen) // 2
