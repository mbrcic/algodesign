# SPDX-License-Identifier: Apache-2.0
"""Records and the corpus, checked the way `rust/crates/algodesign/src/strings/records.rs` checks them.

Two of the three property tests here -- `test_record_bounds_contain_every_position` and
`test_positions_inside_one_record_name_one_quote` -- are the two theorems of
`lean/AlgoDesign/Strings/Records/Quote.lean` restated against this implementation. They are proved there
about the definitional `rank` and `select`. `RankSelect/Directory.lean`'s `rankTwoLevel_eq` proves a
model of this directory computes that `rank` (at any block width, this module's 8/64 included);
`select`'s directory is not modelled, and neither is this code, so these tests hold it. The third,
`test_find_agrees_with_a_scan_of_the_records`, mirrors the Rust's proptest of the same shape and
answers to no theorem.

The fixed cases mirror the Rust's, with one addition.

The **addition** is `test_a_corpus_of_many_records_crosses_the_index_boundaries`. Every corpus in
the Rust's fixed cases is a few dozen bytes, and a structure whose behaviour changes with size is
invisible to a corpus that never reaches the size. That test is what *guarantees* a start
bitvector spanning several superblocks; `layouts()` only sometimes produces one, and says so.
"""

import sys

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings._constants import SENTINEL, SEPARATOR
from algodesign.strings.count_index import SUPERBLOCK
from algodesign.strings.fm_index import SAMPLE, FMIndex
from algodesign.strings.records import Corpus, Records

from .assembly import assemble_fm as _assemble
from .assembly import assemble_records as _records
from .reach import inputs_reaching

QUOTES = [
    b"to be or not to be that is the question",
    b"all the world is a stage",
    b"i have always depended on the kindness of strangers",
]


@st.composite
def layouts(draw: st.DrawFn) -> tuple[list[int], int]:
    """Record starts and a text length, with a record at position 0 as `hstart` requires.

    Wider than the Rust's generator, which tops out at eleven records of at most eleven bytes: up
    to 40 records here, so a draw *can* reach 480 bytes and cross several superblocks. It usually
    does not -- Hypothesis draws small collections far more often than large ones -- so this
    generator is variety, and `test_a_corpus_of_many_records_crosses_the_index_boundaries` is the
    guarantee. Both tests below loop over **every** position
    of whatever layout they are handed, so a long draw exercises the directory exhaustively.
    """
    lengths = draw(st.lists(st.integers(min_value=1, max_value=12), min_size=1, max_size=40))
    starts: list[int] = []
    at = 0
    for length in lengths:
        starts.append(at)
        at += length
    return starts, at


@given(layouts())
def test_record_bounds_contain_every_position(layout: tuple[list[int], int]) -> None:
    """Lean: `recordBounds_contains`. Both of its hypotheses are supplied rather than assumed --
    `hstart` by the generator putting a record at position 0, `hi` by the loop staying below
    `text_len`."""
    starts, text_len = layout
    records = Records(starts, text_len)
    for pos in range(text_len):
        low, high = records.bounds(records.record_of(pos))
        assert low <= pos < high


@given(layouts())
def test_positions_inside_one_record_name_one_quote(layout: tuple[list[int], int]) -> None:
    """Lean: `recordOf_eq_of_no_start_between`.

    Its hypothesis is the content of its name -- `∀ k, i < k → k ≤ j → b[k]! = false`, no record
    start strictly between the two positions -- and the loop below supplies it by construction:
    `low` is a record start and `pos` ranges over `[low, high)`, which holds no other start. The
    theorem is **not** unconditional, and the condition is exactly what `Corpus`'s layout and its
    two guards exist to guarantee. That is why two hits in one quote deduplicate to one, and why
    a fragment that could straddle a boundary would be outside the theorem's reach -- which is
    the case guard 2 removes.
    """
    starts, text_len = layout
    records = Records(starts, text_len)
    for record_id in range(len(records)):
        low, high = records.bounds(record_id)
        for pos in range(low, high):
            assert records.record_of(pos) == record_id


# Every example builds an `FMIndex`, as `test_fm_index.py`'s property tests do, and those run
# without a deadline for the same reason: a pure-Python suffix array is slow on a slow runner.
@settings(deadline=None)
@given(
    st.lists(
        st.lists(st.integers(min_value=2, max_value=4), min_size=1, max_size=12).map(bytes),
        min_size=1,
        max_size=6,
    ),
    st.lists(st.integers(min_value=2, max_value=4), min_size=1, max_size=3).map(bytes),
)
def test_find_agrees_with_a_scan_of_the_records(records: list[bytes], fragment: bytes) -> None:
    """The whole of `find`, against a scan of the records it was built from: the quotes containing
    the fragment, once each, in corpus order."""
    corpus = Corpus(records)
    expected = [
        record_id
        for record_id, record in enumerate(records)
        if any(
            record[at : at + len(fragment)] == fragment
            for at in range(len(record) - len(fragment) + 1)
        )
    ]
    found = corpus.find(fragment)
    assert [quote.record_id for quote in found] == expected
    for quote in found:
        assert quote.text == records[quote.record_id]


def test_any_remembered_fragment_returns_the_whole_quote() -> None:
    corpus = Corpus(QUOTES)
    for fragment in (b"to be or", b"not to be that", b"is the question"):
        hits = corpus.find(fragment)
        assert len(hits) == 1
        assert hits[0].text == QUOTES[0]  # beginning, middle and end all return it whole
    assert len(corpus.find(b"kindness")) == 1
    # One quote per hit, however many occurrences inside it. All three quotes hold "the".
    assert len(corpus.find(b"the")) == 3


def test_start_middle_and_end_name_the_same_record_interval() -> None:
    """The cost claim, concretely: whichever part of the quote was remembered, the same record
    number and the same interval come back, so the same extraction runs. The hit positions differ
    and stop mattering after `record_of`."""
    corpus = Corpus(QUOTES)
    answers = [
        corpus.find(fragment)[0]
        for fragment in (b"to be or", b"not to be that", b"is the question")
    ]
    assert all(answer == answers[0] for answer in answers)
    assert answers[0].record_id == 0
    assert answers[0].bounds == (0, len(QUOTES[0]) + 1)
    assert answers[0].text == QUOTES[0]


def test_two_occurrences_in_one_quote_are_one_hit() -> None:
    """"to be or not to be": two occurrences, one quote. `recordOf_eq_of_no_start_between` cashed
    in -- no record start lies between the two hits, so they name one number and `find` shows one
    quote."""
    corpus = Corpus(QUOTES)
    assert corpus.count(b"to be") == 2
    hits = corpus.find(b"to be")
    assert len(hits) == 1
    assert hits[0].text == QUOTES[0]


def test_a_fragment_spanning_two_records_finds_nothing() -> None:
    corpus = Corpus(QUOTES)
    # The end of quote 0 and the start of quote 1 are adjacent in the concatenation, one separator
    # apart. Neither the joined text nor the text with the separator spelt out can be found: the
    # first is not in the concatenation at all, the second is and is refused.
    assert corpus.find(b"questionall") == []
    assert corpus.count(b"questionall") == 0
    straddle = b"question" + bytes([SEPARATOR]) + b"all"
    assert corpus.find(straddle) == []
    assert corpus.count(straddle) == 0
    # The whole corpus really is one text: 39 + 24 + 51 bytes of quotes, two separators and the
    # terminating sentinel.
    assert corpus.records().text_len() == 39 + 24 + 51 + 3


def test_pinned_straddling_match_without_the_guard() -> None:
    """The witness that guard 2 is load-bearing, in the shape `test_fm_index.py`'s
    `test_pinned_wraparound_match_without_the_guard` gives it: the straddle **is** in the
    concatenation, and an `FMIndex` asked directly finds it. Only `Corpus`'s refusal of a fragment
    carrying a reserved byte keeps `find` from answering with quote 0, which does not contain the
    fragment at all."""
    text = bytes([SEPARATOR]).join(QUOTES) + bytes([SENTINEL])
    straddle = b"question" + bytes([SEPARATOR]) + b"all"
    assert FMIndex(text, SAMPLE).count(straddle) == 1
    corpus = Corpus(QUOTES)
    assert corpus.count(straddle) == 0
    assert corpus.find(straddle) == []


def test_a_fragment_carrying_a_reserved_byte_finds_nothing() -> None:
    corpus = Corpus(QUOTES)
    assert corpus.find(b"strangers" + bytes([SENTINEL])) == []
    assert corpus.find(bytes([SENTINEL])) == []
    assert corpus.find(bytes([SEPARATOR])) == []


def test_a_fragment_in_no_quote_finds_nothing() -> None:
    corpus = Corpus(QUOTES)
    assert corpus.find(b"parting is such sweet sorrow") == []
    assert corpus.find(b"zebra") == []
    assert corpus.count(b"zebra") == 0


def test_an_empty_fragment_is_in_every_quote() -> None:
    """CLRS: the empty fragment occurs at every shift of every record, `len(r) + 1` of them, so
    `find` answers every quote and `count` the concatenation's length. An empty record
    contains it too."""
    corpus = Corpus(QUOTES)
    assert [quote.record_id for quote in corpus.find(b"")] == list(range(len(QUOTES)))
    total = sum(len(quote) + 1 for quote in QUOTES)
    assert corpus.count(b"") == total == corpus.records().text_len()
    with_empty = Corpus([b"first", b"", b"third"])
    assert [quote.text for quote in with_empty.find(b"")] == [b"first", b"", b"third"]


def test_the_corpus_keeps_no_text() -> None:
    """"Delete the original file", pinned on the structure: a `Corpus` holds its index and its
    record starts and nothing else, so every quote `find` and `quote` return was decoded out of the
    index. A field holding the concatenation beside the index would pass every other test here."""
    assert Corpus.__slots__ == ("_index", "_records")
    corpus = Corpus(QUOTES)
    assert isinstance(corpus._index, FMIndex)
    assert [corpus.quote(i).text for i in range(len(corpus))] == QUOTES


def test_an_empty_corpus_finds_nothing() -> None:
    corpus = Corpus([])
    assert len(corpus) == 0
    # The concatenation is the terminating sentinel alone.
    assert corpus.records().text_len() == 1
    assert corpus.find(b"anything") == []
    assert corpus.count(b"anything") == 0
    # No record, so no shift of one: the empty fragment is in nothing here.
    assert corpus.find(b"") == []
    assert corpus.count(b"") == 0


def test_a_single_record_corpus_is_bounded_by_the_text_end() -> None:
    """The last record has no next start, so `select` answers `None` and the text's end stands in
    -- the Lean's `getD b.length`."""
    corpus = Corpus([b"alone"])
    assert corpus.records().bounds(0) == (0, 6)
    assert corpus.find(b"lon")[0].text == b"alone"
    assert corpus.quote(0).text == b"alone"


def test_an_empty_record_is_a_record() -> None:
    """Two dividers in a row. The empty record still starts somewhere, so it still has a number
    and bounds; only the empty fragment is ever found inside it."""
    corpus = Corpus([b"first", b"", b"third"])
    assert len(corpus) == 3
    assert corpus.records().bounds(1) == (6, 7)
    assert corpus.quote(1).text == b""
    assert corpus.find(b"third")[0].record_id == 2


def test_a_corpus_of_many_records_crosses_the_index_boundaries() -> None:
    """A start bitvector spanning several superblocks, so `record_of` and `bounds` really do
    consult the two-level directory rather than its fallback scan. On short texts every query
    lands in block 0 of superblock 0, where a fault in the directory is invisible.
    """
    records = [bytes([2 + (i % 3)]) * (2 + i % 5) for i in range(4 * SUPERBLOCK)]
    corpus = Corpus(records)
    assert corpus.records().text_len() > 4 * SUPERBLOCK
    assert len(corpus) == 4 * SUPERBLOCK
    for record_id in range(len(corpus)):
        low, high = corpus.records().bounds(record_id)
        assert corpus.records().record_of(low) == record_id
        assert corpus.records().record_of(high - 1) == record_id
        assert corpus.quote(record_id).text == records[record_id]


def test_a_record_carrying_a_reserved_byte_is_rejected() -> None:
    """A `ValueError` a caller can catch, naming the first offending record, the position in it
    and the byte, as the Rust's `Corpus::try_build` returns them in `BuildError::ReservedByte`."""
    with pytest.raises(ValueError, match="record 1 carries the reserved byte 1 at position 1;"):
        Corpus([b"fine", bytes([ord("n"), SEPARATOR, ord("o")])])
    with pytest.raises(ValueError, match="record 0 carries the reserved byte 0 at position 1;"):
        Corpus([bytes([ord("n"), SENTINEL])])
    with pytest.raises(ValueError, match="record 1 carries the reserved byte 0 at position 1;"):
        Corpus([b"ok", bytes([ord("a"), SENTINEL, SEPARATOR]), bytes([SEPARATOR])])


def test_a_vector_whose_first_record_starts_late_is_rejected() -> None:
    """`AlgoDesignTests/Strings.lean` pins the same counterexample against the Lean: with
    `b = [false, false, true]` positions 0 and 1 lie in no record, and `recordOf`'s truncating
    subtraction hands them record 0, whose start is *after* them. That is `hstart`."""
    with pytest.raises(ValueError, match="must start at position 0"):
        Records([2], 3)


def test_starts_must_be_strictly_increasing_and_inside_the_text() -> None:
    with pytest.raises(ValueError, match="strictly increasing"):
        Records([0, 3, 3], 5)
    with pytest.raises(ValueError, match="strictly increasing"):
        Records([0, 4, 2], 5)
    with pytest.raises(ValueError, match="not inside"):
        Records([0, 5], 5)


def test_a_record_number_that_is_not_a_record_is_refused() -> None:
    records = Records([0, 4], 8)
    # The message names the record asked for and the range of records there are, so a caller
    # can see which side of the range the number fell off.
    with pytest.raises(ValueError, match=r"no record 2; the records are numbered 0 to 1$"):
        records.bounds(2)
    with pytest.raises(ValueError, match=r"no record -1; the records are numbered 0 to 1$"):
        records.bounds(-1)
    with pytest.raises(ValueError, match="negative"):
        records.record_of(-1)


def test_a_corpus_with_no_records_has_no_quote_to_name() -> None:
    """The one case `hstart` leaves open: an empty `Records` has no start at or before any
    position. Lean's `recordOf` answers `0` there by truncating `Nat` subtraction, and that
    truncation is the defect `hstart` fences rather than a default worth mirroring."""
    with pytest.raises(ValueError, match="holds no records"):
        Records([], 4).record_of(0)


def test_a_position_past_the_text_names_the_last_record() -> None:
    """`rank` saturates, so `record_of` answers with the last record. `recordBounds_contains`'s
    upper half does not apply there -- that is its `hi` hypothesis -- and this pins what happens
    instead rather than leaving it to be discovered."""
    records = Records([0, 4], 8)
    assert records.record_of(99) == 1
    low, high = records.bounds(records.record_of(99))
    assert low <= 99
    assert not 99 < high


def test_every_property_test_that_builds_an_index_runs_without_a_deadline() -> None:
    """A configuration pin, and only that. Building a `Corpus` or an `FMIndex` runs a pure-Python
    suffix array, whose time on a slow runner is not what these properties are about, and under
    Hypothesis' default deadline it can fail intermittently. Every `@given` test in this file and in `test_fm_index.py` that
    builds either -- found by running it, on a few fixed inputs, with `FMIndex.__init__` watched,
    since a `Corpus` builds one too -- must carry `deadline=None`. A timing failure cannot be made
    deterministic; what can be checked is that the setting that removes it is still there."""
    from . import test_fm_index

    builders = 0
    for module in (sys.modules[__name__], test_fm_index):
        for name, test in list(vars(module).items()):
            if not (name.startswith("test_") and getattr(test, "is_hypothesis_test", False)):
                continue
            built = inputs_reaching(test, FMIndex, "__init__", lambda *args: 1, runs=5)
            if built:
                assert test._hypothesis_internal_use_settings.deadline is None, name
                builders += 1
    assert builders >= 5, builders


# -- `is_valid`: the starts begin at 0, the count is right, and the records and the index describe
# one layout. Mirrors the Rust's `unit_tests/records.rs` one for one. A corrupted corpus is made by
# writing the private fields directly: `Records` refuses a first start other than 0, and `Corpus`
# a reserved byte, so neither constructor could build one.


record_lists = st.lists(
    st.lists(st.integers(min_value=2, max_value=4), max_size=11).map(bytes), max_size=5
)
"""Up to five records of up to eleven bytes, none reserved: the Rust's `build_is_valid` ranges."""


@given(record_lists)
@settings(deadline=None)
def test_the_build_is_valid(records: list[bytes]) -> None:
    """Any record list the constructor accepts, empty records and the empty list included."""
    corpus = Corpus(records)
    assert corpus.records().is_valid()
    assert corpus.is_valid()
    assert corpus.check_valid() is None


def test_built_corpora_are_valid() -> None:
    """The empty corpus is the `[0]` case: `FirstRecordAtStart` holds because nothing starts."""
    empty = Corpus([])
    assert empty.records().is_valid() and empty.is_valid()
    assert Corpus([b"ab", b"", b"c"]).is_valid()


def _three() -> Corpus:
    """`ab`, the empty record and `c`: `ab|` `|` `c$`, with starts 0, 3 and 4."""
    return Corpus([b"ab", b"", b"c"])


def _bits(corpus: Corpus) -> list[int]:
    """The start bits of a corpus."""
    starts = corpus.records()._starts
    return [starts.rank(i + 1) - starts.rank(i) for i in range(len(starts))]


def _conjuncts(corpus: Corpus) -> list[bool]:
    """The index's `is_valid`, the records' two checks, and the corpus's two."""
    return [
        corpus._index.is_valid(),
        corpus._records.starts_at_zero(),
        corpus._records.count_matches(),
        corpus.lengths_agree(),
        corpus.reserved_bytes_placed(),
    ]


def test_clearing_the_first_start_breaks_starts_at_zero_alone() -> None:
    """Every start `s > 0` still has its separator at `s - 1`, so only the records object
    notices."""
    corpus = _three()
    bits = _bits(corpus)
    bits[0] = 0
    corpus._records = _records(bits, 2)
    assert _conjuncts(corpus) == [True, False, True, True, True]
    assert not corpus.records().is_valid() and not corpus.is_valid()
    assert corpus.check_valid() == "not in the box (starts_at_zero)"


def test_a_wrong_count_breaks_count_matches_alone() -> None:
    corpus = _three()
    corpus._records._count += 1
    assert _conjuncts(corpus) == [True, True, False, True, True]
    assert not corpus.records().is_valid() and not corpus.is_valid()
    assert corpus.records().check_valid() == "layout (count_matches)"


def test_records_over_a_longer_text_break_lengths_agree_alone() -> None:
    corpus = _three()
    bits = _bits(corpus)
    bits.append(0)
    corpus._records = _records(bits, 3)
    assert _conjuncts(corpus) == [True, True, True, False, True]
    assert not corpus.is_valid()
    assert corpus.check_valid() == "layout (lengths_agree)"


def test_a_start_shifted_by_one_breaks_reserved_bytes_placed_alone() -> None:
    corpus = _three()
    bits = _bits(corpus)
    bits[3], bits[2] = 0, 1
    corpus._records = _records(bits, 3)
    assert _conjuncts(corpus) == [True, True, True, True, False]
    assert not corpus.is_valid()
    assert corpus.check_valid() == "not in the box (reserved_bytes_placed)"


def test_a_reserved_byte_inside_a_record_breaks_reserved_bytes_placed() -> None:
    """The text the constructor refuses, `a`, `SEPARATOR`, `b` as one record, indexed directly:
    an extra separator."""
    corpus = Corpus.__new__(Corpus)
    corpus._index = FMIndex(bytes([ord("a"), SEPARATOR, ord("b"), SENTINEL]), SAMPLE)
    corpus._records = Records([0], 4)
    assert _conjuncts(corpus) == [True, True, True, True, False]


def test_reserved_bytes_placed_answers_on_a_corrupted_index() -> None:
    """No mark at all: a `locate` walk would never stop, so the check must not search."""
    corpus = _three()
    bad = _assemble(FMIndex, bytes([ord("c"), SENTINEL, SEPARATOR]),
                    {SENTINEL: 0, SEPARATOR: 1, ord("c"): 2}, [0, 0, 0], [], [], 1)
    assert isinstance(bad, FMIndex)
    corpus._index = bad
    assert not corpus._index.is_valid()
    assert not corpus.reserved_bytes_placed()
    assert not corpus.is_valid()
