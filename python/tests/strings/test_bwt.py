# SPDX-License-Identifier: Apache-2.0
"""The transform, checked the way `rust/crates/algodesign/src/strings/bwt.rs` checks it.

The three property tests mirror that module's proptests and the fixed cases mirror the ones it
pins. `walk_from` lives here rather than in `bwt.py` for the reason `test_lcp`'s `lcp_naive`
lives here: it is the other side of one differential -- the walk started at the wrong row -- and
not a function the chapter ships.
"""

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.strings import naive
from algodesign.strings._constants import SENTINEL
from algodesign.strings.bwt import (
    check_valid,
    decode,
    encode,
    is_letter_before_each_suffix,
    is_same_letters,
    is_sentinel_once,
)
from algodesign.strings.suffix_array import suffix_array

# Alphabet `{1, 2, 3, 4}`, the Rust proptest's `1u8..5`: every byte above the sentinel, so the
# terminator appended below is the only one in the text. A small alphabet makes rows collide,
# which is what exercises the rank-among-equals half of the LF-mapping.
SYMBOLS = st.integers(min_value=1, max_value=4)


def terminated(max_size: int) -> st.SearchStrategy[bytes]:
    """Non-empty texts of `SYMBOLS`, each with one `SENTINEL` appended -- the Rust's
    `prop::collection::vec(1u8..5, 1..n)` followed by its `text.push(SENTINEL)`."""
    return st.lists(SYMBOLS, min_size=1, max_size=max_size).map(
        lambda symbols: bytes(symbols) + bytes([SENTINEL])
    )


def walk_from(last: bytes, start: int) -> bytes:
    """The LF walk of `bwt.decode`, but from a row the caller names.

    Only here to make the start rule visible: run from the sentinel's row it agrees with
    `decode`, and run from row 0 it returns the text rotated by one.
    """
    counts = [0] * 256
    for byte in last:
        counts[byte] += 1
    block_start = [0] * 256
    running = 0
    for byte, count in enumerate(counts):
        block_start[byte] = running
        running += count

    seen = [0] * 256
    lf = [0] * len(last)
    for row, byte in enumerate(last):
        lf[row] = block_start[byte] + seen[byte]
        seen[byte] += 1

    row = start
    backwards = bytearray()
    for _ in range(len(last)):
        backwards.append(last[row])
        row = lf[row]
    backwards.reverse()
    return bytes(backwards)


@given(terminated(300))
def test_round_trips(text: bytes) -> None:
    """Mirrors `round_trips`.

    Lean: `invertBwt_bwt` -- for a text satisfying `Terminated`, which the appended sentinel
    supplies, the walk over the last column returns the text it started from.
    """
    assert decode(encode(text)) == text


@given(terminated(40))
def test_the_lf_walk_inverts_as_prepend_and_sort_does(text: bytes) -> None:
    """The chapter inverts its worked example by prepending the last column and sorting, `n` times
    over; `decode` walks LF instead. `naive.bwt_inverse` is the chapter's procedure, and the two
    give the same text on every last column a terminated text produces."""
    column = encode(text)
    assert decode(column) == naive.bwt_inverse(column) == text


@given(terminated(60))
def test_agrees_with_the_rotation_matrix(text: bytes) -> None:
    """Mirrors `agrees_with_the_rotation_matrix`.

    Lean: `bwt_eq_rotations` -- under `Terminated t s`, reading the last column off the suffix
    array gives the same string as sorting the rotation matrix. `naive.bwt_rotations` is that
    matrix, built and sorted; `encode` never builds one.
    """
    assert encode(text) == naive.bwt_rotations(text)


@given(terminated(200))
def test_is_a_permutation_not_a_compressor(text: bytes) -> None:
    """Mirrors `is_a_permutation_not_a_compressor`, and pins the stronger claim the Rust leaves
    to its length check.

    Lean: `length_bwtOfSorted` for the length, `bwtOfSorted_perm` for the bytes themselves. The
    output is the input's own bytes in another order; nothing is added and nothing is dropped.
    """
    out = encode(text)
    assert len(out) == len(text)
    assert sorted(out) == sorted(text)


def test_the_three_rejections_are_the_lean_hypothesis_only_because_the_sentinel_is_zero() -> None:
    """`Terminated t s` asks that the last byte be strictly smaller than every other one.

    At `s = 0` over bytes, "strictly smaller than every other" and "no other zero" are the same
    condition, which is why `encode`'s three rejections check the hypothesis rather than merely
    resembling it. That equivalence is contingent on this one constant: give `SENTINEL` any other
    value and a text could pass all three checks while carrying a smaller byte, so the rejections
    would stop being `Terminated`. Pinned here so moving the constant fails loudly.
    """
    assert SENTINEL == 0


def test_prepend_and_sort_on_the_chapters_banana() -> None:
    """The chapter's worked inversion, as the oracle runs it: `annb$aa` back to `banana$`."""
    assert naive.bwt_inverse(encode(b"banana\x00")) == b"banana\x00"


def test_banana() -> None:
    """The chapter's worked example. Rotation order is `$banana, a$banan, ana$ban, anana$b,
    banana$, na$bana, nana$ba`, and its last column is `annb$aa`."""
    text = b"banana" + bytes([SENTINEL])
    assert encode(text) == b"annb" + bytes([SENTINEL]) + b"aa"
    assert encode(text) == naive.bwt_rotations(text)
    assert decode(encode(text)) == text


def test_the_walk_starts_at_the_sentinel_row_and_not_at_row_zero() -> None:
    """The start rule, as the difference it makes.

    Row 0 is the row of the sentinel *suffix*: its rotation begins at the sentinel, so a walk
    from there spells `$banana`. The row wanted is the one whose last column holds the sentinel
    -- row 4 for `banana$` -- because that is the row whose rotation begins at position 0.
    """
    text = b"banana" + bytes([SENTINEL])
    last = encode(text)
    assert last.index(SENTINEL) == 4
    assert walk_from(last, 0) == bytes([SENTINEL]) + b"banana"
    assert walk_from(last, last.index(SENTINEL)) == text
    assert decode(last) == text


def test_pinned_disagreement_without_a_sentinel() -> None:
    """Mirrors `pinned_disagreement_without_a_sentinel`: the hypothesis `bwt_eq_rotations`
    carries, as a witness.

    Without a terminator the two routes answer different questions. The sorted rotation matrix
    orders whole rows cyclically; the suffix-array formula orders by suffix, where a proper
    prefix comes before its extension. `encode` refuses the text outright rather than quietly
    returning the second answer -- delete that check, and this is the line that fails.
    """
    text = b"abaa"
    assert naive.bwt_rotations(text) == b"baaa"

    sa = suffix_array(text)
    assert sa == [3, 2, 0, 1]
    n = len(text)
    via_suffix_array = bytes(text[(start + n - 1) % n] for start in sa)
    assert via_suffix_array == b"abaa"
    assert via_suffix_array != naive.bwt_rotations(text)

    with pytest.raises(ValueError, match="must end with SENTINEL"):
        encode(text)


def test_lone_sentinel_round_trips() -> None:
    """The one-row matrix, which the property tests' non-empty symbol list cannot reach: the
    text is nothing but its terminator, and the transform of it is itself."""
    text = bytes([SENTINEL])
    assert encode(text) == bytes([SENTINEL])
    assert decode(encode(text)) == text


def test_empty_text_is_rejected() -> None:
    """An empty text has no last byte to be the sentinel."""
    with pytest.raises(ValueError, match="text is empty"):
        encode(b"")


def test_missing_sentinel_is_rejected() -> None:
    """`Terminated` asks for a terminator, and `banana` has none."""
    with pytest.raises(ValueError, match="must end with SENTINEL"):
        encode(b"banana")


def test_sentinel_before_the_end_is_rejected() -> None:
    """Terminated asks for the sentinel to be *strictly* below every byte before it, so a second
    occurrence breaks the hypothesis even though the text still ends with one. The message names
    the offending position, matching the Rust's `SentinelBeforeEnd(1)`."""
    text = bytes([ord("b"), SENTINEL, ord("a"), SENTINEL])
    with pytest.raises(ValueError, match="appeared at position 1"):
        encode(text)


def test_empty_last_column_decodes_to_an_empty_text() -> None:
    """No rows, no walk."""
    assert decode(b"") == b""


def test_decode_rejects_a_column_with_no_sentinel() -> None:
    """`banana` is the transform of no text: with no sentinel there is no row to start from."""
    with pytest.raises(ValueError, match="exactly one SENTINEL byte, found 0"):
        decode(b"banana")


def test_decode_rejects_a_column_with_two_sentinels() -> None:
    """Two sentinels leave two candidate start rows, and the walk would pick one and return a
    wrong text. Rejecting is what keeps the wrong text from being returned quietly."""
    with pytest.raises(ValueError, match="exactly one SENTINEL byte, found 2"):
        decode(bytes([ord("b"), SENTINEL, ord("a"), SENTINEL]))


def test_the_chapters_banana_dollar_runs() -> None:
    """The chapter writes the sentinel as `$`; the library's sentinel is byte 0, so `b"banana$"`
    is refused -- its `$` is an ordinary byte and the sentinel is missing. `parse` writes the
    chapter's text as the library's bytes and `show` reads the answer back the chapter's way."""
    from algodesign.strings import parse, show

    with pytest.raises(ValueError):
        encode(b"banana$")
    assert parse("banana$") == b"banana\x00"
    assert show(encode(parse("banana$"))) == "annb$aa"
    assert show(decode(encode(parse("banana$")))) == "banana$"
    assert show(parse("to|be$")) == "to|be$" and parse("to|be$") == b"to\x01be\x00"


# --- is_valid: the Lean `BWT.Valid`, judged on any text and any column ---------------------------


def test_the_transform_of_banana_is_valid() -> None:
    """Mirrors `the_transform_of_banana_is_valid`: `annb$aa` is the chapter's column."""
    text = b"banana" + bytes([SENTINEL])
    last = encode(text)
    assert is_same_letters(text, last)
    assert is_letter_before_each_suffix(text, last)
    assert is_sentinel_once(last)
    assert check_valid(text, last) is None


def test_each_piece_fails_where_it_should() -> None:
    """Mirrors `each_piece_fails_where_it_should`."""
    text = b"banana" + bytes([SENTINEL])
    assert check_valid(text, b"nanb\x00aa") == "invariant 2 (letter_before_each_suffix)"
    assert check_valid(text, b"annb\x00ab") == "invariant 1 (same_letters)"
    sa = suffix_array(b"abaa")
    column = bytes(b"abaa"[(p + 3) % 4] for p in sa)
    assert is_letter_before_each_suffix(b"abaa", column)
    assert check_valid(b"abaa", column) == "assumption (sentinel_once)"
    two = b"a\x00a\x00"
    column = bytes(two[(p + 3) % 4] for p in suffix_array(two))
    assert is_same_letters(two, column) and is_letter_before_each_suffix(two, column)
    assert check_valid(two, column) == "assumption (sentinel_once)"
    assert check_valid(b"", b"") == "assumption (sentinel_once)"


@given(st.binary(max_size=60).map(lambda b: bytes(c % 3 + 1 for c in b)))
def test_encode_is_valid(body: bytes) -> None:
    """Mirrors `encode_is_valid`. Lean: `valid_bwtOfSa`."""
    text = body + bytes([SENTINEL])
    last = encode(text)
    assert check_valid(text, last) is None
