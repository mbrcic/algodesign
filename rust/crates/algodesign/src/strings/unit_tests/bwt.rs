// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::naive;
use proptest::prelude::*;

proptest! {
    #[test]
    fn round_trips(mut text in prop::collection::vec(1u8..5, 1..300)) {
        text.push(SENTINEL);
        prop_assert_eq!(decode(&encode(&text)), text);                // Lean: invertBwt_bwt
    }

    #[test]
    fn agrees_with_the_rotation_matrix(mut text in prop::collection::vec(1u8..5, 1..60)) {
        text.push(SENTINEL);
        prop_assert_eq!(encode(&text), naive::bwt_rotations(&text));  // Lean: bwt_eq_rotations
    }

    #[test]
    fn is_a_permutation_not_a_compressor(mut text in prop::collection::vec(1u8..5, 1..200)) {
        text.push(SENTINEL);
        prop_assert_eq!(encode(&text).len(), text.len());       // Lean: length_bwtOfSorted
    }
}

#[test]
fn banana() {
    let mut text = b"banana".to_vec();
    text.push(SENTINEL);
    assert_eq!(encode(&text), naive::bwt_rotations(&text));
    assert_eq!(decode(&encode(&text)), text);
}

#[test]
fn pinned_disagreement_without_a_sentinel() {
    // Without a sentinel the rotation matrix and the suffix-array formula disagree.
    let text = b"abaa";
    let rotations = naive::bwt_rotations(text);
    assert_eq!(rotations, b"baaa");

    let sa = suffix_array(text);
    let n = text.len();
    let via_suffix_array: Vec<u8> = sa.iter().map(|&i| text[(i as usize + n - 1) % n]).collect();
    assert_eq!(via_suffix_array, b"abaa");

    assert_ne!(rotations, via_suffix_array);

    // So encode refuses unterminated text.
    assert_eq!(try_encode(text), Err(EncodeError::MissingSentinel));
}

#[test]
fn empty_text_is_rejected() {
    assert_eq!(try_encode(b""), Err(EncodeError::Empty));
}

#[test]
#[should_panic(expected = "text is empty")]
fn encode_panics_on_empty_text() {
    let _ = encode(b"");
}

#[test]
fn lone_sentinel_round_trips() {
    let text = [SENTINEL];
    assert_eq!(encode(&text), vec![SENTINEL]);
    assert_eq!(decode(&encode(&text)), text.to_vec());
}

#[test]
fn empty_last_column_decodes_to_empty_text() {
    assert_eq!(decode(&[]), Vec::<u8>::new());
}

#[test]
fn missing_sentinel_is_rejected() {
    assert_eq!(try_encode(b"banana"), Err(EncodeError::MissingSentinel));
}

#[test]
fn sentinel_before_the_end_is_rejected() {
    let text = [b'b', SENTINEL, b'a', SENTINEL];
    assert_eq!(try_encode(&text), Err(EncodeError::SentinelBeforeEnd(1)));
}

#[test]
#[should_panic(expected = "exactly one SENTINEL byte, found 0")]
fn decode_panics_without_a_sentinel() {
    let _ = decode(b"banana");
}

#[test]
#[should_panic(expected = "exactly one SENTINEL byte, found 2")]
fn decode_panics_with_two_sentinels() {
    let _ = decode(&[b'b', SENTINEL, b'a', SENTINEL]);
}

/// The same refusal through `decode` itself, on a last column one byte past `u32::MAX`
/// (lazily zeroed memory, never read).
#[test]
#[cfg(target_pointer_width = "64")]
#[should_panic(expected = "counts and rows are u32 and hold at most u32::MAX")]
fn decode_refuses_a_last_column_past_u32_max() {
    let _ = decode(&vec![0u8; u32::MAX as usize + 1]);
}

/// And `try_encode`'s, on a terminated text one byte past `u32::MAX`: an error, not a panic.
#[test]
#[cfg(target_pointer_width = "64")]
fn try_encode_refuses_a_text_past_u32_max() {
    let len = u32::MAX as usize + 2;
    assert_eq!(
        try_encode(&vec![0u8; len]),
        Err(EncodeError::TooLong { len })
    );
}

/// `try_decode_at_most` refuses a last column past its bound before any counting.
#[test]
fn decode_refuses_a_last_column_longer_than_its_counts_hold() {
    let last = encode(b"bana\0");
    assert_eq!(try_decode_at_most(&last, 5), Ok(b"bana\0".to_vec()));
    assert_eq!(
        try_decode_at_most(&last, 3),
        Err(DecodeError::TooLong { len: 5 })
    );
}

/// `try_decode` names what is wrong with a column instead of panicking.
#[test]
fn try_decode_reports_the_sentinel_count() {
    assert_eq!(try_decode(b"banana"), Err(DecodeError::SentinelCount(0)));
    assert_eq!(
        try_decode(&[b'b', SENTINEL, b'a', SENTINEL]),
        Err(DecodeError::SentinelCount(2))
    );
    assert_eq!(try_decode(&[]), Ok(Vec::new()));
}

// `is_valid` and its three pieces: the Lean `BWT.Valid`, judged on any text and any column. The
// promise, the text back from the letters, is the round trip above (Lean `BWT.Contract.promise`).

/// `banana$`'s transform meets all three; `annb$aa` is the chapter's column.
#[test]
fn the_transform_of_banana_is_valid() {
    let last = encode(b"banana\0");
    assert_eq!(last, b"annb\0aa");
    assert!(is_same_letters(b"banana\0", &last));
    assert!(is_letter_before_each_suffix(b"banana\0", &last));
    assert!(is_sentinel_once(&last));
    assert_eq!(check_valid(b"banana\0", &last), Ok(()));
}

/// Each piece broken on its own where the others hold, or the first failing one named.
#[test]
fn each_piece_fails_where_it_should() {
    // Two letters swapped: still a permutation, no longer the transform.
    assert_eq!(
        check_valid(b"banana\0", b"nanb\0aa"),
        Err("invariant 2 (letter_before_each_suffix)")
    );
    // A letter changed: not even a permutation.
    assert_eq!(
        check_valid(b"banana\0", b"annb\0ab"),
        Err("invariant 1 (same_letters)")
    );
    // `abaa` has no sentinel: the first two pieces hold, the assumption does not.
    let sa = crate::strings::suffix_array::suffix_array(b"abaa");
    let n = 4;
    let column: Vec<u8> = sa
        .iter()
        .map(|&p| b"abaa"[(p as usize + n - 1) % n])
        .collect();
    assert!(is_letter_before_each_suffix(b"abaa", &column));
    assert_eq!(
        check_valid(b"abaa", &column),
        Err("assumption (sentinel_once)")
    );
    // A second sentinel in the text: both pieces hold on its own column, the assumption does not.
    let text = b"a\0a\0";
    let column = encode_unchecked(text);
    assert!(is_same_letters(text, &column) && is_letter_before_each_suffix(text, &column));
    assert_eq!(
        check_valid(text, &column),
        Err("assumption (sentinel_once)")
    );
    // The empty text and column: no sentinel.
    assert_eq!(check_valid(b"", b""), Err("assumption (sentinel_once)"));
}

proptest! {
    /// Lean: `valid_bwtOfSa`, on every terminated text.
    #[test]
    fn encode_is_valid(body in prop::collection::vec(1u8..4, 0..60)) {
        let mut text = body;
        text.push(SENTINEL);
        let last = encode(&text);
        prop_assert_eq!(check_valid(&text, &last), Ok(()));
    }
}

/// The column `bwtOfSa` reads off any text, sentinel or not.
fn encode_unchecked(text: &[u8]) -> Vec<u8> {
    let n = text.len();
    crate::strings::suffix_array::suffix_array(text)
        .iter()
        .map(|&p| text[(p as usize + n - 1) % n])
        .collect()
}
