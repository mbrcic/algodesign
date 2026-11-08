// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::fm_index::FmIndex;
use crate::strings::suffix_array::suffix_array;
use proptest::prelude::*;

/// `banana$`: `ana` is rows 2 and 3 (`ana$`, `anana$`), after `a` (rows 1 to 3) and `na`.
#[test]
fn banana_after_every_symbol() {
    let text = b"banana\0";
    let sa = suffix_array(text);
    let idx = FmIndex::build(text, 2);
    let pat = b"ana";
    for (j, step) in idx.interval_steps(pat).into_iter().enumerate() {
        let (lo, hi) = step.expect("every symbol of `ana` is in the text");
        let read = &pat[pat.len() - j - 1..];
        assert_eq!(check_valid(text, &sa, read, lo, hi), Ok(()), "{read:?}");
    }
}

/// Each piece broken where the others hold.
#[test]
fn each_piece_fails_where_it_should() {
    let text = b"banana\0";
    let sa = suffix_array(text);
    // One row too many: the stretch holds a suffix not starting with `ana`, and is too wide.
    assert_eq!(
        check_valid(text, &sa, b"ana", 2, 5),
        Err("invariant 1 (stretch_holds_matches)")
    );
    // `x` occurs nowhere and sorts after every suffix: its empty stretch belongs at row 7.
    assert_eq!(check_valid(text, &sa, b"x", 7, 7), Ok(()));
    assert_eq!(
        check_valid(text, &sa, b"x", 6, 6),
        Err("not in the box (stretch_starts_right)")
    );
    assert_eq!(
        check_valid(text, &sa, b"x", 7, 6),
        Err("not in the box (stretch_as_wide_as_matches)")
    );
}

proptest! {
    /// Lean: `BackwardSearch.valid_backwardSearch`, at every step of every pattern the index
    /// reads to the end.
    #[test]
    fn every_step_is_valid(
        body in prop::collection::vec(1u8..4, 0..40),
        pat in prop::collection::vec(1u8..4, 1..5),
    ) {
        let mut text = body;
        text.push(0);
        let sa = suffix_array(&text);
        let idx = FmIndex::build(&text, 3);
        for (j, step) in idx.interval_steps(&pat).into_iter().enumerate() {
            if let Some((lo, hi)) = step {
                let read = &pat[pat.len() - j - 1..];
                prop_assert_eq!(check_valid(&text, &sa, read, lo, hi), Ok(()));
            }
        }
    }
}
