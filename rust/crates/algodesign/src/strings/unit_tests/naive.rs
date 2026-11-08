// SPDX-License-Identifier: Apache-2.0
use super::*;

// One smoke test per oracle: the other modules' property tests use these as their differential.

#[test]
fn search_finds_every_occurrence() {
    assert_eq!(search(b"banana", b"ana"), vec![1, 3]);
    assert_eq!(search(b"banana", b"xyz"), Vec::<u32>::new());
    assert_eq!(search(b"banana", b""), vec![0, 1, 2, 3, 4, 5, 6]);
    assert_eq!(search(b"", b""), vec![0]);
}

#[test]
fn suffix_array_orders_suffixes_lexicographically() {
    assert_eq!(suffix_array(b"banana"), vec![5, 3, 1, 0, 4, 2]);
}

#[test]
fn bwt_rotations_of_banana_without_a_sentinel() {
    assert_eq!(bwt_rotations(b"banana"), b"nnbaaa".to_vec());
}

#[test]
fn rank_counts_bits_strictly_before_i() {
    let words = [0b1011u64];
    assert_eq!(rank(&words, 0), 0);
    assert_eq!(rank(&words, 1), 1);
    assert_eq!(rank(&words, 2), 2);
    assert_eq!(rank(&words, 3), 2);
    assert_eq!(rank(&words, 4), 3);
}
