// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::strings::suffix_array::suffix_array;
use proptest::prelude::*;

fn lcp_naive(text: &[u8], sa: &[u32]) -> Vec<u32> {
    let mut out = vec![0u32; sa.len()];
    for i in 1..sa.len() {
        let (a, b) = (&text[sa[i - 1] as usize..], &text[sa[i] as usize..]);
        out[i] = a.iter().zip(b).take_while(|(x, y)| x == y).count() as u32;
    }
    out
}

/// Every substring, counted where it starts: the longest that starts in two places, the
/// smallest of those, empty if none. `O(n^3)`, which is the point of an oracle.
fn longest_repeat_naive(text: &[u8]) -> Vec<u8> {
    let mut best = Vec::new();
    for len in 1..text.len() {
        let mut seen = std::collections::BTreeMap::<&[u8], usize>::new();
        for w in text.windows(len) {
            *seen.entry(w).or_default() += 1;
        }
        match seen.into_iter().find(|&(_, c)| c >= 2) {
            Some((w, _)) => best = w.to_vec(), // BTreeMap order: the smallest repeat
            None => break,                     // no repeat of this length means none longer either
        }
    }
    best
}

proptest! {
    #[test]
    fn longest_repeat_matches_the_definition(text in prop::collection::vec(0u8..4, 0..60)) {
        prop_assert_eq!(longest_repeat(&text).to_vec(), longest_repeat_naive(&text));
    }

    #[test]
    fn kasai_matches_the_definition(text in prop::collection::vec(0u8..4, 1..300)) {
        let sa = suffix_array(&text);
        prop_assert_eq!(lcp(&text, &sa), lcp_naive(&text, &sa));      // Lean: kasai_eq
    }
}

#[test]
fn longest_repeat_on_the_textbook_examples() {
    assert_eq!(longest_repeat(b"banana"), b"ana"); // the two occurrences overlap
    assert_eq!(longest_repeat(b"mississippi"), b"issi");
    assert_eq!(longest_repeat(b"abcd"), b"");
    assert_eq!(longest_repeat(b""), b"");
    assert_eq!(longest_repeat(b"abab"), b"ab");
    assert_eq!(longest_repeat(b"abxba"), b"a"); // "a" and "b" tie: the smaller wins
}

#[test]
fn banana() {
    // Suffix order: a, ana, anana, banana, na, nana.
    let sa = suffix_array(b"banana");
    assert_eq!(sa, vec![5, 3, 1, 0, 4, 2]);
    assert_eq!(lcp(b"banana", &sa), vec![0, 1, 3, 0, 0, 2]);
}

#[test]
fn empty_and_single_byte_texts() {
    // Outside the proptest's length range.
    assert_eq!(lcp(b"", &[]), Vec::<u32>::new());
    assert_eq!(lcp(b"a", &[0]), vec![0]);
}

/// Without the decrement the carried `h` overshoots; `aaa` is the shortest text that shows it.
#[test]
fn without_the_decrement_aaa_comes_out_wrong() {
    fn kasai_without_the_decrement(text: &[u8], sa: &[u32]) -> Vec<u32> {
        let n = text.len();
        let mut rank = vec![0usize; n];
        for (i, &p) in sa.iter().enumerate() {
            rank[p as usize] = i;
        }
        let (mut out, mut h) = (vec![0u32; n], 0usize);
        for p in 0..n {
            if rank[p] > 0 {
                let q = sa[rank[p] - 1] as usize;
                while p + h < n && q + h < n && text[p + h] == text[q + h] {
                    h += 1;
                }
                out[rank[p]] = u32::try_from(h).unwrap();
            }
        }
        out
    }
    let sa = suffix_array(b"aaa");
    assert_eq!(lcp(b"aaa", &sa), vec![0, 1, 2]);
    assert_eq!(kasai_without_the_decrement(b"aaa", &sa), vec![0, 2, 2]);
    // No text over {a, b} shorter than three bytes tells the two loops apart.
    for len in 0..3 {
        for bits in 0..1u32 << len {
            let text: Vec<u8> = (0..len)
                .map(|k| b'a' + u8::from(bits >> k & 1 == 1))
                .collect();
            let sa = suffix_array(&text);
            assert_eq!(kasai_without_the_decrement(&text, &sa), lcp(&text, &sa));
        }
    }
}

#[test]
#[should_panic(expected = "sa must be the suffix array of text")]
fn mismatched_lengths_panic() {
    let _ = lcp(b"banana", &[0, 1]);
}

/// At most `2n` successful comparisons, where restarting `h` at 0 would make `n (n - 1) / 2`
/// on all-equal bytes.
#[test]
fn comparison_count_is_linear_on_a_concrete_input() {
    let matched = |text: &[u8]| {
        let sa = suffix_array(text);
        MATCHED.with(|m| m.set(0));
        assert_eq!(lcp(text, &sa), lcp_naive(text, &sa));
        MATCHED.with(std::cell::Cell::get)
    };
    let n = 2000;
    let naive_sum: usize = {
        let text = vec![7u8; n];
        let sa = suffix_array(&text);
        lcp_naive(&text, &sa).iter().map(|&x| x as usize).sum()
    };
    assert_eq!(naive_sum, n * (n - 1) / 2);
    // Carried forward, `h` grows once per position after the first: n - 1 in all.
    assert_eq!(matched(&vec![7u8; n]), n - 1);
    let mut state = 0x1357_9bdf_u32;
    for alphabet in [2u32, 3, 26] {
        let text: Vec<u8> = (0..n)
            .map(|_| {
                state ^= state << 13;
                state ^= state >> 17;
                state ^= state << 5;
                (state % alphabet) as u8
            })
            .collect();
        let grown = matched(&text);
        assert!(
            grown <= 2 * n,
            "{grown} successful comparisons, bound 2n = {}",
            2 * n
        );
    }
    let periodic: Vec<u8> = b"abaab".iter().copied().cycle().take(n).collect();
    let grown = matched(&periodic);
    assert!(
        grown <= 2 * n,
        "{grown} successful comparisons, bound 2n = {}",
        2 * n
    );
}
