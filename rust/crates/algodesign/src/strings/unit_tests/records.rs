// SPDX-License-Identifier: Apache-2.0
use super::*;
use proptest::prelude::*;

const QUOTES: [&[u8]; 3] = [
    b"to be or not to be that is the question",
    b"all the world is a stage",
    b"i have always depended on the kindness of strangers",
];

#[test]
fn any_remembered_fragment_returns_the_whole_quote() {
    let quotes: [&[u8]; 3] = [
        b"to be or not to be that is the question",
        b"all the world is a stage",
        b"i have always depended on the kindness of strangers",
    ];
    let corpus = Corpus::build(&quotes);
    for fragment in [
        b"to be or".as_slice(),
        b"not to be that",
        b"is the question",
    ] {
        let hits = corpus.find(fragment);
        assert_eq!(hits.len(), 1);
        assert_eq!(hits[0].text(), quotes[0]); // beginning, middle and end all return it whole
    }
    assert_eq!(corpus.find(b"kindness").len(), 1);
    // All three quotes hold "the".
    assert_eq!(corpus.find(b"the").len(), 3);
}

#[test]
fn start_middle_and_end_name_the_same_record_interval() {
    let corpus = Corpus::build(&QUOTES);
    // Start, middle or end of the quote: the same id and interval come back.
    let answers: Vec<(u32, (u32, u32), Vec<u8>)> = [
        b"to be or".as_slice(),
        b"not to be that",
        b"is the question",
    ]
    .iter()
    .map(|fragment| {
        let quote = corpus
            .find(fragment)
            .pop()
            .expect("each fragment is in quote 0");
        (quote.id(), quote.bounds(), quote.text().to_vec())
    })
    .collect();
    assert!(answers.iter().all(|answer| *answer == answers[0]));
    assert_eq!(answers[0].0, 0);
    assert_eq!(answers[0].1, (0, QUOTES[0].len() as u32 + 1));
    assert_eq!(answers[0].2, QUOTES[0]);
}

#[test]
fn two_occurrences_in_one_quote_are_one_hit() {
    let corpus = Corpus::build(&QUOTES);
    // "to be or not to be": two occurrences, one quote.
    assert_eq!(corpus.count(b"to be"), 2);
    let hits = corpus.find(b"to be");
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].text(), QUOTES[0]);
}

#[test]
fn a_fragment_spanning_two_records_finds_nothing() {
    let corpus = Corpus::build(&QUOTES);
    // No match straddles quotes 0 and 1, with or without the separator spelt out.
    assert!(corpus.find(b"questionall").is_empty());
    assert_eq!(corpus.count(b"questionall"), 0);
    let straddle = [b"question".as_slice(), &[SEPARATOR], b"all"].concat();
    assert!(corpus.find(&straddle).is_empty());
    assert_eq!(corpus.count(&straddle), 0);
    // Three quotes, two separators and the sentinel.
    assert_eq!(corpus.records().text_len() as usize, 39 + 24 + 51 + 3);
}

#[test]
fn pinned_straddling_match_without_the_guard() {
    // The straddle is in the concatenation; only the reserved-byte refusal keeps it out.
    let text = [
        QUOTES[0],
        &[SEPARATOR],
        QUOTES[1],
        &[SEPARATOR],
        QUOTES[2],
        &[bwt::SENTINEL],
    ]
    .concat();
    let straddle = [b"question".as_slice(), &[SEPARATOR], b"all"].concat();
    assert_eq!(FmIndex::build(&text, SAMPLE).count(&straddle), 1);
    assert_eq!(Corpus::build(&QUOTES).count(&straddle), 0);
}

#[test]
fn a_fragment_carrying_a_reserved_byte_finds_nothing() {
    let corpus = Corpus::build(&QUOTES);
    let tail = [b"strangers".as_slice(), &[bwt::SENTINEL]].concat();
    assert!(corpus.find(&tail).is_empty());
    assert!(corpus.find(&[bwt::SENTINEL]).is_empty());
    assert!(corpus.find(&[SEPARATOR]).is_empty());
}

#[test]
fn a_fragment_in_no_quote_finds_nothing() {
    let corpus = Corpus::build(&QUOTES);
    assert!(corpus.find(b"parting is such sweet sorrow").is_empty());
    assert!(corpus.find(b"zebra").is_empty());
    assert_eq!(corpus.count(b"zebra"), 0);
}

#[test]
fn an_empty_fragment_is_in_every_quote() {
    // Every quote contains the empty fragment; occurrences add up to the text's length.
    let corpus = Corpus::build(&QUOTES);
    let all: Vec<u32> = corpus.find(b"").iter().map(Quote::id).collect();
    assert_eq!(all, (0..QUOTES.len() as u32).collect::<Vec<_>>());
    let total: usize = QUOTES.iter().map(|q| q.len() + 1).sum();
    assert_eq!(corpus.count(b""), total);
    assert_eq!(total, corpus.records().text_len() as usize);
    // An empty record contains it too.
    let with_empty = Corpus::build(&[b"first".as_slice(), b"", b"third"]);
    assert_eq!(with_empty.find(b"").len(), 3);
    assert_eq!(with_empty.find(b"")[1].text(), b"");
}

#[test]
fn an_empty_corpus_finds_nothing() {
    let corpus = Corpus::build(&[]);
    // The empty corpus is a valid one (the shrunk `build_is_valid` case `records = []`).
    assert_eq!(corpus.check_valid(), Ok(()));
    assert!(corpus.is_empty());
    assert_eq!(corpus.len(), 0);
    // The concatenation is the sentinel alone.
    assert_eq!(corpus.records().text_len(), 1);
    assert!(corpus.find(b"anything").is_empty());
    assert_eq!(corpus.count(b"anything"), 0);
    assert!(corpus.find(b"").is_empty());
    assert_eq!(corpus.count(b""), 0);
}

#[test]
fn a_single_record_corpus_is_bounded_by_the_text_end() {
    let corpus = Corpus::build(&[b"alone".as_slice()]);
    assert_eq!(corpus.records().bounds(0), (0, 6));
    assert_eq!(corpus.find(b"lon")[0].text(), b"alone");
    assert_eq!(corpus.quote(0).text(), b"alone");
}

#[test]
fn an_empty_record_is_a_record() {
    // The empty record has an id and bounds, and holds no non-empty fragment.
    let corpus = Corpus::build(&[b"first".as_slice(), b"", b"third"]);
    assert_eq!(corpus.len(), 3);
    assert_eq!(corpus.records().bounds(1), (6, 7));
    assert_eq!(corpus.quote(1).text(), b"");
    assert_eq!(corpus.find(b"third")[0].id(), 2);
}

#[test]
#[should_panic(expected = "reserved byte")]
fn a_record_carrying_a_reserved_byte_is_rejected() {
    let _ = Corpus::build(&[b"fine".as_slice(), &[b'n', SEPARATOR, b'o']]);
}

#[test]
fn try_build_names_the_record_the_position_and_the_byte() {
    assert_eq!(
        Corpus::try_build(&[b"fine".as_slice(), &[b'n', SEPARATOR, b'o']]).err(),
        Some(BuildError::ReservedByte {
            record: 1,
            at: 1,
            byte: SEPARATOR,
        })
    );
    assert_eq!(
        Corpus::try_build(&[b"no".as_slice(), &[b'n', b'o', bwt::SENTINEL]]).err(),
        Some(BuildError::ReservedByte {
            record: 1,
            at: 2,
            byte: bwt::SENTINEL,
        })
    );
    // The first reserved byte of the first record that has one, whatever comes after.
    assert_eq!(
        Corpus::try_build(&[
            b"ok".as_slice(),
            &[b'a', bwt::SENTINEL, SEPARATOR],
            &[SEPARATOR]
        ])
        .err(),
        Some(BuildError::ReservedByte {
            record: 1,
            at: 1,
            byte: bwt::SENTINEL,
        })
    );
}

/// The length is refused before anything is allocated.
#[test]
fn try_build_refuses_a_concatenation_past_u32_max_before_allocating() {
    let block = vec![b'a'; 1 << 20];
    let records: Vec<&[u8]> = vec![block.as_slice(); 4097];
    let len = 4097 * ((1usize << 20) + 1);
    assert!(u32::try_from(len).is_err());
    assert_eq!(
        Corpus::try_build(&records).err(),
        Some(BuildError::TooLong { len })
    );
    // The length is checked before reserved bytes.
    let mut with_separator = records.clone();
    with_separator[0] = &[SEPARATOR];
    assert!(matches!(
        Corpus::try_build(&with_separator),
        Err(BuildError::TooLong { .. })
    ));
}

#[test]
fn build_panics_with_try_build_s_message() {
    let records: [&[u8]; 2] = [b"fine", &[b'n', SEPARATOR, b'o']];
    let Err(error) = Corpus::try_build(&records) else {
        panic!("a separator inside a record was accepted");
    };
    let panic = std::panic::catch_unwind(|| Corpus::build(&records)).expect_err("build panics");
    let message = panic
        .downcast_ref::<String>()
        .expect("a formatted panic message");
    assert_eq!(*message, error.to_string());
    assert!(message.contains("record 1 carries the reserved byte 1 at position 1"));
}

#[test]
fn try_build_on_clean_records_builds_the_corpus_build_builds() {
    let built = Corpus::build(&QUOTES);
    let tried = Corpus::try_build(&QUOTES).expect("no reserved byte in the quotes");
    assert!(tried.is_valid());
    for fragment in [b"the".as_slice(), b"be", b"strangers", b"", b"zzz"] {
        assert_eq!(tried.find(fragment), built.find(fragment));
    }
    assert!(Corpus::try_build(&[]).is_ok_and(|empty| empty.find(b"a").is_empty()));
}

#[test]
#[should_panic(expected = "must start at position 0")]
fn a_vector_whose_first_record_starts_late_is_rejected() {
    // Positions 0 and 1 would lie in no record.
    let _ = Records::new(&[2], 3);
}

// The theorems of `Records/Quote.lean`, against this code.

/// Record starts and a text length, with a record at position 0 as `hstart` requires.
fn a_layout() -> impl Strategy<Value = (Vec<u32>, u32)> {
    prop::collection::vec(1u32..12, 1..12).prop_map(|lengths| {
        let mut starts = Vec::with_capacity(lengths.len());
        let mut at = 0u32;
        for length in lengths {
            starts.push(at);
            at += length;
        }
        (starts, at)
    })
}

proptest! {
    /// The record named by a position contains that position.
    #[test]
    fn record_bounds_contain_every_position((starts, text_len) in a_layout()) {
        let records = Records::new(&starts, text_len);
        for pos in 0..text_len {
            // Lean: recordBounds_contains
            let (lo, hi) = records.bounds(records.record_of(pos));
            prop_assert!(lo <= pos, "{} <= {} failed", lo, pos);
            prop_assert!(pos < hi, "{} < {} failed", pos, hi);
        }
    }

    /// Every position inside one record names that record.
    #[test]
    fn positions_inside_one_record_name_one_quote((starts, text_len) in a_layout()) {
        let records = Records::new(&starts, text_len);
        for id in 0..records.len() as u32 {
            let (lo, hi) = records.bounds(id);
            for pos in lo..hi {
                prop_assert_eq!(records.record_of(pos), id); // Lean: recordOf_eq_of_no_start_between
            }
        }
    }

    /// `find` against a scan of the records.
    #[test]
    fn find_agrees_with_a_scan_of_the_records(
        records in prop::collection::vec(prop::collection::vec(2u8..5, 1..12), 1..6),
        fragment in prop::collection::vec(2u8..5, 1..4),
    ) {
        let slices: Vec<&[u8]> = records.iter().map(Vec::as_slice).collect();
        let corpus = Corpus::build(&slices);
        prop_assert!(corpus.is_valid());
        let expected: Vec<u32> = records
            .iter()
            .enumerate()
            .filter(|(_, record)| {
                record.len() >= fragment.len()
                    && record.windows(fragment.len()).any(|w| w == fragment.as_slice())
            })
            .map(|(id, _)| id as u32)
            .collect();
        let found = corpus.find(&fragment);
        prop_assert_eq!(found.iter().map(Quote::id).collect::<Vec<_>>(), expected);
        for quote in &found {
            prop_assert_eq!(quote.text(), records[quote.id() as usize].as_slice());
        }
    }
}

/// `find` spends each hit on `record_of` as it is located, not after locating them all.
#[test]
fn find_spends_each_hit_as_it_arrives() {
    let record: &[u8] = b"xyabxyab";
    let corpus = Corpus::build(&[record; 30]);
    crate::strings::fm_index::LOCATED.with(|n| n.set(0));
    QUOTED_AFTER.with(|log| log.borrow_mut().clear());
    let found = corpus.find(b"ab");
    assert_eq!(found.len(), 30);
    let log = QUOTED_AFTER.with(|log| log.borrow().clone());
    assert_eq!(log, (1..=60).collect::<Vec<_>>());
}

/// `find_iter` is `find` one quote at a time, extracting each when drawn.
#[test]
fn find_iter_extracts_only_the_quotes_drawn() {
    use crate::strings::fm_index::{LF_STEPS, LOCATED};
    let corpus = Corpus::build(&QUOTES);
    for fragment in [&b""[..], b"the", b"is", b"zz", b"a\x01"] {
        assert_eq!(
            corpus.find_iter(fragment).collect::<Vec<_>>(),
            corpus.find(fragment)
        );
    }
    let record: &[u8] = b"xyabxyab";
    let corpus = Corpus::build(&[record; 30]);
    LOCATED.with(|n| n.set(0));
    let mut quotes = corpus.find_iter(b"ab");
    assert_eq!(
        LOCATED.with(std::cell::Cell::get),
        60,
        "the hits are located up front"
    );
    LF_STEPS.with(|n| n.set(0));
    assert_eq!(quotes.next().map(|q| q.id), Some(0));
    let one = LF_STEPS.with(std::cell::Cell::get);
    assert!(one > 0, "the drawn quote was extracted");
    assert_eq!(quotes.count(), 29);
    assert!(
        LF_STEPS.with(std::cell::Cell::get) > one,
        "the other 29 were extracted only when drawn"
    );
}

proptest! {
    /// Any record list `build` accepts, empty records and the empty list included.
    #[test]
    fn build_is_valid(records in prop::collection::vec(prop::collection::vec(2u8..5, 0..12), 0..6)) {
        let slices: Vec<&[u8]> = records.iter().map(Vec::as_slice).collect();
        let corpus = Corpus::build(&slices);
        prop_assert!(corpus.records().is_valid());
        prop_assert!(corpus.is_valid());
        prop_assert_eq!(corpus.check_valid(), Ok(()));
    }
}

#[test]
fn built_corpora_are_valid() {
    let empty = Corpus::build(&[]);
    assert!(empty.records().is_valid() && empty.is_valid());
    let three = Corpus::build(&[b"ab".as_slice(), b"", b"c"]);
    assert!(three.is_valid());
}

/// `ab`, the empty record and `c`: `ab|.|c$` with starts 0, 3 and 4.
fn three() -> Corpus {
    Corpus::build(&[b"ab".as_slice(), b"", b"c"])
}

/// The start bits of a corpus.
fn bits(corpus: &Corpus) -> Vec<bool> {
    let starts = &corpus.records.starts;
    (0..starts.len()).map(|i| starts.get(i)).collect()
}

/// Which of the corpus's five conjuncts hold.
fn conjuncts(corpus: &Corpus) -> [bool; 5] {
    [
        corpus.index.is_valid(),
        corpus.records.starts_at_zero(),
        corpus.records.count_matches(),
        corpus.lengths_agree(),
        corpus.reserved_bytes_placed(),
    ]
}

#[test]
fn clearing_the_first_start_breaks_starts_at_zero_alone() {
    let mut corpus = three();
    let mut b = bits(&corpus);
    b[0] = false;
    corpus.records = Records::assemble(&b, 2);
    assert_eq!(conjuncts(&corpus), [true, false, true, true, true]);
    assert!(!corpus.records.is_valid() && !corpus.is_valid());
    assert_eq!(corpus.check_valid(), Err("not in the box (starts_at_zero)"));
}

#[test]
fn a_wrong_count_breaks_count_matches_alone() {
    let mut corpus = three();
    corpus.records.count += 1;
    assert_eq!(conjuncts(&corpus), [true, true, false, true, true]);
    assert!(!corpus.records.is_valid() && !corpus.is_valid());
    assert_eq!(corpus.records.check_valid(), Err("layout (count_matches)"));
}

#[test]
fn records_over_a_longer_text_break_lengths_agree_alone() {
    let mut corpus = three();
    let mut b = bits(&corpus);
    b.push(false);
    corpus.records = Records::assemble(&b, 3);
    assert_eq!(conjuncts(&corpus), [true, true, true, false, true]);
    assert!(!corpus.is_valid());
    assert_eq!(corpus.check_valid(), Err("layout (lengths_agree)"));
}

#[test]
fn a_start_shifted_by_one_breaks_reserved_bytes_placed_alone() {
    let mut corpus = three();
    let mut b = bits(&corpus);
    (b[3], b[2]) = (false, true);
    corpus.records = Records::assemble(&b, 3);
    assert_eq!(conjuncts(&corpus), [true, true, true, true, false]);
    assert!(!corpus.is_valid());
    assert_eq!(
        corpus.check_valid(),
        Err("not in the box (reserved_bytes_placed)")
    );
}

#[test]
fn a_reserved_byte_inside_a_record_breaks_reserved_bytes_placed() {
    // `a\x01b` as one record, indexed directly.
    let corpus = Corpus {
        index: FmIndex::build(&[b'a', SEPARATOR, b'b', bwt::SENTINEL], SAMPLE),
        records: Records::new(&[0], 4),
    };
    assert_eq!(conjuncts(&corpus), [true, true, true, true, false]);
}

#[test]
fn reserved_bytes_placed_answers_on_a_corrupted_index() {
    let mut corpus = three();
    corpus.index = FmIndex::assemble(&[b'c', 0, 1], vec![0, 1, 2], &[false; 3], &[], &[], 1);
    assert!(!corpus.index.is_valid());
    assert!(!corpus.reserved_bytes_placed());
    assert!(!corpus.is_valid());
}

#[cfg(feature = "unchecked")]
#[test]
fn records_parts_round_trip() {
    let corpus = three();
    let b = corpus.records().to_bits();
    let again = Records::from_parts_unchecked(&b, corpus.len());
    assert_eq!(again.to_bits(), b);
    assert!(again.is_valid());
    assert_eq!(again.bounds(1), corpus.records().bounds(1));
}

/// `record_of` past the text saturates to the last record, as its doc says.
#[test]
fn record_of_past_the_text_answers_the_last_record() {
    let records = Records::new(&[0, 5], 10);
    for pos in [9, 10, 1_000_000, u32::MAX] {
        assert_eq!(records.record_of(pos), 1);
    }
}
