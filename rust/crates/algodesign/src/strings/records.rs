// SPDX-License-Identifier: Apache-2.0
//! A corpus of records under one FM-index: a hit becomes its whole record by one `rank` and two
//! `select`s ("From a hit to the whole quote" in the Strings chapter).
//!
//! Lean: `Records/Quote.lean` and `Records/Corpus.lean` (a model of [`Corpus::find`] and
//! [`Corpus::quote`]).

use crate::strings::bwt;
use crate::strings::count_index::BitIndex;
use crate::strings::fm_index::{FmIndex, SAMPLE};

/// The byte that ends each record in a [`Corpus`]'s concatenation. No record may contain it.
pub const SEPARATOR: u8 = 1;

/// A bitvector of record starts: `rank` names a position's record, `select` bounds it. Lean:
/// `recordOf`, `recordBounds`. Built by [`Records::new`]; the unchecked constructor needs the
/// `unchecked` feature, for tests that build broken records on purpose: `cargo test --features
/// unchecked`.
#[derive(Clone)]
pub struct Records {
    starts: BitIndex,
    text_len: u32,
    /// Cached: [`BitIndex`] has no population count.
    count: usize,
}

impl Records {
    /// Index `starts` (strictly increasing, first `0`) over a text of `text_len` bytes.
    ///
    /// # Panics
    ///
    /// If `starts` is not strictly increasing, does not begin at `0`, or reaches `text_len`.
    #[must_use]
    pub fn new(starts: &[u32], text_len: u32) -> Records {
        assert!(
            starts.first().is_none_or(|&first| first == 0),
            "records::Records::new: the first record must start at position 0, not {}; \
             a position before the first start lies in no record (Records/Quote.lean's `hstart`)",
            starts[0]
        );
        assert!(
            starts.windows(2).all(|pair| pair[0] < pair[1]),
            "records::Records::new: record starts must be strictly increasing"
        );
        assert!(
            starts.last().is_none_or(|&last| last < text_len),
            "records::Records::new: record start {} is not inside a {text_len}-byte text",
            starts.last().copied().unwrap_or_default()
        );

        let mut bits = vec![0u64; (text_len as usize).div_ceil(64)];
        for &start in starts {
            bits[start as usize / 64] |= 1u64 << (start % 64);
        }
        Records {
            starts: BitIndex::new(&bits, text_len as usize),
            text_len,
            count: starts.len(),
        }
    }

    /// The records `bits` marks, with `count` as given; nothing is checked.
    ///
    /// # Panics
    ///
    /// If `bits` is longer than `u32::MAX`.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn from_parts_unchecked(bits: &[bool], count: usize) -> Records {
        Records::assemble(bits, count)
    }

    #[cfg(any(test, feature = "unchecked"))]
    pub(crate) fn assemble(bits: &[bool], count: usize) -> Records {
        let mut words = vec![0u64; bits.len().div_ceil(64)];
        for (i, &b) in bits.iter().enumerate() {
            words[i / 64] |= u64::from(b) << (i % 64);
        }
        Records {
            starts: BitIndex::new(&words, bits.len()),
            text_len: u32::try_from(bits.len())
                .expect("one index covers at most u32::MAX positions"),
            count,
        }
    }

    /// The start bits, one per text position.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn to_bits(&self) -> Vec<bool> {
        (0..self.starts.len()).map(|i| self.starts.get(i)).collect()
    }

    /// If any record starts, one starts at position 0. Lean: `FirstRecordAtStart`.
    #[must_use]
    pub fn starts_at_zero(&self) -> bool {
        self.starts.rank(self.starts.len()) == 0 || self.starts.get(0)
    }

    /// `count` equals the number of starts.
    #[must_use]
    pub fn count_matches(&self) -> bool {
        self.count == self.starts.rank(self.text_len as usize)
    }

    /// [`Records::starts_at_zero`] and [`Records::count_matches`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// The first check [`Records::is_valid`] finds broken, in its order:
    /// `"not in the box (starts_at_zero)"` or `"layout (count_matches)"`.
    ///
    /// # Errors
    ///
    /// That label, when a check fails.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.starts_at_zero() {
            return Err("not in the box (starts_at_zero)");
        }
        if !self.count_matches() {
            return Err("layout (count_matches)");
        }
        Ok(())
    }

    /// Records indexed.
    #[must_use]
    pub fn len(&self) -> usize {
        self.count
    }

    /// Whether there are no records.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// Bytes of text the starts cover.
    #[must_use]
    pub fn text_len(&self) -> u32 {
        self.text_len
    }

    /// The record `pos` falls in, from zero; past the text, the last record. `O(1)`. Lean:
    /// `recordOf`.
    ///
    /// # Panics
    ///
    /// If there are no records.
    #[must_use]
    pub fn record_of(&self, pos: u32) -> u32 {
        #[cfg(test)]
        QUOTED_AFTER.with(|log| {
            log.borrow_mut()
                .push(crate::strings::fm_index::LOCATED.with(std::cell::Cell::get));
        });
        let at_or_before = self.starts.rank(pos as usize + 1);
        assert!(
            at_or_before > 0,
            "records::record_of: no record starts at or before position {pos}; \
             this corpus holds no records"
        );
        u32::try_from(at_or_before - 1).expect("record ids are bounded by the u32 text length")
    }

    /// The half-open bounds `[start, end)` of record `id`, closing reserved byte included.
    /// `O(log n)`. Lean: `recordBounds`.
    ///
    /// # Panics
    ///
    /// If `id` is not a record of this index.
    #[must_use]
    pub fn bounds(&self, id: u32) -> (u32, u32) {
        assert!(
            (id as usize) < self.count,
            "records::bounds: record {id} of {}",
            self.count
        );
        let start = self
            .starts
            .select(id as usize)
            .expect("id is below the number of set bits, so the id-th start exists");
        let end = self
            .starts
            .select(id as usize + 1)
            .map_or(self.text_len, |next| {
                u32::try_from(next).expect("positions are u32")
            });
        (u32::try_from(start).expect("positions are u32"), end)
    }
}

/// One whole record, recovered from a hit inside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Quote {
    id: u32,
    bounds: (u32, u32),
    text: Vec<u8>,
}

impl Quote {
    /// Which record of the corpus this is, in build order.
    #[must_use]
    pub fn id(&self) -> u32 {
        self.id
    }

    /// Its bounds in the concatenation, as [`Records::bounds`] reports them.
    #[must_use]
    pub fn bounds(&self) -> (u32, u32) {
        self.bounds
    }

    /// The record's bytes.
    #[must_use]
    pub fn text(&self) -> &[u8] {
        &self.text
    }
}

/// Why [`Corpus::try_build`] refused its records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum BuildError {
    /// Record `record` holds the reserved byte `byte` at position `at` (the first such).
    ReservedByte {
        /// Index of the record.
        record: usize,
        /// Position of the byte inside that record.
        at: usize,
        /// The reserved byte found there.
        byte: u8,
    },
    /// The concatenation would be `len` bytes, more than `u32::MAX`.
    TooLong {
        /// The concatenation's length, sentinel included.
        len: usize,
    },
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ReservedByte { record, at, byte } => write!(
                f,
                "records::Corpus: record {record} carries the reserved byte {byte} at \
                 position {at}; bwt::SENTINEL (0) terminates the concatenation and SEPARATOR (1) \
                 divides it, so no record may hold either"
            ),
            Self::TooLong { len } => write!(
                f,
                "records::Corpus: the records concatenate to {len} bytes, more than the \
                 u32::MAX positions one index covers; shard the corpus at a record boundary"
            ),
        }
    }
}

impl std::error::Error for BuildError {}

/// Records under one [`FmIndex`], searched by fragment, answering with whole records extracted
/// from the index. The unchecked constructor needs the `unchecked` feature, for tests that build
/// a broken corpus on purpose: `cargo test --features unchecked`.
#[derive(Clone)]
pub struct Corpus {
    index: FmIndex,
    records: Records,
}

impl Corpus {
    /// Build the index over `records`, in order. `O(n log n)` in the total size.
    ///
    /// # Errors
    ///
    /// [`BuildError::TooLong`] past `u32::MAX` bytes; [`BuildError::ReservedByte`] if a record
    /// holds [`bwt::SENTINEL`] or [`SEPARATOR`].
    #[allow(
        clippy::missing_panics_doc,
        reason = "the expects cannot fire: the total length was checked against u32::MAX first"
    )]
    pub fn try_build(records: &[&[u8]]) -> Result<Corpus, BuildError> {
        let len = records
            .iter()
            .fold(0usize, |total, r| {
                total.saturating_add(r.len()).saturating_add(1)
            })
            .max(1);
        if u32::try_from(len).is_err() {
            return Err(BuildError::TooLong { len });
        }
        // Every record is checked before anything is allocated or copied.
        for (id, record) in records.iter().enumerate() {
            if let Some(at) = record
                .iter()
                .position(|&b| b == bwt::SENTINEL || b == SEPARATOR)
            {
                return Err(BuildError::ReservedByte {
                    record: id,
                    at,
                    byte: record[at],
                });
            }
        }
        let mut text = Vec::with_capacity(len);
        let mut starts = Vec::with_capacity(records.len());
        for record in records {
            starts.push(
                u32::try_from(text.len())
                    .expect("one index covers at most u32::MAX positions; shard the corpus"),
            );
            text.extend_from_slice(record);
            text.push(SEPARATOR);
        }
        // The last separator becomes the sentinel that terminates the concatenation.
        match text.last_mut() {
            Some(last) => *last = bwt::SENTINEL,
            None => text.push(bwt::SENTINEL),
        }
        let text_len = u32::try_from(text.len())
            .expect("one index covers at most u32::MAX positions; shard the corpus");

        Ok(Corpus {
            index: FmIndex::build(&text, SAMPLE),
            records: Records::new(&starts, text_len),
        })
    }

    /// [`Corpus::try_build`], panicking on its error.
    ///
    /// # Panics
    ///
    /// Whenever [`Corpus::try_build`] returns an error.
    #[must_use]
    pub fn build(records: &[&[u8]]) -> Corpus {
        Corpus::try_build(records).unwrap_or_else(|e| panic!("{e}"))
    }

    /// The corpus `index` and `records` make, as given; nothing is checked.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn from_parts_unchecked(index: FmIndex, records: Records) -> Corpus {
        Corpus { index, records }
    }

    /// The records cover exactly the text the index holds.
    #[must_use]
    pub fn lengths_agree(&self) -> bool {
        self.records.text_len as usize == self.index.text_len()
    }

    /// The separators sit just before each start after the first, and nowhere else (read through
    /// the index). The sentinel's place, the text's end, is the index's own: a valid index ends
    /// its text with it. `false` on an invalid index.
    #[must_use]
    pub fn reserved_bytes_placed(&self) -> bool {
        if !self.index.is_valid() {
            return false;
        }
        let starts = &self.records.starts;
        let want: Vec<u32> = (1..starts.len())
            .filter(|&i| starts.get(i))
            .map(|i| u32::try_from(i - 1).unwrap_or(u32::MAX))
            .collect();
        let mut separators = self.index.locate(&[SEPARATOR]);
        separators.sort_unstable();
        separators == want
    }

    /// [`FmIndex::is_valid`], [`Records::is_valid`], [`Corpus::lengths_agree`] and
    /// [`Corpus::reserved_bytes_placed`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// The first check [`Corpus::is_valid`] finds broken, in its order: the index's own
    /// [`FmIndex::check_valid`] label, then the records' [`Records::check_valid`], then
    /// `"layout (lengths_agree)"` or `"not in the box (reserved_bytes_placed)"`.
    ///
    /// # Errors
    ///
    /// That label, when a check fails.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        self.index.check_valid()?;
        self.records.check_valid()?;
        if !self.lengths_agree() {
            return Err("layout (lengths_agree)");
        }
        if !self.reserved_bytes_placed() {
            return Err("not in the box (reserved_bytes_placed)");
        }
        Ok(())
    }

    /// Records in the corpus.
    #[must_use]
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Whether the corpus holds no records.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    /// The record starts.
    #[must_use]
    pub fn records(&self) -> &Records {
        &self.records
    }

    /// How many times `fragment` occurs, counting repeats within a record: one
    /// [`FmIndex::count`], with no position located. `O(m)`. Lean: `matchCount`.
    ///
    /// The empty fragment is at every position of every record, its end included, as the
    /// chapter has it: `count(b"")` is the sum of each record's length plus one, while
    /// [`Corpus::find`] answers each record once.
    #[must_use]
    pub fn count(&self, fragment: &[u8]) -> usize {
        if self.is_empty() || Self::is_unsearchable(fragment) {
            return 0;
        }
        self.index.count(fragment)
    }

    /// The whole of record `id`, decoded from the index. `O(len + 32)`. Lean:
    /// `Corpus.quoteObligation`.
    ///
    /// # Panics
    ///
    /// If `id` is not a record of this corpus.
    #[must_use]
    pub fn quote(&self, id: u32) -> Quote {
        let (start, end) = self.records.bounds(id);
        Quote {
            id,
            bounds: (start, end),
            text: self.index.extract(start, end - start - 1),
        }
    }

    /// Every quote containing `fragment`, once each, in corpus order; the empty fragment answers
    /// every quote. Lean: `Corpus.findObligation`.
    #[must_use]
    pub fn find(&self, fragment: &[u8]) -> Vec<Quote> {
        self.find_iter(fragment).collect()
    }

    /// [`Self::find`]'s quotes one at a time: ids are found now, each text when drawn.
    pub fn find_iter(&self, fragment: &[u8]) -> impl Iterator<Item = Quote> + '_ {
        let (every, ids) = if fragment.is_empty() {
            // At most one record per byte of a text of at most `u32::MAX` bytes.
            #[allow(
                clippy::cast_possible_truncation,
                reason = "at most one record per byte of a text of at most u32::MAX bytes"
            )]
            let records = self.records.len() as u32;
            (records, None)
        } else if Self::is_unsearchable(fragment) {
            (0, None)
        } else {
            (0, Some(self.ids_holding(fragment)))
        };
        (0..every)
            .chain(ids.into_iter().flatten())
            .map(move |id| self.quote(id))
    }

    /// The ids of the quotes holding a nonempty, searchable `fragment`, ascending, each once.
    fn ids_holding(&self, fragment: &[u8]) -> impl Iterator<Item = u32> {
        // One insert per hit: `collect()` would buffer every hit first.
        let mut ids = std::collections::BTreeSet::new();
        for hit in self.index.locate_iter(fragment) {
            ids.insert(self.records.record_of(hit));
        }
        ids.into_iter()
    }

    /// Whether `fragment` holds a reserved byte.
    fn is_unsearchable(fragment: &[u8]) -> bool {
        fragment
            .iter()
            .any(|&b| b == bwt::SENTINEL || b == SEPARATOR)
    }
}

impl std::fmt::Debug for Records {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Records")
            .field("len", &self.len())
            .field("text_len", &self.text_len())
            .finish_non_exhaustive()
    }
}

impl std::fmt::Debug for Corpus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Corpus")
            .field("records", &self.records)
            .field("index", &self.index)
            .finish()
    }
}

#[cfg(test)]
thread_local! {
    /// For each `record_of`, how many hits had been located by then.
    static QUOTED_AFTER: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(test)]
#[path = "unit_tests/records.rs"]
mod tests;
