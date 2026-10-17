// SPDX-License-Identifier: Apache-2.0
//! The compressed **FM-index**: count, locate and extract over a sentinel-terminated text without
//! the text, in less space than the text.
//!
//! Navarro, *Compact Data Structures* §11.2-§11.3, the column as chunked wavelet trees
//! (Kärkkäinen and Puglisi, 2011). Lean: `lean/AlgoDesign/Strings/FMIndex/`.
//!
//! **Against the Python, and how fast.** The same compressed structure the Python builds, chunked
//! wavelet trees over the last column, an RRR marker and both kept-position arrays packed at
//! `⌈log2 n⌉` bits; `sample` is the chapter's rate. `cargo bench -p algodesign --bench strings`
//! times `count`, `locate` and `extract` and prints the index's size, after
//! `scripts/fetch_corpus.sh`.

use crate::strings::bits::{read_bits, write_bits};
use crate::strings::bwt;
use crate::strings::chunked_wavelet::ChunkedWavelet;
use crate::strings::occ::Occ;
use crate::strings::rrr::Rrr;

/// The default sampling rate (Navarro's `l`, both samples): one text position in 32 is sampled.
/// [`FmIndex::new`] builds at it.
pub const SAMPLE: u32 = 32;

#[cfg(test)]
thread_local! {
    pub(crate) static LF_STEPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    pub(crate) static LOCATED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Unsigned integers packed at a fixed width, `⌈log2 n⌉` bits a value: the sample arrays.
#[derive(Clone, PartialEq, Eq)]
struct Packed {
    words: Vec<u64>,
    width: u32,
    len: usize,
}

impl Packed {
    fn new(values: &[u32], bound: usize) -> Packed {
        let width = (usize::BITS - bound.saturating_sub(1).leading_zeros()).max(1);
        let mut words = vec![0u64; (values.len() * width as usize).div_ceil(64) + 1];
        for (k, &v) in values.iter().enumerate() {
            write_bits(&mut words, k * width as usize, width, u64::from(v));
        }
        Packed {
            words,
            width,
            len: values.len(),
        }
    }

    #[inline]
    #[allow(
        clippy::cast_possible_truncation,
        reason = "a value is `width <= 32` bits wide"
    )]
    fn get(&self, k: usize) -> usize {
        debug_assert!(k < self.len);
        read_bits(&self.words, k * self.width as usize, self.width) as usize
    }

    fn try_get(&self, k: usize) -> Option<usize> {
        (k < self.len).then(|| self.get(k))
    }

    fn size_bytes(&self) -> usize {
        self.words.len() * size_of::<u64>()
    }
}

/// A self-contained, compressed index over one sentinel-terminated text: counts, locates and
/// extracts without the text. `O` holds the last column, [`ChunkedWavelet`] by default.
///
/// The parameter is the crate's test device, not an extension point: [`Occ`] is sealed, and only
/// the default `FmIndex` has a public constructor. The tests build the same index over the plain
/// [`ByteIndex`](crate::strings::count_index::ByteIndex) and over a
/// [`WaveletTree`](crate::strings::wavelet_tree::WaveletTree) and hold the compressed column to
/// them.
///
/// Built only by [`FmIndex::new`], [`FmIndex::build`] or [`FmIndex::try_build`];
/// `from_parts_unchecked` exists only behind the `unchecked` feature, for tests that build a
/// broken index on purpose: `cargo test --features unchecked`.
#[derive(Clone)]
pub struct FmIndex<O: Occ = ChunkedWavelet> {
    occ: O,
    c: Vec<u32>,
    marks: Rrr,
    sa_samples: Packed,
    isa_samples: Packed,
    sample: u32,
}

impl FmIndex {
    /// Build the index over a sentinel-terminated `text` at the default rate, [`SAMPLE`]:
    /// `FmIndex::build(text, SAMPLE)`. `O(n log n)`.
    ///
    /// ```
    /// use algodesign::strings::fm_index::FmIndex;
    ///
    /// assert_eq!(FmIndex::new(b"banana\0").count(b"ana"), 2);
    /// ```
    ///
    /// # Panics
    ///
    /// Where [`FmIndex::try_build`] errs.
    #[must_use]
    pub fn new(text: &[u8]) -> FmIndex {
        FmIndex::build(text, SAMPLE)
    }

    /// Build the index over a sentinel-terminated `text`, sampling every `sample`-th text
    /// position. `O(n log n)`.
    ///
    /// # Errors
    ///
    /// [`bwt::EncodeError`] where [`bwt::try_encode`] rejects `text`.
    ///
    /// # Panics
    ///
    /// If `sample` is zero, a broken contract rather than outside input.
    pub fn try_build(text: &[u8], sample: u32) -> Result<FmIndex, bwt::EncodeError> {
        FmIndex::try_build_over(text, sample, ChunkedWavelet::new)
    }

    /// [`FmIndex::try_build`], panicking instead of returning an error.
    ///
    /// # Panics
    ///
    /// If `sample` is zero, or where [`FmIndex::try_build`] errs.
    #[must_use]
    pub fn build(text: &[u8], sample: u32) -> FmIndex {
        FmIndex::try_build(text, sample).unwrap_or_else(|e| panic!("{e}"))
    }

    /// [`FmIndex::build`] with the last column in chunks of `chunk` symbols.
    ///
    /// # Panics
    ///
    /// As [`FmIndex::build`], and if `chunk` is zero.
    #[must_use]
    pub fn build_with_chunk(text: &[u8], sample: u32, chunk: usize) -> FmIndex {
        FmIndex::try_build_over(text, sample, |last| ChunkedWavelet::with_chunk(last, chunk))
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Symbols per chunk of the last column.
    #[must_use]
    pub fn chunk_len(&self) -> usize {
        self.occ.chunk_len()
    }

    /// The index `parts` writes out, unchecked: it may break [`FmIndex::is_valid`]. Behind the
    /// `unchecked` feature.
    ///
    /// # Panics
    ///
    /// If the column or the marks are longer than `u32::MAX`.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn from_parts_unchecked(parts: FmParts) -> FmIndex {
        FmIndex::assemble(
            &parts.last,
            parts.c,
            &parts.marks,
            &parts.sa_samples,
            &parts.isa_samples,
            parts.sample,
        )
    }

    #[cfg(any(test, feature = "unchecked"))]
    pub(crate) fn assemble(
        last: &[u8],
        c: Vec<u32>,
        marks: &[bool],
        sa_samples: &[u32],
        isa_samples: &[u32],
        sample: u32,
    ) -> FmIndex {
        let bound = |values: &[u32]| {
            let top = values.iter().map(|&v| v as usize + 1).max().unwrap_or(0);
            top.max(last.len())
        };
        FmIndex {
            occ: ChunkedWavelet::new(last),
            c,
            marks: Rrr::from_bools(marks),
            sa_samples: Packed::new(sa_samples, bound(sa_samples)),
            isa_samples: Packed::new(isa_samples, bound(isa_samples)),
            sample,
        }
    }
}

/// An FM-index written out as plain data, one field per stored piece. Behind the `unchecked`
/// feature.
#[cfg(feature = "unchecked")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FmParts {
    /// The last column `L`.
    pub last: Vec<u8>,
    /// `C`, indexed by dense symbol.
    pub c: Vec<u32>,
    /// `B`, one bit per row.
    pub marks: Vec<bool>,
    /// `A_S`, the text positions of the marked rows, in row order.
    pub sa_samples: Vec<u32>,
    /// `A⁻¹_S`, the rows of text positions `0, k, 2k, …`.
    pub isa_samples: Vec<u32>,
    /// `k`, the sampling rate.
    pub sample: u32,
}

impl<O: Occ> FmIndex<O> {
    #[cfg(test)]
    pub(crate) fn build_over(text: &[u8], sample: u32, make: impl FnOnce(&[u8]) -> O) -> Self {
        Self::try_build_over(text, sample, make).unwrap_or_else(|e| panic!("{e}"))
    }

    fn try_build_over(
        text: &[u8],
        sample: u32,
        make: impl FnOnce(&[u8]) -> O,
    ) -> Result<Self, bwt::EncodeError> {
        assert!(
            sample > 0,
            "fm_index::build: the sampling rate must be positive, got {sample}"
        );
        let (last, sa) = bwt::try_encode_with_sa(text)?;
        let n = last.len();
        let step = sample as usize;
        let occ = make(&last);

        // C, by prefix sum over the alphabet in ascending byte order.
        let mut c = Vec::with_capacity(occ.alphabet().len());
        let mut below = 0u32;
        for &symbol in occ.alphabet().symbols() {
            c.push(below);
            below += u32::try_from(occ.occ(symbol, n)).expect("n <= u32::MAX");
        }

        // Both samples, in one pass over the rows. Rows come in ascending order, so `sa_samples`
        // is filled in the order `rank(B, i)` will index it.
        let mut marks = vec![0u64; n.div_ceil(64)];
        let mut sa_samples: Vec<u32> = Vec::with_capacity(n / step + 1);
        let mut isa_samples = vec![0u32; n.div_ceil(step)];
        #[allow(
            clippy::cast_possible_truncation,
            reason = "rows and text positions are below n, and try_encode_with_sa refuses n > u32::MAX"
        )]
        for (row, &pos) in sa.iter().enumerate() {
            let pos = pos as usize;
            if pos % step == 0 {
                marks[row / 64] |= 1u64 << (row % 64);
                sa_samples.push(pos as u32);
                isa_samples[pos / step] = row as u32;
            }
        }

        Ok(FmIndex {
            occ,
            c,
            marks: Rrr::new(&marks, n),
            sa_samples: Packed::new(&sa_samples, n),
            isa_samples: Packed::new(&isa_samples, n),
            sample,
        })
    }

    /// The index written out as [`FmParts`]. Behind the `unchecked` feature.
    #[cfg(feature = "unchecked")]
    #[must_use]
    pub fn to_parts(&self) -> FmParts {
        #[allow(
            clippy::cast_possible_truncation,
            reason = "a sample is a row or text position, below n <= u32::MAX"
        )]
        let packed = |p: &Packed| (0..p.len).map(|k| p.get(k) as u32).collect();
        FmParts {
            last: self.column(),
            c: self.c.clone(),
            marks: (0..self.marks.len()).map(|i| self.marks.get(i)).collect(),
            sa_samples: packed(&self.sa_samples),
            isa_samples: packed(&self.isa_samples),
            sample: self.sample,
        }
    }

    fn column(&self) -> Vec<u8> {
        (0..self.text_len())
            .map(|i| self.occ.symbol_and_occ(i).0)
            .collect()
    }

    /// The column, and LF over it with `C` recomputed from the column (the Lean's `lf`).
    fn column_and_lf(&self) -> (Vec<u8>, Vec<usize>) {
        let n = self.text_len();
        let reads: Vec<(u8, usize)> = (0..n).map(|i| self.occ.symbol_and_occ(i)).collect();
        let mut below = [0usize; 256];
        for &(symbol, _) in &reads {
            below[usize::from(symbol)] += 1;
        }
        let mut sum = 0;
        for slot in &mut below {
            (*slot, sum) = (sum, sum + *slot);
        }
        let lf = reads
            .iter()
            .map(|&(symbol, before)| below[usize::from(symbol)] + before)
            .collect();
        (reads.into_iter().map(|(symbol, _)| symbol).collect(), lf)
    }

    fn kept_count(&self) -> usize {
        let k = self.sample as usize;
        if k == 0 {
            0
        } else {
            self.text_len().div_ceil(k)
        }
    }

    /// Box invariant 2 (Lean `PositionsKept`): at fixed intervals along the text, a row keeps its
    /// own position, so every match is a short walk from one. Its three parts, in the Lean's
    /// order: the kept positions are `{0, k, 2k, …}` below `n`, each once; one mark per row and
    /// one kept position per mark; each marked row keeps its own position.
    #[must_use]
    pub fn is_positions_kept(&self) -> bool {
        self.kept_evenly() && self.kept_rows_flagged() && self.kept_positions_correct()
    }

    /// Invariant 2's first part: the suffix-array samples are exactly `{0, k, 2k, …}` below `n`,
    /// each once, in any order (none at rate `0`, as the Lean's `(n + k - 1) / k` is `0` there).
    fn kept_evenly(&self) -> bool {
        let k = self.sample as usize;
        let m = self.kept_count();
        if self.sa_samples.len != m {
            return false;
        }
        let mut seen = vec![false; m];
        (0..m).all(|i| {
            let Some(v) = self.sa_samples.try_get(i) else {
                return false;
            };
            v % k == 0
                && seen
                    .get_mut(v / k)
                    .is_some_and(|s| !std::mem::replace(s, true))
        })
    }

    /// Invariant 2's second part: one mark per row, and as many marks as suffix-array samples.
    fn kept_rows_flagged(&self) -> bool {
        let n = self.text_len();
        self.marks.len() == n && self.marks.rank(n) == self.sa_samples.len
    }

    /// Invariant 2's third part (Lean `KeptPositionsCorrect`): each marked row's sample is its own
    /// text position, and exactly the rows of multiples of `k` are marked.
    fn kept_positions_correct(&self) -> bool {
        let (column, lf) = self.column_and_lf();
        let n = column.len();
        let Some(mut row) = column.iter().position(|&c| c == bwt::SENTINEL) else {
            return true;
        };
        let k = self.sample as usize;
        for j in 0..n {
            let pos = (n - j) % n;
            // The Lean's `p % 0` is `p`.
            let kept = pos.checked_rem(k).unwrap_or(pos) == 0;
            if row >= self.marks.len() || self.marks.get(row) != kept {
                return false;
            }
            if kept && self.sa_samples.try_get(self.marks.rank(row)) != Some(pos) {
                return false;
            }
            row = lf[row];
        }
        true
    }

    /// Not in the box (Lean `SmallerLettersCounted`): `c[d]` counts the column's symbols
    /// below its `d`-th smallest, one entry per symbol.
    #[must_use]
    pub fn is_smaller_letters_counted(&self) -> bool {
        let mut count = [0usize; 256];
        for symbol in self.column() {
            count[usize::from(symbol)] += 1;
        }
        let mut want = Vec::new();
        let mut below = 0usize;
        for &k in &count {
            if k > 0 {
                want.push(below);
                below += k;
            }
        }
        self.c.len() == want.len() && self.c.iter().zip(&want).all(|(&c, &w)| c as usize == w)
    }

    /// The transform's box assumption, one `$` (Lean `SentinelOnce`): the sentinel stands in the
    /// column once.
    #[must_use]
    pub fn is_sentinel_once(&self) -> bool {
        self.column()
            .iter()
            .filter(|&&b| b == bwt::SENTINEL)
            .count()
            == 1
    }

    /// Not in the box (Lean `WalkVisitsEveryRow`): `n` LF steps from row 0 visit every row
    /// once and return to row 0.
    #[must_use]
    pub fn is_walk_visits_every_row(&self) -> bool {
        let (_, lf) = self.column_and_lf();
        let n = lf.len();
        if n == 0 {
            return true;
        }
        let mut seen = vec![false; n];
        let mut row = 0;
        for _ in 0..n {
            match seen.get_mut(row) {
                Some(s) if !*s => *s = true,
                _ => return false,
            }
            row = lf[row];
        }
        row == 0
    }

    /// Not in the box (Lean `KeptRowsListed`): `⌈n/k⌉` inverse samples, and each `isa[j]`
    /// is a marked row whose sample is `j·k`.
    #[must_use]
    pub fn is_kept_rows_listed(&self) -> bool {
        let (n, k) = (self.text_len(), self.sample as usize);
        self.isa_samples.len == self.kept_count()
            && (0..self.isa_samples.len).all(|j| {
                self.isa_samples.try_get(j).is_some_and(|row| {
                    row < n
                        && row < self.marks.len()
                        && self.marks.get(row)
                        && self.sa_samples.try_get(self.marks.rank(row)) == Some(j * k)
                })
            })
    }

    /// Not in the box (Lean `LettersAreBytes`): every letter of the column is a byte. Held
    /// by the type (the column stores `u8`), so always `true`.
    #[must_use]
    pub fn is_letters_are_bytes(&self) -> bool {
        self.column().iter().all(|&b| usize::from(b) < 256)
    }

    /// Not in the box (Lean `RateAtLeastOne`): the interval between kept positions is at
    /// least one.
    #[must_use]
    pub fn is_rate_at_least_one(&self) -> bool {
        self.sample > 0
    }

    /// All seven pieces above, the Lean `FMIndex.Valid`; never panics on a corrupted index.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`FmIndex::is_valid`] with the first failed piece named, in its order.
    ///
    /// # Errors
    ///
    /// The first failed piece's name, e.g. `"invariant 2 (positions_kept)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        // Box invariant 1 holds of backward search's running stretch, not of the stored index:
        // `backward_search::check_valid` checks it on each step's state.
        let pieces = [
            (
                Self::is_positions_kept as fn(&Self) -> bool,
                "invariant 2 (positions_kept)",
            ),
            (Self::is_sentinel_once, "assumption (sentinel_once)"),
            (
                Self::is_smaller_letters_counted,
                "not in the box (smaller_letters_counted)",
            ),
            (
                Self::is_walk_visits_every_row,
                "not in the box (walk_visits_every_row)",
            ),
            (
                Self::is_kept_rows_listed,
                "not in the box (kept_rows_listed)",
            ),
            (
                Self::is_letters_are_bytes,
                "not in the box (letters_are_bytes)",
            ),
            (
                Self::is_rate_at_least_one,
                "not in the box (rate_at_least_one)",
            ),
        ];
        match pieces.iter().find(|(holds, _)| !holds(self)) {
            Some(&(_, name)) => Err(name),
            None => Ok(()),
        }
    }

    /// Length of the indexed text, sentinel included.
    #[must_use]
    pub fn text_len(&self) -> usize {
        self.occ.len()
    }

    /// Bytes this index occupies (not counting the alphabet's fixed 256-entry map).
    #[must_use]
    pub fn size_bytes(&self) -> usize {
        self.occ.size_bytes()
            + self.c.len() * size_of::<u32>()
            + self.marks.size_bytes()
            + self.sa_samples.size_bytes()
            + self.isa_samples.size_bytes()
    }

    /// `(L[row], LF(row))`, `LF(i) = C[L[i]] + occ(L[i], i)`: the row one text position earlier.
    #[inline]
    fn lf(&self, row: usize) -> (u8, usize) {
        #[cfg(test)]
        LF_STEPS.with(|n| n.set(n.get() + 1));
        let (symbol, dense, rank) = self.occ.symbol_dense_and_occ(row);
        (symbol, self.c[dense] as usize + rank)
    }

    /// The rows `[lo, hi)` whose suffix starts with `pat`, or `None`, for the answers about the
    /// text without its sentinel: `None` for a pattern holding one, which that text cannot hold,
    /// else backward search. `O(m)`.
    fn interval(&self, pat: &[u8]) -> Option<(usize, usize)> {
        if pat.contains(&bwt::SENTINEL) {
            return None;
        }
        self.interval_observed(pat, |_| {})
    }

    /// Backward search over the stored text, its sentinel included, reporting each step.
    fn interval_observed(
        &self,
        pat: &[u8],
        mut seen: impl FnMut(Option<(usize, usize)>),
    ) -> Option<(usize, usize)> {
        let n = self.text_len();
        if pat.len() > n {
            return None;
        }
        // A sentinel before the end would match a rotation that wraps, not a substring.
        if let Some((_, before_last)) = pat.split_last() {
            if before_last.contains(&bwt::SENTINEL) {
                return None;
            }
        }
        let (mut lo, mut hi) = (0usize, n);
        for &symbol in pat.iter().rev() {
            let Some(dense) = self.occ.alphabet().index_of(symbol) else {
                seen(None);
                return None;
            };
            let base = self.c[dense] as usize;
            lo = base + self.occ.occ(symbol, lo);
            hi = base + self.occ.occ(symbol, hi);
            seen(Some((lo, hi)));
            if lo >= hi {
                return None;
            }
        }
        Some((lo, hi))
    }

    /// The stretch of rows after each symbol backward search read on `pat`, right to left, up to
    /// the one that emptied it (`None` for a symbol outside the alphabet), over the stored text,
    /// its sentinel included. Behind the `unchecked` feature.
    #[cfg(any(test, feature = "unchecked"))]
    #[must_use]
    pub fn interval_steps(&self, pat: &[u8]) -> Vec<Option<(usize, usize)>> {
        let mut steps = Vec::new();
        let _ = self.interval_observed(pat, |step| steps.push(step));
        steps
    }

    /// Occurrences of `pat` in the text without its sentinel (the empty pattern: `n`, every
    /// position `0..n - 1` of that text, its end included; a pattern holding the sentinel: `0`).
    /// `O(m)`. Lean: `FMIndex.count_of_valid`, `fmCount_eq`.
    #[must_use]
    pub fn count(&self, pat: &[u8]) -> usize {
        self.interval(pat).map_or(0, |(lo, hi)| hi - lo)
    }

    /// Text position of `row`: walk LF to a marked row, read its sample. Fewer than
    /// `min(sample, n)` steps; a corrupt index panics. Lean: `locateSampled_eq`.
    fn position_of(&self, row: usize) -> u32 {
        #[cfg(test)]
        LOCATED.with(|n| n.set(n.get() + 1));
        #[allow(
            clippy::cast_possible_truncation,
            reason = "text_len is at most u32::MAX, which try_encode_with_sa enforces"
        )]
        let limit = self.sample.min(self.text_len() as u32);
        let mut row = row;
        #[allow(
            clippy::cast_possible_truncation,
            reason = "a sample is a text position below n <= u32::MAX, and steps < sample keeps the sum below n"
        )]
        for steps in 0..limit {
            let (marked, before) = self.marks.access_rank(row);
            if marked {
                return self.sa_samples.get(before) as u32 + steps;
            }
            row = self.lf(row).1;
        }
        panic!(
            "fm_index: an LF walk met no sampled row in {limit} steps; the index is corrupt \
             (every walk reaches text position 0, which is always sampled)"
        )
    }

    /// Start positions of every occurrence of `pat` in the text without its sentinel, in suffix
    /// order. `O(m + occ · sample)`. Lean: `FMIndex.locate_perm_of_valid`, `fmLocate_perm`.
    #[must_use]
    pub fn locate(&self, pat: &[u8]) -> Vec<u32> {
        self.locate_iter(pat).collect()
    }

    /// [`Self::locate`]'s positions lazily: `O(m)` now, fewer than `sample` LF steps per position
    /// drawn.
    pub fn locate_iter(&self, pat: &[u8]) -> impl Iterator<Item = u32> + '_ {
        let (lo, hi) = self.interval(pat).unwrap_or((0, 0));
        (lo..hi).map(|row| self.position_of(row))
    }

    /// The `len` text bytes starting at `from`, by an LF walk back from the next sampled
    /// position. `O(len + sample)`. Lean: `fmExtract_eq`.
    ///
    /// # Panics
    ///
    /// If `from + len` exceeds the text length.
    #[must_use]
    pub fn extract(&self, from: u32, len: u32) -> Vec<u8> {
        let n = self.text_len();
        let (from, len) = (from as usize, len as usize);
        assert!(
            from + len <= n,
            "fm_index::extract: range {from}..{} runs past the text's {n} bytes",
            from + len
        );
        if len == 0 {
            return Vec::new();
        }

        // Past the last real sample, start from position n (0 read cyclically).
        let step = self.sample as usize;
        let k = (from + len).div_ceil(step);
        let (start, mut row) = if k * step >= n {
            (n, self.isa_samples.get(0))
        } else {
            (k * step, self.isa_samples.get(k))
        };

        debug_assert!(
            start - (from + len) < step,
            "extract discarded {} characters at rate {step}",
            start - (from + len)
        );
        let mut out = Vec::with_capacity(start - from);
        for _ in 0..start - from {
            let (symbol, next) = self.lf(row);
            out.push(symbol);
            row = next;
        }
        out.reverse();
        out.truncate(len);
        out
    }
}

impl<O: Occ> std::fmt::Debug for FmIndex<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FmIndex")
            .field("text_len", &self.text_len())
            .field("sample", &self.sample)
            .field("size_bytes", &self.size_bytes())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[path = "unit_tests/fm_index.rs"]
mod tests;
