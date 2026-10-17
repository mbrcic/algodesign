// SPDX-License-Identifier: Apache-2.0
//! The FM-index's size against its query latency, and Rabin–Karp against the naive scan.
//!
//! **The sweep.** Every pair of chunk length (half, once and twice Kärkkäinen--Puglisi's
//! `σ ⌈log2(n + 1)⌉²`, the default of
//! [`FmIndex::build`](algodesign::strings::fm_index::FmIndex::build)) and sampling rate `l`
//! {16, 32, 64} builds one index. Each is timed on `count` and
//! [`locate`](algodesign::strings::fm_index::FmIndex::locate) at pattern lengths 4, 8 and 16, and
//! on [`extract`](algodesign::strings::fm_index::FmIndex::extract) of 100-byte ranges, and reports
//! its `size_bytes()`. Shorter chunks mean more tables and a closer fit to the text; a sparser
//! sample means a smaller index and a longer LF walk per `locate` and `extract`.
//!
//! **Cold queries.** Every pattern in a set is distinct: 8192 per length for `count`, so the few
//! chunk-tree nodes a backward search touches are not still in cache from the last time it was
//! asked; 32 for `locate`, whose walks touch more of the index than any cache holds; 2048
//! pseudo-random ranges for `extract`.
//!
//! **The corpus.** Run `scripts/fetch_corpus.sh` first: it fetches ten works of English prose
//! from Project Gutenberg into `corpus/corpus.txt`, licence boilerplate cut. Without that file
//! the benchmark falls back to generated text and says so in its first line and in every
//! summary table; generated text has its generator's alphabet and entropy, so its sizes are not
//! the corpus's. `STRINGS_CORPUS` names another file to index.
//!
//! **The scans.** Before the sweep, the `scan` groups time Rabin–Karp
//! ([`rabin_karp::search_seeded`], the prime drawn from a fixed seed) against the naive scan
//! ([`naive::search`], `O(nm)`), in bytes of text per second: on the corpus at `Elizabeth`,
//! `whale` and `the quick brown fox` and a 64- and a 256-byte quote; on 4 MiB of random bytes at
//! `m` 4, 16, 64 and 256; and on `a^n` against `a^(m-1) b`, the naive scan's worst case. Each
//! case prints its modulus. `scan/reducer` times the two reductions: `search_with` at base 256
//! takes the table, at base 257 Möller–Granlund's. `STRINGS_SCAN_ONLY=1` stops after the scans.
//!
//! **The dictionaries and the suffix array.** After the scans, `words/trie` and `words/patricia`
//! insert the corpus's distinct words (split at ASCII whitespace, at most [`WORDS`]) into an empty
//! [`Trie`] and an empty [`Patricia`] and look every one up again, beside `words/btreemap`, the
//! standard library's ordered map on the same words; `suffix_array/build` times
//! [`suffix_array::suffix_array`] on the first [`SA_BYTES`] bytes of the corpus.
//! `STRINGS_STRUCTURES_ONLY=1` runs these alone.
//!
//! Run: `cargo bench -p algodesign --bench strings`, after `scripts/fetch_corpus.sh`.

use std::time::{Duration, Instant};

use algodesign::strings::chunked_wavelet::default_chunk;
use algodesign::strings::fm_index::FmIndex;
use algodesign::strings::fm_index::SAMPLE;
use algodesign::strings::naive;
use algodesign::strings::patricia::Patricia;
use algodesign::strings::rabin_karp;
use algodesign::strings::suffix_array;
use algodesign::strings::trie::Trie;
use criterion::{BenchmarkId, Criterion, Throughput};

/// Sampling rates swept, around the library's [`SAMPLE`].
const RATES: [u32; 3] = [SAMPLE / 2, SAMPLE, SAMPLE * 2];
/// Pattern lengths swept.
const PATTERN_LENGTHS: [usize; 3] = [4, 8, 16];
/// Distinct patterns per length for `count`. Each benchmark iteration runs the whole set, so
/// criterion's `time` line is the cost of all of them; the `thrpt` line beside it is the one to
/// read, since [`Throughput::Elements`] divides by the queries the set did.
const COUNT_PATTERNS: usize = 8192;
/// Distinct patterns per length for `locate`, whose `thrpt` line divides by the occurrences the
/// set located.
const LOCATE_PATTERNS: usize = 32;
/// Ranges per `extract` pass, and the length of each.
const EXTRACT_RANGES: usize = 2048;
/// See [`EXTRACT_RANGES`].
const EXTRACT_LEN: u32 = 100;
/// Size of the generated fallback text, when there is no corpus. Small enough that a machine
/// with no network still finishes the sweep; big enough that the index is not overhead.
const FALLBACK_BYTES: usize = 2 << 20;

/// Where the indexed bytes came from. Printed on every table, because a number measured on
/// generated text and a number measured on English prose are not the same number.
enum Provenance {
    /// `corpus/corpus.txt`, from `scripts/fetch_corpus.sh`.
    Corpus(String),
    /// Generated here, because that file was absent.
    Generated,
}

impl Provenance {
    fn banner(&self) -> String {
        match self {
            Provenance::Corpus(path) => format!("REAL CORPUS: {path}"),
            Provenance::Generated => format!(
                "FALLBACK: GENERATED TEXT ({FALLBACK_BYTES} bytes) -- no corpus/corpus.txt. \
                 These numbers are NOT corpus numbers; run scripts/fetch_corpus.sh."
            ),
        }
    }
}

/// One cell of the sweep, filled as its index is built.
struct Cell {
    chunk: usize,
    rate: u32,
    size_bytes: usize,
    build: Duration,
}

/// The text to index, sentinel *not* yet appended.
///
/// `STRINGS_CORPUS` overrides the path, for measuring some other corpus without editing this file.
fn load_text() -> (Vec<u8>, Provenance) {
    let path = std::env::var("STRINGS_CORPUS").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../../corpus/corpus.txt").to_string()
    });
    match std::fs::read(&path) {
        Ok(mut bytes) if !bytes.is_empty() => {
            // `bwt::encode` reserves 0x00 for its sentinel and rejects an interior one. The
            // fetcher strips NULs; a hand-supplied `STRINGS_CORPUS` might not.
            bytes.retain(|&b| b != 0);
            (bytes, Provenance::Corpus(path))
        }
        _ => (generated_text(FALLBACK_BYTES), Provenance::Generated),
    }
}

/// Fallback text: words drawn from a small fixed vocabulary, deterministically.
///
/// It is word-shaped rather than random bytes so that `count` and `locate` face the repetition
/// structure they face in prose, but its alphabet is a couple of dozen symbols and its entropy
/// is its generator's. Nothing measured on it may be reported as a measurement of English.
fn generated_text(bytes: usize) -> Vec<u8> {
    const VOCAB: [&str; 16] = [
        "the", "quick", "brown", "fox", "jumps", "over", "lazy", "dog", "pack", "my", "box",
        "with", "five", "dozen", "liquor", "jugs",
    ];
    let mut rng = Rng::new(0x5EED_1234_5678_9ABC);
    let mut out = Vec::with_capacity(bytes + 16);
    while out.len() < bytes {
        out.extend_from_slice(VOCAB[rng.below(VOCAB.len() as u64) as usize].as_bytes());
        out.push(b' ');
    }
    out.truncate(bytes);
    out
}

/// xorshift64*, so the pattern set and the fallback text are the same on every machine.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed | 1)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// `how_many` *distinct* substrings of `text` of length `len`, taken at uniformly random
/// positions, in the order they were drawn.
///
/// Uniform *positions*, not uniform patterns: a substring is therefore drawn in proportion to
/// how often it occurs, so common ones are over-represented. That is deliberate and it is the
/// harder case for `locate`, whose cost is per occurrence -- a pattern set of rarities would
/// make the sampling rate look free. A repeat is drawn again rather than kept, because a
/// pattern asked twice is answered from cache the second time.
///
/// The draws are capped at a hundred per pattern wanted, so a text with fewer distinct
/// substrings than that -- the generated fallback's sixteen words have far fewer than 8192
/// four-byte ones -- ends with a smaller set rather than a loop that never does. The sizes
/// actually drawn are printed before the sweep.
fn patterns(text: &[u8], len: usize, how_many: usize) -> Vec<Vec<u8>> {
    let mut rng = Rng::new(0xC0FF_EE00_0000_0000 ^ len as u64);
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::with_capacity(how_many);
    for _ in 0..100 * how_many {
        if out.len() == how_many {
            break;
        }
        let at = rng.below((text.len() - len) as u64) as usize;
        if seen.insert(&text[at..at + len]) {
            out.push(text[at..at + len].to_vec());
        }
    }
    out
}

/// The pattern sets one length is measured with: `(len, count's set, locate's set)`.
type PatternSets = (usize, Vec<Vec<u8>>, Vec<Vec<u8>>);
/// One [`PatternSets`] per length.
type Sets = [PatternSets];

/// Build one index per sampling rate at one chunk length, benchmarking each as it is built.
fn sweep(c: &mut Criterion, text: &[u8], chunk: usize, sets: &Sets, cells: &mut Vec<Cell>) {
    let n = text.len() as u32;
    let mut rng = Rng::new(0xE17A_C700_0000_0000);
    let starts: Vec<u32> = (0..EXTRACT_RANGES)
        .map(|_| rng.below(u64::from(n - EXTRACT_LEN)) as u32)
        .collect();
    for rate in RATES {
        let start = Instant::now();
        let index = FmIndex::build_with_chunk(text, rate, chunk);
        let build = start.elapsed();
        let cell = Cell {
            chunk,
            rate,
            size_bytes: index.size_bytes(),
            build,
        };
        println!(
            "\nbuilt: chunk = {chunk}, sample = {rate} -- {} bytes ({:.3} n) in {:.2} s",
            cell.size_bytes,
            cell.size_bytes as f64 / index.text_len() as f64,
            build.as_secs_f64()
        );
        cells.push(cell);

        let param = format!("chunk={chunk},l={rate}");

        let mut group = c.benchmark_group("count");
        // A pass over 8192 patterns takes milliseconds, so fewer samples still fill the time.
        group.sample_size(20);
        group.measurement_time(Duration::from_secs(3));
        for (len, set, _) in sets {
            // One element per query: `count` answers in the pattern's length and nothing else,
            // so per-query is the number that means something.
            group.throughput(Throughput::Elements(set.len() as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("m={len}"), &param),
                set,
                |b, set| {
                    b.iter(|| {
                        let mut total = 0usize;
                        for pat in set {
                            total += index.count(std::hint::black_box(pat));
                        }
                        total
                    });
                },
            );
        }
        group.finish();

        let mut group = c.benchmark_group("locate");
        group.sample_size(10);
        group.warm_up_time(Duration::from_millis(500));
        group.measurement_time(Duration::from_secs(3));
        for (len, _, set) in sets {
            // One element per *occurrence*: `locate` walks the LF map once per hit, so the
            // sampling rate's cost shows up per occurrence, and per query it is swamped by how
            // common the pattern happens to be.
            let occurrences: u64 = set.iter().map(|p| index.count(p) as u64).sum();
            group.throughput(Throughput::Elements(occurrences.max(1)));
            group.bench_with_input(
                BenchmarkId::new(format!("m={len}"), &param),
                set,
                |b, set| {
                    b.iter(|| {
                        let mut total = 0usize;
                        for pat in set {
                            total += index.locate(std::hint::black_box(pat)).len();
                        }
                        total
                    });
                },
            );
        }
        group.finish();

        let mut group = c.benchmark_group("extract");
        group.sample_size(10);
        group.measurement_time(Duration::from_secs(3));
        // One element per range asked.
        group.throughput(Throughput::Elements(starts.len() as u64));
        group.bench_with_input(
            BenchmarkId::new(format!("len={EXTRACT_LEN}"), &param),
            &starts,
            |b, starts| {
                b.iter(|| {
                    let mut total = 0usize;
                    for &from in starts {
                        total += index.extract(std::hint::black_box(from), EXTRACT_LEN).len();
                    }
                    total
                });
            },
        );
        group.finish();
    }
}

/// The seed every `scan` case draws its prime from.
const SCAN_SEED: u64 = 0x5CA1_AB1E_0000_0001;
/// Bytes of the random and the adversarial scan texts.
const SCAN_RANDOM_BYTES: usize = 4 << 20;
/// See [`SCAN_RANDOM_BYTES`]: `a^n` is quadratic for the naive scan, so it is kept shorter.
const SCAN_ADVERSARIAL_BYTES: usize = 1 << 20;
/// Pattern lengths for the random and adversarial scans.
const SCAN_LENGTHS: [usize; 4] = [4, 16, 64, 256];

/// One `scan` group: Rabin–Karp and the naive scan over `text`, for each `(label, pattern)`.
fn scan_group(c: &mut Criterion, group: &str, text: &[u8], cases: &[(String, Vec<u8>)]) {
    let mut group = c.benchmark_group(group);
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));
    group.measurement_time(Duration::from_secs(2));
    group.throughput(Throughput::Bytes(text.len() as u64));
    for (label, pat) in cases {
        let modulus =
            rabin_karp::random_prime_below(rabin_karp::threshold(text.len(), pat.len()), SCAN_SEED);
        let hits = naive::search(text, pat).len();
        assert_eq!(rabin_karp::search_seeded(text, pat, SCAN_SEED).len(), hits);
        println!(
            "scan {label}: m = {}, {hits} hits, drawn modulus {modulus} (2^{:.1})",
            pat.len(),
            (modulus as f64).log2()
        );
        group.bench_with_input(BenchmarkId::new("rabin_karp", label), pat, |b, pat| {
            b.iter(|| rabin_karp::search_seeded(text, std::hint::black_box(pat), SCAN_SEED).len());
        });
        group.bench_with_input(BenchmarkId::new("naive", label), pat, |b, pat| {
            b.iter(|| naive::search(text, std::hint::black_box(pat)).len());
        });
    }
    group.finish();
}

/// The three `scan` groups: the corpus, random bytes, and the naive scan's worst case.
fn scans(c: &mut Criterion, body: &[u8]) {
    let mut corpus_cases: Vec<(String, Vec<u8>)> = ["Elizabeth", "whale", "the quick brown fox"]
        .iter()
        .map(|p| (format!("{p:?}"), p.as_bytes().to_vec()))
        .collect();
    for len in [64, 256] {
        let at = body.len() / 3;
        corpus_cases.push((format!("quote{len}"), body[at..at + len].to_vec()));
    }
    scan_group(c, "scan/corpus", body, &corpus_cases);

    let mut group = c.benchmark_group("scan/reducer");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));
    group.measurement_time(Duration::from_secs(2));
    group.throughput(Throughput::Bytes(body.len() as u64));
    for (label, pat) in &corpus_cases[..3] {
        let modulus =
            rabin_karp::random_prime_below(rabin_karp::threshold(body.len(), pat.len()), SCAN_SEED);
        for base in [256u64, 257] {
            group.bench_with_input(
                BenchmarkId::new(format!("base={base}"), label),
                pat,
                |b, pat| {
                    b.iter(|| {
                        rabin_karp::search_with(body, std::hint::black_box(pat), base, modulus)
                            .len()
                    });
                },
            );
        }
    }
    group.finish();

    let mut rng = Rng::new(0x0BAD_5EED_0000_0000);
    let random: Vec<u8> = (0..SCAN_RANDOM_BYTES)
        .map(|_| rng.next_u64() as u8)
        .collect();
    let random_cases: Vec<(String, Vec<u8>)> = SCAN_LENGTHS
        .iter()
        .map(|&m| {
            (
                format!("m={m}"),
                random[random.len() / 2..random.len() / 2 + m].to_vec(),
            )
        })
        .collect();
    scan_group(c, "scan/random", &random, &random_cases);

    let adversarial = vec![b'a'; SCAN_ADVERSARIAL_BYTES];
    let adversarial_cases: Vec<(String, Vec<u8>)> = SCAN_LENGTHS
        .iter()
        .map(|&m| {
            let mut pat = vec![b'a'; m - 1];
            pat.push(b'b');
            (format!("m={m}"), pat)
        })
        .collect();
    scan_group(c, "scan/a^n", &adversarial, &adversarial_cases);
}

/// At most this many distinct words go into each dictionary.
const WORDS: usize = 100_000;
/// Bytes of the corpus the suffix-array build sorts.
const SA_BYTES: usize = 1 << 20;

/// The `words` groups, a trie, a Patricia tree and a `BTreeMap` built and queried on the same
/// distinct words, and the `suffix_array` group.
fn structures(c: &mut Criterion, body: &[u8]) {
    let mut seen = std::collections::BTreeSet::new();
    let words: Vec<&[u8]> = body
        .split(u8::is_ascii_whitespace)
        .filter(|w| !w.is_empty() && seen.insert(*w))
        .take(WORDS)
        .collect();
    println!("words: {} distinct words", words.len());

    let mut group = c.benchmark_group("words");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));
    group.measurement_time(Duration::from_secs(3));
    group.throughput(Throughput::Elements(words.len() as u64));
    group.bench_function("trie/insert", |b| {
        b.iter(|| {
            let mut t = Trie::new();
            for (i, w) in words.iter().enumerate() {
                t.insert(w, i);
            }
            t.len()
        });
    });
    group.bench_function("patricia/insert", |b| {
        b.iter(|| {
            let mut p = Patricia::new();
            for (i, w) in words.iter().enumerate() {
                p.insert(w, i);
            }
            p.len()
        });
    });
    group.bench_function("btreemap/insert", |b| {
        b.iter(|| {
            let mut m = std::collections::BTreeMap::new();
            for (i, w) in words.iter().enumerate() {
                m.insert(w.to_vec(), i);
            }
            m.len()
        });
    });
    let mut trie = Trie::new();
    let mut patricia = Patricia::new();
    let mut map = std::collections::BTreeMap::new();
    for (i, w) in words.iter().enumerate() {
        trie.insert(w, i);
        patricia.insert(w, i);
        map.insert(w.to_vec(), i);
    }
    group.bench_function("trie/get", |b| {
        b.iter(|| {
            words
                .iter()
                .filter_map(|w| trie.get(std::hint::black_box(w)))
                .count()
        });
    });
    group.bench_function("patricia/get", |b| {
        b.iter(|| {
            words
                .iter()
                .filter_map(|w| patricia.get(std::hint::black_box(w)))
                .count()
        });
    });
    group.bench_function("btreemap/get", |b| {
        b.iter(|| {
            words
                .iter()
                .filter_map(|w| map.get(std::hint::black_box(*w)))
                .count()
        });
    });
    group.finish();

    let text = &body[..body.len().min(SA_BYTES)];
    let mut group = c.benchmark_group("suffix_array");
    group.sample_size(10);
    group.warm_up_time(Duration::from_millis(500));
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Bytes(text.len() as u64));
    group.bench_function("build", |b| {
        b.iter(|| suffix_array::suffix_array(std::hint::black_box(text)).len());
    });
    group.finish();
}

/// Distinct byte values and zeroth-order entropy of the bytes actually indexed.
fn statistics(bytes: &[u8]) -> (usize, f64) {
    let mut counts = [0usize; 256];
    for &b in bytes {
        counts[b as usize] += 1;
    }
    let n = bytes.len() as f64;
    let sigma = counts.iter().filter(|&&c| c > 0).count();
    let h0 = counts
        .iter()
        .filter(|&&c| c > 0)
        .map(|&c| {
            let p = c as f64 / n;
            -p * p.log2()
        })
        .sum();
    (sigma, h0)
}

fn main() {
    let (mut text, provenance) = load_text();
    text.push(0); // the sentinel `bwt::encode` requires; it is part of what gets indexed
    let n = text.len();
    let (sigma, h0) = statistics(&text);

    let header = format!(
        "\n=== Strings sampling sweep ===\n{}\n\
         indexed: {n} bytes including the sentinel, sigma_eff = {sigma}, H_0 = {h0:.3} bits/byte\n\
         library: sample = {SAMPLE}; {COUNT_PATTERNS} distinct patterns per length for count and \
         {LOCATE_PATTERNS} for locate, drawn at uniformly random positions; {EXTRACT_RANGES} \
         ranges of {EXTRACT_LEN} bytes for extract\n",
        provenance.banner()
    );
    println!("{header}");

    let sets: Vec<PatternSets> = PATTERN_LENGTHS
        .iter()
        .map(|&len| {
            let body = &text[..n - 1];
            (
                len,
                patterns(body, len, COUNT_PATTERNS),
                patterns(body, len, LOCATE_PATTERNS),
            )
        })
        .collect();
    for (len, count_set, locate_set) in &sets {
        println!(
            "m = {len}: {} distinct patterns for count, {} for locate",
            count_set.len(),
            locate_set.len()
        );
    }

    let mut criterion = Criterion::default().configure_from_args();
    if std::env::var_os("STRINGS_STRUCTURES_ONLY").is_some() {
        structures(&mut criterion, &text[..n - 1]);
        criterion.final_summary();
        return;
    }
    scans(&mut criterion, &text[..n - 1]);
    if std::env::var_os("STRINGS_SCAN_ONLY").is_some() {
        criterion.final_summary();
        return;
    }
    structures(&mut criterion, &text[..n - 1]);

    // The length `FmIndex::build` uses, over the last column's alphabet, which is the text's.
    let chunk = default_chunk(n, sigma);
    let mut cells: Vec<Cell> = Vec::new();
    for len in [chunk / 2, chunk, chunk * 2] {
        sweep(&mut criterion, &text, len.max(1), &sets, &mut cells);
    }
    criterion.final_summary();

    // The size half of the trade, gathered into one table. Criterion prints the time half.
    println!("{header}");
    println!("| chunk | sample | index bytes | × n | build s |");
    println!("|---:|---:|---:|---:|---:|");
    for cell in &cells {
        println!(
            "| {} | {} | {} | {:.3} | {:.1} |",
            cell.chunk,
            cell.rate,
            cell.size_bytes,
            cell.size_bytes as f64 / n as f64,
            cell.build.as_secs_f64()
        );
    }
    println!(
        "\nfor comparison: the text alone is {n} bytes (1.000 n), and text plus a u32 suffix \
         array is {} bytes (5.000 n).",
        5 * n
    );
}
