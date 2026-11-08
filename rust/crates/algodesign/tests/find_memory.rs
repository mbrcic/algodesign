// SPDX-License-Identifier: Apache-2.0
//! `Corpus::find` holds memory in quotes, not in hits.
//!
//! A common fragment occurs thousands of times in a handful of records. `find` spends each hit
//! on one `record_of` as the index resolves it and keeps only the record ids, so what it
//! allocates is the quotes it returns and a small set of ids. Locating every hit into a vector
//! before deduplicating answers identically and holds four bytes per hit; so does collecting one
//! id per hit and sorting that. Only a count of the bytes allocated sees the difference.
//!
//! `harness = false` (see `Cargo.toml`): the allocator's counts are global to the process, so
//! this runs as a plain `main` on one thread, and a failed check panics.

use std::alloc::System;

use algodesign::strings::records::Corpus;
use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};

#[global_allocator]
static GLOBAL: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

fn main() {
    // Three records of 20 000 `a`s, every byte a hit for `a`, among records that hold none.
    let dense = vec![b'a'; 20_000];
    let sparse = b"the quick brown fox jumps over the lazy dog".to_vec();
    let records: Vec<&[u8]> = vec![&sparse, &dense, &sparse, &dense, &sparse, &dense, &sparse];
    let corpus = Corpus::build(&records);

    let region = Region::new(GLOBAL);
    let found = corpus.find(b"a");
    let stats = region.change();

    let hits = 3 * dense.len() + 4 * 3; // `lazy` and `a` hold three more between them
    let quoted: usize = found.iter().map(|q| q.text().len()).sum();
    assert_eq!(found.len(), 7);
    let reallocated = usize::try_from(stats.bytes_reallocated.max(0)).expect("non-negative");
    let allocated = stats.bytes_allocated + reallocated;
    println!(
        "find(\"a\"): {} quotes, {quoted} bytes quoted, {hits} hits; {allocated} bytes \
         allocated in {} allocations and {} reallocations",
        found.len(),
        stats.allocations,
        stats.reallocations
    );
    // The quotes, plus each extraction's walk from the next sampled position (at most one text
    // sample, 32 bytes, per quote), plus the id set and the output vector: well under twice
    // what is returned. Four bytes per hit is 240 000 here, and a vector of them grown by
    // doubling allocates more again.
    let bound = 2 * quoted + 4096;
    assert!(
        allocated <= bound,
        "find allocated {allocated} bytes for {quoted} bytes of quotes (bound {bound}): it holds \
         something per hit, not per quote"
    );
}
