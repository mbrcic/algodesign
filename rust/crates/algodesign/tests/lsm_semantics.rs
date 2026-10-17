// SPDX-License-Identifier: Apache-2.0
//! What the store *answers*, pinned across a change of how it stores things.
//!
//! The layering is deliberately observable (see the module doc), so a shape hash would move with
//! any policy change and pin nothing. These constants are the semantics instead: for a
//! deterministic mix of writes, deletes and re-writes, every `lookup` — which distinguishes
//! "never written" from "written, then deleted" — plus the live-key sequence `iter` produces, and
//! `len`, folded together after every single operation.
//!
//! FNV-1a rather than
//! `DefaultHasher`, whose algorithm std declines to keep stable across releases.

use algodesign::searching::lsm::Lsm;

/// Everything a client can observe: `get`, the live-key sequence, `len`, `is_valid`.
const CLIENT: u64 = 0x7517_b31f_99aa_9119;
/// The same run, plus `lookup`'s three-way answer, which distinguishes "never written" from
/// "written, then deleted". Collecting a tombstone turns the second into the first, so this
/// constant moves with when tombstones are collected, and `CLIENT` does not.
const WITH_TOMBSTONES: u64 = 0x6357_25a4_bf82_dddc;
const STEPS: u64 = 3480;

struct Fnv(u64);
impl Fnv {
    fn new() -> Self {
        Fnv(0xcbf2_9ce4_8422_2325)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0 ^ u64::from(*b)).wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    fn u64(&mut self, v: u64) {
        self.write(&v.to_le_bytes());
    }
    fn tag(&mut self, v: u8) {
        self.write(&[v]);
    }
}

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Fold everything the store can be asked, over the whole key space it can hold.
fn record(client: &mut Fnv, full: &mut Fnv, s: &Lsm<u64, u64>, span: u64) {
    for k in 0..span {
        match s.get(&k) {
            None => client.tag(0),
            Some(v) => {
                client.tag(1);
                client.u64(*v);
            }
        }
        match s.lookup(&k) {
            None => full.tag(0),
            Some(None) => full.tag(1),
            Some(Some(v)) => {
                full.tag(2);
                full.u64(*v);
            }
        }
    }
    for (k, v) in s {
        for h in [&mut *client, &mut *full] {
            h.u64(*k);
            h.u64(*v);
        }
    }
    for h in [&mut *client, &mut *full] {
        h.u64(s.len() as u64);
        h.tag(u8::from(s.is_valid()));
    }
}

#[test]
fn every_answer_survives_the_representation() {
    let mut client = Fnv::new();
    let mut full = Fnv::new();
    let mut steps: u64 = 0;
    for seed in 0..20u64 {
        for span in [4u64, 16, 64] {
            let mut rng = 0x_0000_5EED_0000_0000 ^ (seed << 16) ^ span;
            let mut s: Lsm<u64, u64> = Lsm::new();
            for _ in 0..(span * 2) {
                let k = splitmix64(&mut rng) % span;
                match splitmix64(&mut rng) % 4 {
                    0 => s.delete(k),
                    _ => s.write(k, splitmix64(&mut rng)),
                }
                record(&mut client, &mut full, &s, span);
                steps += 1;
            }
            // and again with compaction interleaved, which must change no answer
            s.flush();
            record(&mut client, &mut full, &s, span);
            s.compact_fully();
            record(&mut client, &mut full, &s, span);
            steps += 2;
        }
    }
    println!(
        "LSM steps={steps} client={:#018x} with_tombstones={:#018x}",
        client.0, full.0
    );
    assert_eq!(steps, STEPS, "the corpus changed size");
    assert_eq!(client.0, CLIENT, "a client-visible answer changed");
    assert_eq!(full.0, WITH_TOMBSTONES, "lookup's three-way answer changed");
}
