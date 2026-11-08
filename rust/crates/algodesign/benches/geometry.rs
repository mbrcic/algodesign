//! Criterion benchmarks for `algodesign::geometry`: `orient2d`, the 2D range tree, the k-d tree
//! and the graph index.
//!
//! **`orient2d`.** Two input sets, each built once outside the timing, each timed as one pass over every triple
//! with the signs summed (so no call can be optimized away):
//!
//! - `uniform`: 10^6 seeded triples uniform in `[-1, 1]²`. The floating-point filter decides
//!   almost all of them, so this measures the fast path.
//! - `near_collinear`: 10^5 seeded near-collinear triples, built as the orientation tests build
//!   their near-collinear cases: `a` and `b` uniform in
//!   `[-1, 1]²`, `c` on the segment between them, then moved 0 to 3 ulps along one axis. The
//!   filter rarely trusts its answer here, so the exact stages run.
//!
//! **`range_tree_2d`.** 10^5 seeded points with integer coordinates uniform in `[0, 10^6)²`:
//! `build` times `RangeTree2D::new`; `query` times one pass of 1 000 seeded rectangles, each
//! side uniform up to `10^5` long (at most 1% of the points, about 250 on average), with the
//! reported ids summed. Each query walks `O(log n)` canonical subtrees, so their associated
//! trees and reports dominate.
//!
//! **`kdtree`.** 10^5 seeded points uniform in `[0, 1)²`: `build/b=1` and `build/b=8` time
//! `KdTree::with_bucket` at a leaf of one point (the Python's default) and of eight (the Rust's);
//! `nearest/b=1` and `nearest/b=8` time 1 000 seeded nearest-point questions on each, beside
//! `nearest/scan`, the scan over the same points.
//!
//! **`hnsw`.** 10^4 seeded points uniform in `[0, 1)^16`: `build` times `Hnsw::build` at M 16 and
//! `ef_construction` 200; `search/ef=…` times 200 seeded 10-nearest questions at `ef` 16, 64 and
//! 256, beside `search/scan`.
//!
//! Run: `cargo bench -p algodesign --bench geometry`.

// `criterion_group!` expands to a public function it does not document (as in `structures.rs`).
#![allow(missing_docs)]

use algodesign::geometry::hnsw::{Hnsw, HnswParams};
use algodesign::geometry::kdtree::KdTree;
use algodesign::geometry::orientation::orient2d;
use algodesign::geometry::point::Points;
use algodesign::geometry::range_tree::RangeTree2D;
use algodesign::geometry::scan;
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::hint::black_box;
use std::time::Duration;

type Tri = ([f64; 2], [f64; 2], [f64; 2]);

/// SplitMix64 (Vigna's `splitmix64.c`), the generator the geometry module and its tests
/// use; repeated here because `algodesign`'s own copy is crate-private.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in `[0, 1)`: the top 53 bits.
    fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }

    /// Uniform in `[-1, 1)`.
    fn unit(&mut self) -> f64 {
        2.0 * self.next_f64() - 1.0
    }
}

/// `x` moved `steps` representable doubles up (toward `+∞`) or down; `x` finite and nonzero.
fn ulps(x: f64, steps: u64, up: bool) -> f64 {
    let bits = x.to_bits();
    if up == (x > 0.0) {
        f64::from_bits(bits + steps)
    } else {
        f64::from_bits(bits - steps)
    }
}

fn uniform(n: usize) -> Vec<Tri> {
    let mut rng = SplitMix64(0x6E0_0001);
    (0..n)
        .map(|_| {
            (
                [rng.unit(), rng.unit()],
                [rng.unit(), rng.unit()],
                [rng.unit(), rng.unit()],
            )
        })
        .collect()
}

fn near_collinear(n: usize) -> Vec<Tri> {
    let mut rng = SplitMix64(0x6E0_0002);
    (0..n)
        .map(|_| {
            let a = [rng.unit(), rng.unit()];
            let b = [rng.unit(), rng.unit()];
            let t = rng.next_f64();
            let mut c = [a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])];
            let axis = (rng.next_u64() % 2) as usize;
            let steps = rng.next_u64() % 4;
            let up = rng.next_u64() % 2 == 1;
            if c[axis] != 0.0 {
                c[axis] = ulps(c[axis], steps, up);
            }
            (a, b, c)
        })
        .collect()
}

/// One pass: the number of left turns minus right turns, NaN counted apart, so every result is
/// used.
fn pass(triples: &[Tri]) -> (i64, u32) {
    let (mut turns, mut nan) = (0i64, 0u32);
    for &(a, b, c) in triples {
        let d = orient2d(black_box(a), black_box(b), black_box(c));
        if d > 0.0 {
            turns += 1;
        } else if d < 0.0 {
            turns -= 1;
        } else if d.is_nan() {
            nan += 1;
        }
    }
    (turns, nan)
}

fn bench_orient2d(c: &mut Criterion) {
    let mut group = c.benchmark_group("orient2d");
    group.sample_size(30);
    group.measurement_time(Duration::from_secs(6));
    for (id, triples) in [
        ("uniform", uniform(1_000_000)),
        ("near_collinear", near_collinear(100_000)),
    ] {
        group.throughput(Throughput::Elements(triples.len() as u64));
        group.bench_function(id, |b| b.iter(|| pass(black_box(&triples))));
    }
    group.finish();
}

/// `n` points with coordinates uniform in `[0, 10^6)`.
fn grid_points(n: usize) -> Vec<(i64, i64)> {
    let mut rng = SplitMix64(0x6E0_0003);
    (0..n)
        .map(|_| {
            let x = (rng.next_u64() % 1_000_000) as i64;
            let y = (rng.next_u64() % 1_000_000) as i64;
            (x, y)
        })
        .collect()
}

/// `n` rectangles `(lo, hi)`, each side uniform in `[0, 10^5]` long, inside `[0, 10^6)²`.
fn rectangles(n: usize) -> Vec<((i64, i64), (i64, i64))> {
    let mut rng = SplitMix64(0x6E0_0004);
    let side = |rng: &mut SplitMix64| {
        let len = (rng.next_u64() % 100_001) as i64;
        let lo = (rng.next_u64() % (1_000_000 - len as u64)) as i64;
        (lo, lo + len)
    };
    (0..n)
        .map(|_| {
            let (x0, x1) = side(&mut rng);
            let (y0, y1) = side(&mut rng);
            ((x0, y0), (x1, y1))
        })
        .collect()
}

fn bench_range_tree_2d(c: &mut Criterion) {
    let points = grid_points(100_000);
    let rects = rectangles(1_000);
    let tree = RangeTree2D::new(points.clone());
    let mut group = c.benchmark_group("range_tree_2d");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(6));
    group.throughput(Throughput::Elements(points.len() as u64));
    group.bench_function("build", |b| {
        b.iter(|| RangeTree2D::new(black_box(points.clone())).len());
    });
    group.throughput(Throughput::Elements(rects.len() as u64));
    group.bench_function("query", |b| {
        b.iter(|| {
            black_box(&rects)
                .iter()
                .map(|(lo, hi)| tree.query((&lo.0, &lo.1), (&hi.0, &hi.1)).len())
                .sum::<usize>()
        });
    });
    group.finish();
}

/// `n` points of `dim` coordinates uniform in `[0, 1)`, from `seed`.
fn unit_points(n: usize, dim: usize, seed: u64) -> Points {
    let mut rng = SplitMix64(seed);
    let coords = (0..n * dim)
        .map(|_| (rng.next_u64() >> 11) as f64 / (1u64 << 53) as f64)
        .collect();
    Points::new(dim, coords).expect("finite coordinates")
}

/// The rows of a `Points`, one `Vec` each, to ask as queries.
fn rows(points: &Points) -> Vec<Vec<f64>> {
    points.iter().map(<[f64]>::to_vec).collect()
}

fn bench_kdtree(c: &mut Criterion) {
    let points = unit_points(100_000, 2, 0x6E0_0005);
    let queries = rows(&unit_points(1_000, 2, 0x6E0_0006));
    let mut group = c.benchmark_group("kdtree");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(6));
    for bucket in [1, 8] {
        group.throughput(Throughput::Elements(points.len() as u64));
        group.bench_function(format!("build/b={bucket}"), |b| {
            b.iter(|| KdTree::with_bucket(black_box(points.clone()), bucket).len());
        });
        let tree = KdTree::with_bucket(points.clone(), bucket);
        group.throughput(Throughput::Elements(queries.len() as u64));
        group.bench_function(format!("nearest/b={bucket}"), |b| {
            b.iter(|| {
                queries
                    .iter()
                    .map(|q| tree.k_nearest(black_box(q), 1).len())
                    .sum::<usize>()
            });
        });
    }
    group.bench_function("nearest/scan", |b| {
        b.iter(|| {
            queries
                .iter()
                .map(|q| scan::k_nearest(&points, black_box(q), 1).len())
                .sum::<usize>()
        });
    });
    group.finish();
}

fn bench_hnsw(c: &mut Criterion) {
    let points = unit_points(10_000, 16, 0x6E0_0007);
    let queries = rows(&unit_points(200, 16, 0x6E0_0008));
    let mut group = c.benchmark_group("hnsw");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(10));
    group.throughput(Throughput::Elements(points.len() as u64));
    group.bench_function("build", |b| {
        b.iter(|| Hnsw::build(black_box(points.clone()), HnswParams::new(16)).len());
    });
    let graph = Hnsw::build(points.clone(), HnswParams::new(16));
    group.throughput(Throughput::Elements(queries.len() as u64));
    for ef in [16, 64, 256] {
        group.bench_function(format!("search/ef={ef}"), |b| {
            b.iter(|| {
                queries
                    .iter()
                    .map(|q| graph.search(black_box(q), 10, ef).len())
                    .sum::<usize>()
            });
        });
    }
    group.bench_function("search/scan", |b| {
        b.iter(|| {
            queries
                .iter()
                .map(|q| scan::k_nearest(&points, black_box(q), 10).len())
                .sum::<usize>()
        });
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_orient2d,
    bench_range_tree_2d,
    bench_kdtree,
    bench_hnsw
);
criterion_main!(benches);
