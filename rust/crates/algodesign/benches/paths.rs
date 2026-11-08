// SPDX-License-Identifier: Apache-2.0
//! Criterion benchmarks for `algodesign::paths`: one group per method, each on seeded inputs built
//! once outside the timing, each call's answer summed so no call can be optimized away.
//!
//! **`bfs`, `dijkstra`.** 10^5 vertices and 4 · 10^5 arrows with uniform ends (loops and doubled
//! arrows allowed), each costing 1 to 1000; `bfs` reads the same graph with every arrow costing
//! one. Both run from vertex 0.
//!
//! **`bellman_ford`.** The same graph, its costs shifted by a potential: arrow `u → v` costs
//! `c + p(u) − p(v)` with `p` uniform in `0..=2000`, so about three arrows in ten cost less than
//! nothing and no cycle does.
//!
//! **`dag`.** 10^5 vertices in a shuffled order and 4 · 10^5 arrows, each from an earlier vertex of
//! that order to a later one, costing −500 to 500: a graph with no cycle, from the first vertex of
//! the order.
//!
//! **`knapsack`.** 1000 items, each weighing 1 to 1000 and worth 1 to 1000, in a box of 10^4: 10^7
//! states.
//!
//! **`a_star`.** A 300 × 300 grid, an arrow each way between neighbors, each costing 1 to 10, from
//! one corner to the opposite one. `a_star/grid` takes the grid distance to the goal as its
//! estimate, which is consistent since no arrow costs less than one; `a_star/zero` takes the zero
//! estimate, which makes it Dijkstra's walk towards the goal.
//!
//! **`kruskal`, `prim`.** 10^5 vertices and 4 · 10^5 links with uniform ends (loops allowed), each
//! costing 1 to 1000.
//!
//! Run: `cargo bench -p algodesign --bench paths`, or one group: `cargo bench -p algodesign --bench
//! paths -- dijkstra`.

// `criterion_group!` expands to a public function it does not document (as in `structures.rs`).
#![allow(missing_docs)]

use algodesign::graphs::{Digraph, Graph};
use algodesign::paths::{
    a_star, bellman_ford, bfs, dag_paths, dijkstra, knapsack, kruskal, prim, Distances,
    LinkNetwork, Network,
};
use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use std::hint::black_box;
use std::time::Duration;

/// Vertices of the random graphs.
const N: usize = 100_000;
/// Arrows or links per vertex of the random graphs.
const DEGREE: usize = 4;
/// The side of the A* grid.
const SIDE: usize = 300;

/// SplitMix64 (Vigna's `splitmix64.c`), the generator the library and its tests use; repeated
/// here because `algodesign`'s own copy is crate-private.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A draw below `k`.
    fn below(&mut self, k: u64) -> u64 {
        self.next_u64() % k
    }

    /// A draw in `lo..=hi`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }
}

/// `n` vertices and `DEGREE · n` uniform pairs of ends, from `seed`.
fn uniform_pairs(n: usize, seed: u64) -> Vec<(u32, u32)> {
    let mut r = SplitMix64(seed);
    (0..DEGREE * n)
        .map(|_| (r.below(n as u64) as u32, r.below(n as u64) as u32))
        .collect()
}

/// `count` costs in `lo..=hi`, from `seed`.
fn costs(count: usize, lo: i64, hi: i64, seed: u64) -> Vec<i64> {
    let mut r = SplitMix64(seed);
    (0..count).map(|_| r.range(lo, hi)).collect()
}

/// The random network the `bfs`, `dijkstra` and `bellman_ford` groups share, before any shift.
fn random_network() -> Network {
    let arrows = uniform_pairs(N, 0x6E06_0001);
    let cost = costs(arrows.len(), 1, 1000, 0x6E06_0002);
    Network::new(Digraph::new(N, &arrows).expect("ends in range"), cost).expect("one cost each")
}

/// The random network with every arrow `u → v` costing `c + p(u) − p(v)`: some arrows below
/// nothing, every cycle as dear as before.
fn shifted_network() -> Network {
    let arrows = uniform_pairs(N, 0x6E06_0001);
    let base = costs(arrows.len(), 1, 1000, 0x6E06_0002);
    let p = costs(N, 0, 2000, 0x6E06_0003);
    let cost = arrows
        .iter()
        .zip(&base)
        .map(|(&(u, v), &c)| c + p[u as usize] - p[v as usize])
        .collect();
    Network::new(Digraph::new(N, &arrows).expect("ends in range"), cost).expect("one cost each")
}

/// A network with no cycle: the vertices in a shuffled order, every arrow from an earlier vertex
/// of it to a later one, negative costs included; and the first vertex of the order.
fn acyclic_network() -> (Network, u32) {
    let mut r = SplitMix64(0x6E06_0004);
    let mut order: Vec<u32> = (0..N as u32).collect();
    for i in (1..N).rev() {
        order.swap(i, r.below(i as u64 + 1) as usize);
    }
    let arrows: Vec<(u32, u32)> = (0..DEGREE * N)
        .map(|_| {
            let a = r.below(N as u64 - 1) as usize;
            let b = a + 1 + r.below((N - 1 - a) as u64) as usize;
            (order[a], order[b])
        })
        .collect();
    let cost = costs(arrows.len(), -500, 500, 0x6E06_0005);
    let net = Network::new(Digraph::new(N, &arrows).expect("ends in range"), cost)
        .expect("one cost each");
    (net, order[0])
}

/// The A* grid: vertex `y · SIDE + x`, an arrow each way between neighbors costing 1 to 10.
fn grid_network() -> Network {
    let at = |x: usize, y: usize| (y * SIDE + x) as u32;
    let mut arrows = Vec::new();
    for y in 0..SIDE {
        for x in 0..SIDE {
            if x + 1 < SIDE {
                arrows.extend([(at(x, y), at(x + 1, y)), (at(x + 1, y), at(x, y))]);
            }
            if y + 1 < SIDE {
                arrows.extend([(at(x, y), at(x, y + 1)), (at(x, y + 1), at(x, y))]);
            }
        }
    }
    let cost = costs(arrows.len(), 1, 10, 0x6E06_0006);
    Network::new(
        Digraph::new(SIDE * SIDE, &arrows).expect("ends in range"),
        cost,
    )
    .expect("one cost each")
}

/// The random link network the `kruskal` and `prim` groups share.
fn link_network() -> LinkNetwork {
    let links = uniform_pairs(N, 0x6E06_0007);
    let cost = costs(links.len(), 1, 1000, 0x6E06_0008);
    LinkNetwork::new(Graph::new(N, &links).expect("ends in range"), cost).expect("one cost each")
}

/// The vertices an answer reaches, so every call's result is used.
fn reached(d: &Distances) -> usize {
    d.cost.iter().filter(|c| c.is_some()).count()
}

fn bench_bfs_dijkstra(c: &mut Criterion) {
    let net = random_network();
    let m = net.graph().arrow_count() as u64;
    let mut group = c.benchmark_group("bfs");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Elements(m));
    group.bench_function("random", |b| {
        b.iter(|| reached(&bfs(black_box(net.graph()), 0)));
    });
    group.finish();
    let mut group = c.benchmark_group("dijkstra");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Elements(m));
    group.bench_function("random", |b| {
        b.iter(|| reached(&dijkstra(black_box(&net), 0)));
    });
    group.finish();
}

fn bench_bellman_ford(c: &mut Criterion) {
    let net = shifted_network();
    let mut group = c.benchmark_group("bellman_ford");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(10));
    group.throughput(Throughput::Elements(net.graph().arrow_count() as u64));
    group.bench_function("shifted", |b| {
        b.iter(|| {
            let d = bellman_ford(black_box(&net), 0).expect("no negative cycle");
            reached(&d)
        });
    });
    group.finish();
}

fn bench_dag(c: &mut Criterion) {
    let (net, start) = acyclic_network();
    let mut group = c.benchmark_group("dag");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Elements(net.graph().arrow_count() as u64));
    group.bench_function("acyclic", |b| {
        b.iter(|| reached(&dag_paths(black_box(&net), start).expect("no cycle")));
    });
    group.finish();
}

fn bench_knapsack(c: &mut Criterion) {
    let mut r = SplitMix64(0x6E06_0009);
    let weights: Vec<u64> = (0..1000).map(|_| 1 + r.below(1000)).collect();
    let values = costs(weights.len(), 1, 1000, 0x6E06_000A);
    let capacity = 10_000;
    let mut group = c.benchmark_group("knapsack");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(10));
    group.throughput(Throughput::Elements(weights.len() as u64 * (capacity + 1)));
    group.bench_function("items-1000-capacity-10000", |b| {
        b.iter(|| {
            knapsack(black_box(&weights), black_box(&values), capacity)
                .expect("one value per weight")
                .value
        });
    });
    group.finish();
}

fn bench_a_star(c: &mut Criterion) {
    let net = grid_network();
    let goal = (SIDE * SIDE - 1) as u32;
    // The grid distance to the goal: an arrow costs at least one, so the estimate drops by no more
    // than any arrow costs.
    let grid: Vec<i64> = (0..SIDE * SIDE)
        .map(|v| (2 * (SIDE - 1) - v % SIDE - v / SIDE) as i64)
        .collect();
    let zero = vec![0; SIDE * SIDE];
    let mut group = c.benchmark_group("a_star");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Elements(net.graph().arrow_count() as u64));
    for (id, estimate) in [("grid", &grid), ("zero", &zero)] {
        group.bench_function(id, |b| {
            b.iter(|| {
                let d = a_star(black_box(&net), 0, goal, estimate).expect("one estimate each");
                d.cost[goal as usize]
            });
        });
    }
    group.finish();
}

fn bench_kruskal_prim(c: &mut Criterion) {
    let net = link_network();
    let m = net.graph().link_count() as u64;
    let mut group = c.benchmark_group("kruskal");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Elements(m));
    group.bench_function("random", |b| b.iter(|| kruskal(black_box(&net)).len()));
    group.finish();
    let mut group = c.benchmark_group("prim");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(5));
    group.throughput(Throughput::Elements(m));
    group.bench_function("random", |b| b.iter(|| prim(black_box(&net)).len()));
    group.finish();
}

criterion_group!(
    benches,
    bench_bfs_dijkstra,
    bench_bellman_ford,
    bench_dag,
    bench_knapsack,
    bench_a_star,
    bench_kruskal_prim
);
criterion_main!(benches);
