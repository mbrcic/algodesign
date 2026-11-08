use super::*;
use crate::geometry::{
    point::{sq_dist, Points},
    rng::SplitMix64,
    scan,
};
use proptest::prelude::*;

fn pts(rows: &[[f64; 2]]) -> Points {
    Points::from_rows(2, rows).unwrap()
}

fn sorted_by_base(p: &Points, base: &[f64], ids: &[u32]) -> Vec<(f64, u32)> {
    let mut v: Vec<(f64, u32)> = ids
        .iter()
        .map(|&i| (sq_dist(p.get(i as usize), base), i))
        .collect();
    v.sort_by(|a, b| a.0.total_cmp(&b.0).then(a.1.cmp(&b.1)));
    v
}

fn random_unit(n: usize, d: usize, seed: u64) -> Points {
    let mut r = SplitMix64::new(seed);
    Points::new(d, (0..n * d).map(|_| r.standard_normal()).collect())
        .unwrap()
        .normalized()
        .unwrap()
}

#[test]
fn lean_examples() {
    // Lean: the AlgoDesignTests/Geometry.lean neighbor-rule examples
    let p = pts(&[[1.0, 0.0], [0.0, 2.0], [2.0, 0.0], [1.0, 2.0]]);
    let base = [0.0, 0.0];
    assert_eq!(
        select_neighbors(&p, &base, &sorted_by_base(&p, &base, &[0, 1, 2]), 3),
        vec![0, 1]
    );
    assert_eq!(
        select_neighbors(&p, &base, &sorted_by_base(&p, &base, &[0, 1, 2]), 1),
        vec![0]
    );
    // the tie: (1, 2) is 5 from the base and 5 from the kept (2, 0) -- kept, as hnswlib does
    assert_eq!(
        select_neighbors(&p, &base, &sorted_by_base(&p, &base, &[2, 3]), 2),
        vec![2, 3]
    );
    // the greedy step
    let g = pts(&[[0.0, 0.0], [1.0, 0.0], [4.0, 4.0], [3.0, 3.0]]);
    assert_eq!(greedy_step(&g, &[5.0, 5.0], 0, &[1, 2, 3]), 2);
    assert_eq!(greedy_step(&g, &[0.0, 0.0], 0, &[1, 2]), 0);
}

proptest! {
    #[test]
    fn rule_is_diverse(rows in prop::collection::vec([-6i32..6, -6i32..6], 1..40), m in 1usize..8) {
        // Lean: selectNeighbors_diverse, _length_le, _subset, _head
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let base = [0.5, 0.25];
        let ids: Vec<u32> = (0..p.len() as u32).collect();
        let cands = sorted_by_base(&p, &base, &ids);
        let kept = select_neighbors(&p, &base, &cands, m);
        prop_assert!(kept.len() <= m);                                         // _length_le
        prop_assert!(kept.iter().all(|k| cands.iter().any(|c| c.1 == *k)));  // _subset
        prop_assert_eq!(kept.first(), cands.first().map(|c| &c.1));           // _head
        for (i, &a) in kept.iter().enumerate() {                              // _diverse
            for &b in &kept[i + 1..] {
                let (pa, pb) = (p.get(a as usize), p.get(b as usize));
                prop_assert!(sq_dist(&base, pb) <= sq_dist(pa, pb));
            }
        }
    }

    #[test]
    fn greedy_step_never_moves_away(rows in prop::collection::vec([-6i32..6, -6i32..6], 1..30), q in [-6i32..6, -6i32..6]) {
        // Lean: greedyStep_le
        let rows: Vec<[f64; 2]> = rows.iter().map(|r| r.map(f64::from)).collect();
        let p = pts(&rows);
        let q = q.map(f64::from);
        let nbrs: Vec<u32> = (1..p.len() as u32).collect();
        let next = greedy_step(&p, &q, 0, &nbrs);
        prop_assert!(sq_dist(p.get(next as usize), &q) <= sq_dist(p.get(0), &q));
    }
}

#[test]
fn degrees_and_nested_layers() {
    // The Rust build keeps the Lean `HNSW.Valid` and `HNSW.WellFormed` (`HNSW.valid_build` and
    // `HNSW.wellFormed_build` prove them of the Lean model):
    // degree ≤ M above level 0 and ≤ M0 at level 0; a node on level ℓ is on every level below; no
    // self-links, no duplicate links. Checked here only: every link target exists on that level.
    let h = Hnsw::build(random_unit(2000, 16, 1), HnswParams::new(8));
    assert!(
        h.max_level() >= 1,
        "2 000 points at M = 8 should reach level 1"
    );
    for v in 0..h.len() {
        for l in 0..=h.level(v) {
            let ns = h.neighbors(v, l);
            assert!(ns.len() <= if l == 0 { 16 } else { 8 });
            assert!(ns
                .iter()
                .all(|&u| u as usize != v && h.level(u as usize) >= l));
            let mut s = ns.to_vec();
            s.sort_unstable();
            s.dedup();
            assert_eq!(s.len(), ns.len());
        }
    }
}

#[test]
fn flat_is_one_level() {
    let h = Hnsw::build(random_unit(500, 8, 2), HnswParams::new(8).flat());
    assert_eq!(h.max_level(), 0);
    assert!((0..h.len()).all(|v| h.level(v) == 0));
}

#[test]
fn recall_against_the_scan() {
    // Statistical, with fixed seeds: recall@10 on 2 000 random unit vectors in d = 16, 100
    // queries. There is no guarantee; this pins measured levels, so a regression shows. Measured
    // (layered): 1.0 at ef = 100, 0.892 at ef = 10. The narrow beam is the sensitive
    // one: a well-built graph needs few hops.
    let p = random_unit(2000, 16, 3);
    let qs = random_unit(100, 16, 4);
    for flat in [false, true] {
        let params = if flat {
            HnswParams::new(16).flat()
        } else {
            HnswParams::new(16)
        };
        let h = Hnsw::build(p.clone(), params);
        for (ef, floor) in [(100, 0.95), (10, 0.80)] {
            let mut hit = 0;
            for q in qs.iter() {
                let truth: Vec<usize> = scan::k_nearest(&p, q, 10).iter().map(|n| n.id).collect();
                hit += h
                    .search(q, 10, ef)
                    .iter()
                    .filter(|n| truth.contains(&n.id))
                    .count();
            }
            let recall = hit as f64 / 1000.0;
            eprintln!("recall@10, flat {flat}, ef {ef}: {recall}");
            assert!(recall >= floor, "flat {flat}, ef {ef}: recall {recall}");
        }
    }
}

#[test]
fn edge_cases() {
    let h = Hnsw::build(Points::new(4, vec![]).unwrap(), HnswParams::new(4));
    assert!(h.is_empty());
    assert!(h.search(&[0.0; 4], 3, 10).is_empty());
    let one = Hnsw::build(pts(&[[1.0, 1.0]]), HnswParams::new(4));
    let got: Vec<usize> = one
        .search(&[1.0, 1.0], 5, 10)
        .iter()
        .map(|n| n.id)
        .collect();
    assert_eq!(got, vec![0]);
    let p = random_unit(300, 8, 5);
    let h = Hnsw::build(p.clone(), HnswParams::new(8));
    assert!(h.search(p.get(17), 0, 10).is_empty());
    assert_eq!(h.search(p.get(17), 1, 50)[0].id, 17); // a stored query finds itself
    assert_eq!(h.search(p.get(17), 5, 1).len(), 5); // ef below k is raised to k
    let dup = Points::new(2, [3.0, 3.0].repeat(50)).unwrap();
    let hd = Hnsw::build(dup, HnswParams::new(4));
    assert_eq!(hd.search(&[3.0, 3.0], 1, 10)[0].sq_dist, 0.0);
}

#[test]
#[should_panic(expected = "M")]
fn m_below_two_is_rejected() {
    let _ = HnswParams::new(1);
}

#[test]
fn greedy_descent_is_search_layer_with_ef_one() {
    // Alg. 5 descends the upper levels with SEARCH-LAYER at ef = 1; on data without distance
    // ties that is the fixed point of `greedy_step` (Lean `greedyStep`).
    let p = random_unit(1500, 8, 6);
    let h = Hnsw::build(p.clone(), HnswParams::new(6));
    let qs = random_unit(50, 8, 7);
    for q in qs.iter() {
        for level in 0..=h.max_level() {
            let start = (0..h.len()).find(|&v| h.level(v) >= level).unwrap() as u32;
            let dist = |i: u32| sq_dist(p.get(i as usize), q);
            let by_layer = h.search_layer(&dist, &[(dist(start), start)], 1, level)[0].1;
            let mut cur = start;
            loop {
                let next = greedy_step(&p, q, cur, h.neighbors(cur as usize, level));
                if next == cur {
                    break;
                }
                cur = next;
            }
            assert_eq!(by_layer, cur);
        }
    }
}

#[test]
fn a_huge_k_returns_every_point() {
    let p = random_unit(50, 4, 9);
    let h = Hnsw::build(p, HnswParams::new(4));
    for k in [1usize << 40, usize::MAX] {
        assert_eq!(h.search(&[0.5, 0.5, 0.5, 0.5], k, 10).len(), 50);
    }
}

#[cfg(feature = "unchecked")]
#[test]
fn the_unchecked_order_is_distance_then_node() {
    use std::cmp::Ordering;
    assert_eq!(by_distance_order(&(1.0, 5), &(2.0, 0)), Ordering::Less);
    assert_eq!(by_distance_order(&(1.0, 2), &(1.0, 1)), Ordering::Greater);
    assert_eq!(by_distance_order(&(1.0, 1), &(1.0, 1)), Ordering::Equal);
    let mut v = vec![(2.0, 0), (1.0, 3), (1.0, 1)];
    v.sort_by(by_distance_order);
    assert_eq!(v, vec![(1.0, 1), (1.0, 3), (2.0, 0)]);
}

fn grid_points(n: usize, seed: u64) -> Points {
    let mut r = SplitMix64::new(seed);
    let rows: Vec<[f64; 2]> = (0..n)
        .map(|_| [(r.next_f64() * 7.0).floor(), (r.next_f64() * 7.0).floor()])
        .collect();
    pts(&rows)
}

#[test]
fn every_graph_the_build_makes_is_valid() {
    // Lean: HNSW.Valid, HNSW.WellFormed
    for seed in 0..20 {
        for m in [2, 3] {
            for flat in [false, true] {
                let mut params = HnswParams::new(m);
                params.ef_construction = 4;
                params.seed = seed;
                let params = if flat { params.flat() } else { params };
                let h = Hnsw::build(grid_points(30, seed), params);
                assert_eq!(h.check_valid(), Ok(()));
                // the cached top level is the entry's, which the search descends from
                assert_eq!(h.entry.map(|e| h.level(e as usize)), Some(h.max_level()));
            }
        }
    }
    let h = Hnsw::build(random_unit(2000, 16, 1), HnswParams::new(8));
    assert_eq!(h.check_valid(), Ok(()));
}

#[test]
fn every_picking_is_diverse_new_lists_and_re_picks() {
    // Lean: HNSW.Picking.Valid, picksDiverse_selectNeighbors
    let mut re_picks = 0;
    for seed in 0..20 {
        let mut params = HnswParams::new(2);
        params.ef_construction = 4;
        params.seed = seed;
        let p = grid_points(30, seed);
        let (_, pickings) = Hnsw::build_with_pickings(p.clone(), params);
        let mut newest = 0;
        for (i, pk) in pickings.iter().enumerate() {
            let base = p.get(pk.base as usize);
            assert_eq!(
                check_picking_valid(&p, base, &pk.candidates, &pk.picked, pk.m),
                Ok(()),
                "picking #{i}"
            );
            // a re-pick: the base is an earlier node than the one being inserted
            if pk.base >= newest {
                newest = pk.base;
            } else {
                re_picks += 1;
            }
        }
    }
    assert!(
        re_picks > 0,
        "the corpus reaches the re-pick of an overfull list"
    );
}

#[test]
fn the_picking_piece_fails_where_it_should() {
    // (0,0) base; candidates (2,0) at 4 and (1,2) at 5; (1,2) is 5 from (2,0): a tie, kept
    let p = pts(&[[2.0, 0.0], [1.0, 2.0], [1.0, 0.0], [2.0, 0.0]]);
    let base = [0.0, 0.0];
    assert!(is_picks_diverse(&p, &base, &[0, 1], &[0, 1], 2));
    assert!(!is_picks_diverse(&p, &base, &[0, 1], &[0], 2)); // the tie dropped (rule A)
    assert!(!is_picks_diverse(&p, &base, &[0, 1], &[1, 0], 2)); // out of order
    assert!(is_picks_diverse(&p, &base, &[0, 1], &[0], 1)); // the cap
    assert!(!is_picks_diverse(&p, &base, &[1, 0], &[1, 0], 2)); // candidates not nearest first
                                                                // (2,0) blocked by (1,0): 1 < 4
    assert!(is_picks_diverse(&p, &base, &[2, 0], &[2], 3));
    assert!(!is_picks_diverse(&p, &base, &[2, 0], &[2, 0], 3));
    // a pick with the same coordinates as the candidate is the same pick
    assert!(is_picks_diverse(&p, &base, &[2, 0], &[2], 3));
    assert!(is_picks_diverse(&p, &base, &[0, 1], &[3, 1], 2));
    // ids off the points: false, not a panic
    assert!(!is_picks_diverse(&p, &base, &[9], &[], 1));
    assert!(!is_picks_diverse(&p, &[0.0], &[], &[], 1));
    assert_eq!(
        check_picking_valid(&p, &base, &[0, 1], &[0], 2),
        Err("invariant 2 (picks_diverse)")
    );
}

#[test]
fn each_graph_piece_fails_alone() {
    let p = pts(&[[0.0, 0.0], [1.0, 0.0], [0.0, 1.0]]);
    let params = || HnswParams::new(2); // m = 2, m0 = 4
    let g = |links: Vec<Vec<Vec<u32>>>, entry| {
        Hnsw::from_links_unchecked(p.clone(), params(), links, entry)
    };
    let good = g(
        vec![vec![vec![1, 2], vec![]], vec![vec![0, 2]], vec![vec![0, 1]]],
        Some(0),
    );
    assert_eq!(good.check_valid(), Ok(()));
    let over = g(
        vec![vec![vec![1, 2], vec![]], vec![vec![0, 2]], vec![vec![0, 1]]],
        Some(0),
    );
    let mut over = over;
    over.params.m0 = 1;
    assert_eq!(over.check_valid(), Err("invariant 1 (degree_bounded)"));
    let up = g(
        vec![
            vec![vec![1, 2], vec![1]],
            vec![vec![0, 2]],
            vec![vec![0, 1]],
        ],
        Some(0),
    );
    assert_eq!(up.check_valid(), Err("invariant 3 (nested_layers)"));
    let off = g(
        vec![vec![vec![1, 7]], vec![vec![0]], vec![vec![0]]],
        Some(0),
    );
    assert_eq!(off.check_valid(), Err("invariant 3 (nested_layers)"));
    let none = g(vec![vec![vec![]], vec![], vec![vec![]]], Some(0));
    assert_eq!(none.check_valid(), Err("invariant 3 (nested_layers)"));
    let selfl = g(vec![vec![vec![0]], vec![vec![]], vec![vec![]]], Some(0));
    assert_eq!(selfl.check_valid(), Err("not in the box (no_self_links)"));
    let rep = g(vec![vec![vec![1, 1]], vec![vec![0]], vec![vec![]]], Some(0));
    assert_eq!(rep.check_valid(), Err("not in the box (no_repeated_links)"));
    // the entry below the top level, and no entry on a graph with nodes
    let low = g(
        vec![vec![vec![1, 2], vec![]], vec![vec![0, 2]], vec![vec![0, 1]]],
        Some(1),
    );
    assert!(low.is_nested_layers() && !low.is_entry_on_top());
    assert_eq!(low.check_valid(), Err("not in the box (entry_on_top)"));
    let lost = g(vec![vec![vec![1]], vec![vec![0]], vec![vec![]]], None);
    assert_eq!(lost.check_valid(), Err("not in the box (entry_on_top)"));
    // a node with no point behind it, and a point with no node
    for links in [
        vec![vec![vec![1]], vec![vec![0]], vec![vec![]], vec![vec![]]],
        vec![vec![vec![1]], vec![vec![0]]],
    ] {
        let short = Hnsw::from_links_unchecked(p.clone(), params(), links, Some(0));
        assert!(!short.is_one_node_per_point());
        assert_eq!(
            short.check_valid(),
            Err("not in the box (one_node_per_point)")
        );
    }
}

#[test]
fn equality_and_debug_skip_the_visited_pool() {
    let h = Hnsw::build(random_unit(50, 4, 1), HnswParams::new(4));
    let before = format!("{h:?}");
    let _ = h.search(&[1.0, 0.0, 0.0, 0.0], 3, 10);
    assert_eq!(format!("{h:?}"), before);
    assert!(!before.contains("visited") && !before.contains("marks"));
    assert_eq!(h, h.clone());
    assert_eq!(h, Hnsw::build(random_unit(50, 4, 1), HnswParams::new(4)));
    let other = HnswParams {
        seed: 1,
        ..HnswParams::new(4)
    };
    assert_ne!(h, Hnsw::build(random_unit(50, 4, 1), other));
}

#[test]
#[should_panic(expected = "finite m_L")]
fn build_refuses_a_nan_ml() {
    let params = HnswParams {
        ml: f64::NAN,
        ..HnswParams::new(2)
    };
    let _ = Hnsw::build(pts(&[[0.0, 0.0]]), params);
}

#[test]
#[should_panic(expected = "ef_construction ≥ 1")]
fn build_refuses_a_zero_beam() {
    let params = HnswParams {
        ef_construction: 0,
        ..HnswParams::new(2)
    };
    let _ = Hnsw::build(pts(&[[0.0, 0.0]]), params);
}

#[test]
fn search_ends_with_finish() {
    // Lean: HNSW.promise_finish
    let h = Hnsw::build(random_unit(300, 8, 3), HnswParams::new(4));
    let mut r = SplitMix64::new(9);
    for _ in 0..50 {
        let q: Vec<f64> = (0..8).map(|_| r.standard_normal()).collect();
        for k in [1, 5, 40] {
            let beam = h.search_beam(&q, k, 10);
            assert_eq!(h.search(&q, k, 10), finish(beam, k));
        }
    }
    // the tie goes to the lower node; distances are the ones measured
    let f = finish(vec![(9.0, 0), (1.0, 2), (1.0, 1)], 2);
    assert_eq!(
        f.iter().map(|n| (n.sq_dist, n.id)).collect::<Vec<_>>(),
        vec![(1.0, 1), (1.0, 2)]
    );
    assert!(finish(vec![(1.0, 0)], 0).is_empty());
}

/// The walk `search_walk` records, checked against the graph: the descent on each upper layer is
/// repeated greedy steps to a fixed point, each layer starts where the one above stopped, the
/// beam on layer 0 starts where the descent stopped, every node pushed is in the list of the node
/// it was read from, and every beam node is the start or was pushed.
fn check_walk(h: &Hnsw, q: &[f64], k: usize, ef: usize) {
    let (beam, walk) = h.search_walk(q, k, ef);
    assert_eq!(h.search(q, k, ef), finish(beam.clone(), k));
    let Some(entry) = h.entry else {
        assert!(beam.is_empty() && walk == Walk::default());
        return;
    };
    if k == 0 {
        return;
    }
    let layers: Vec<usize> = walk.upper.iter().map(|(lc, _)| *lc).collect();
    assert_eq!(layers, (1..=h.max_level()).rev().collect::<Vec<_>>());
    let mut at = entry;
    for (lc, nodes) in &walk.upper {
        assert_eq!(
            nodes[0], at,
            "layer {lc} starts where the one above stopped"
        );
        for pair in nodes.windows(2) {
            let next = greedy_step(h.points(), q, pair[0], h.neighbors(pair[0] as usize, *lc));
            assert_eq!(
                next, pair[1],
                "layer {lc}: a step the greedy rule would not take"
            );
        }
        at = *nodes.last().unwrap();
        let stays = greedy_step(h.points(), q, at, h.neighbors(at as usize, *lc));
        assert_eq!(
            stays, at,
            "layer {lc}: the descent stopped before the fixed point"
        );
    }
    assert_eq!(walk.start, Some(at));
    for (node, pushed) in &walk.level0 {
        for e in pushed {
            assert!(h.neighbors(*node as usize, 0).contains(e));
        }
    }
    for &(_, v) in &beam {
        assert!(v == at || walk.level0.iter().any(|(_, pushed)| pushed.contains(&v)));
    }
}

#[test]
fn the_walk_is_greedy_steps_then_the_beam_search_returns() {
    // Lean: greedyStep; the record a separate Lean–Rust check replays
    let h = Hnsw::build(random_unit(1500, 8, 6), HnswParams::new(6));
    assert!(h.max_level() >= 2, "the walk should cross upper layers");
    for q in random_unit(50, 8, 7).iter() {
        for (k, ef) in [(1, 1), (5, 10), (10, 40)] {
            check_walk(&h, q, k, ef);
        }
    }
    // integer points: distance ties on every layer, the first of equals kept on both sides
    for seed in 0..20 {
        let h = Hnsw::build(grid_points(60, seed), HnswParams::new(2));
        for q in grid_points(10, seed + 100).iter() {
            for (k, ef) in [(1, 1), (3, 5)] {
                check_walk(&h, q, k, ef);
            }
        }
    }
    let flat = Hnsw::build(random_unit(200, 4, 2), HnswParams::new(4).flat());
    let (_, walk) = flat.search_walk(&[0.5; 4], 3, 10);
    assert!(walk.upper.is_empty() && walk.start == flat.entry);
    let empty = Hnsw::build(Points::new(2, vec![]).unwrap(), HnswParams::new(2));
    check_walk(&empty, &[0.0, 0.0], 3, 10);
}

#[test]
fn levels_thin_out_by_m() {
    // each layer up keeps a random few of the one below: P(level ≥ 1) = 1/M
    for m in [2usize, 4, 16] {
        let mut rng = SplitMix64::new(m as u64);
        let ml = 1.0 / (m as f64).ln();
        let draws = 200_000;
        let up = (0..draws).filter(|_| draw_level(&mut rng, ml) >= 1).count();
        let rate = up as f64 / draws as f64;
        assert!((rate - 1.0 / m as f64).abs() < 0.01, "m = {m}: {rate}");
    }
}

#[test]
#[should_panic(expected = "HNSW needs m ≤ m0")]
fn build_refuses_m0_below_m() {
    let mut params = HnswParams::new(4);
    params.m0 = 3;
    let _ = Hnsw::build(grid_points(10, 0), params);
}
