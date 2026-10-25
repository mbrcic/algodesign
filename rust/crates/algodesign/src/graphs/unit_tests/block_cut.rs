use super::*;
use crate::graphs::naive;
use proptest::prelude::*;

fn graph(n: usize, links: &[(u32, u32)]) -> Graph {
    Graph::new(n, links).unwrap()
}

/// Every block's links, in emission order, each in pop order.
fn all_links(b: &Blocks) -> Vec<Vec<u32>> {
    (0..b.count()).map(|i| b.block_links(i).to_vec()).collect()
}

/// Every block's vertices, in emission order.
fn all_vertices(b: &Blocks) -> Vec<Vec<u32>> {
    (0..b.count())
        .map(|i| b.block_vertices(i).to_vec())
        .collect()
}

fn blocks_of_links(b: &Blocks, m: usize) -> Vec<Option<u32>> {
    (0..m).map(|e| b.block_of_link(e)).collect()
}

fn parents(f: &BlockCutForest) -> Vec<u32> {
    (0..f.node_count()).map(|x| f.parent(x)).collect()
}

fn depths(f: &BlockCutForest) -> Vec<u32> {
    (0..f.node_count()).map(|x| f.depth(x)).collect()
}

fn nodes(f: &BlockCutForest, n: usize) -> Vec<u32> {
    (0..n).map(|p| f.node_of(p)).collect()
}

/// The link stack's blocks are the forest's: one node per block and per cut vertex; a block's
/// neighbours in the forest are exactly the cut vertices among its vertices; every vertex's node
/// holds it; one tree per piece, with depths one more than the parent's.
fn forest_matches(n: usize, links: &[(u32, u32)], b: &Blocks, f: &BlockCutForest) -> bool {
    let nb = b.count();
    let cuts = b.cut_vertices();
    let cut_node = |p: u32| cuts.binary_search(&p).ok().map(|k| (nb + k) as u32);
    let mut want: Vec<(u32, u32)> = (0..nb)
        .flat_map(|i| {
            b.block_vertices(i)
                .iter()
                .filter_map(move |&p| cut_node(p).map(|x| (i as u32, x)))
        })
        .collect();
    want.sort_unstable();
    let mut got: Vec<(u32, u32)> = (0..f.node_count())
        .filter(|&x| f.parent(x) as usize != x)
        .map(|x| {
            let (y, x) = (f.parent(x), x as u32);
            (x.min(y), x.max(y))
        })
        .collect();
    got.sort_unstable();
    let roots = (0..f.node_count())
        .filter(|&x| f.parent(x) as usize == x)
        .count();
    let depths_ok = (0..f.node_count()).all(|x| {
        let p = f.parent(x) as usize;
        if p == x {
            f.depth(x) == 0
        } else {
            f.depth(x) == f.depth(p) + 1
        }
    });
    let nodes_ok = (0..n as u32).all(|p| {
        let x = f.node_of(p as usize);
        match cut_node(p) {
            Some(c) => x == c,
            None => {
                let holding: Vec<usize> = (0..nb)
                    .filter(|&i| b.block_vertices(i).contains(&p))
                    .collect();
                holding == [x as usize]
            }
        }
    });
    f.node_count() == nb + cuts.len()
        && got == want
        && roots == naive::pieces(n, links)
        && depths_ok
        && nodes_ok
}

#[test]
fn on_a_path_every_link_is_a_bridge_and_every_inner_vertex_a_cut_vertex() {
    let links = [(0, 1), (1, 2), (2, 3)];
    let g = graph(4, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[0, 1, 2]);
    assert_eq!(b.cut_vertices(), &[1, 2]);
    // The deepest link finishes first.
    assert_eq!(all_links(&b), vec![vec![2], vec![1], vec![0]]);
    assert_eq!(all_vertices(&b), vec![vec![2, 3], vec![1, 2], vec![0, 1]]);
    let f = BlockCutForest::new(&g, &b);
    assert!(forest_matches(4, &links, &b, &f));
    assert_eq!(f.separators(0, 3), Some(vec![1, 2]));
    assert_eq!(f.separators(1, 3), Some(vec![2]));
    assert_eq!(f.separators(1, 2), Some(vec![]));
}

#[test]
fn a_cycle_is_one_block_with_no_bridge_and_no_cut_vertex() {
    // 0 → 1 → 2 by tree links; 2's link to 0 climbs back, so nothing pops until 1 finishes.
    let links = [(0, 1), (1, 2), (2, 0)];
    let g = graph(3, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[] as &[u32]);
    assert_eq!(b.cut_vertices(), &[] as &[u32]);
    assert_eq!(all_links(&b), vec![vec![2, 1, 0]]);
    assert_eq!(all_vertices(&b), vec![vec![0, 1, 2]]);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(f.separators(0, 2), Some(vec![]));
}

#[test]
fn the_bowtie_pops_at_d_because_a_non_tree_link_passes_the_entry_number() {
    // a–b, b–c, c–a, b–d, d–e, e–b as 0..4. From c the walk climbs back to a, so low[b] is a's
    // number before d–e–b is walked; e's link to b passes b's entry number, and d's block pops.
    // Passing low[b] instead would keep it on the stack and merge the two triangles.
    let links = [(0, 1), (1, 2), (2, 0), (1, 3), (3, 4), (4, 1)];
    let g = graph(5, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[] as &[u32]);
    assert_eq!(b.cut_vertices(), &[1]);
    assert_eq!(
        blocks_of_links(&b, 6),
        vec![Some(1), Some(1), Some(1), Some(0), Some(0), Some(0)]
    );
    assert_eq!(all_links(&b), vec![vec![5, 4, 3], vec![2, 1, 0]]);
    assert_eq!(all_vertices(&b), vec![vec![1, 3, 4], vec![0, 1, 2]]);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(parents(&f), vec![2, 1, 1]);
    assert_eq!(depths(&f), vec![2, 0, 1]);
    assert_eq!(nodes(&f, 5), vec![1, 2, 1, 0, 0]);
    assert_eq!(f.separators(0, 4), Some(vec![1]));
    assert_eq!(f.separators(1, 4), Some(vec![]));
    assert!(forest_matches(5, &links, &b, &f));
}

#[test]
fn two_cycles_sharing_a_vertex_through_the_root() {
    // The bowtie with the shared vertex as the root: a root with two children is a cut vertex.
    let links = [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)];
    let g = graph(5, &links);
    let b = blocks(&g);
    assert_eq!(b.cut_vertices(), &[0]);
    assert_eq!(b.bridges(), &[] as &[u32]);
    assert_eq!(all_vertices(&b), vec![vec![0, 1, 2], vec![0, 3, 4]]);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(f.separators(1, 4), Some(vec![0]));
    assert_eq!(f.separators(1, 2), Some(vec![]));
    assert!(forest_matches(5, &links, &b, &f));
}

#[test]
fn disconnected_pieces_have_one_tree_each() {
    let links = [(0, 1), (2, 3), (3, 4), (4, 2)];
    let g = graph(6, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[0]);
    assert_eq!(b.cut_vertices(), &[] as &[u32]);
    assert_eq!(all_links(&b), vec![vec![0], vec![3, 2, 1], vec![]]);
    assert_eq!(all_vertices(&b), vec![vec![0, 1], vec![2, 3, 4], vec![5]]);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(parents(&f), vec![0, 1, 2]);
    assert_eq!(f.separators(0, 2), None);
    assert_eq!(f.separators(5, 0), None);
    assert_eq!(f.separators(2, 4), Some(vec![]));
    assert_eq!(f.separators(5, 5), Some(vec![]));
    assert!(forest_matches(6, &links, &b, &f));
}

#[test]
fn a_doubled_link_is_never_a_bridge_and_its_copies_share_a_block() {
    // Given in opposite directions. The walk arrives at 1 by link 0 and skips only link 0, so
    // link 1 climbs back to 0.
    let links = [(0, 1), (1, 0)];
    let g = graph(2, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[] as &[u32]);
    assert_eq!(b.cut_vertices(), &[] as &[u32]);
    assert_eq!(all_links(&b), vec![vec![1, 0]]);
    assert_eq!(all_vertices(&b), vec![vec![0, 1]]);
}

#[test]
fn a_triple_link_is_one_block() {
    let g = graph(2, &[(0, 1), (0, 1), (1, 0)]);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[] as &[u32]);
    assert_eq!(all_links(&b), vec![vec![2, 1, 0]]);
}

#[test]
fn a_doubled_link_inside_a_cycle_joins_the_cycle_s_block() {
    let links = [(0, 1), (1, 0), (1, 2), (2, 0)];
    let g = graph(3, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[] as &[u32]);
    assert_eq!(b.cut_vertices(), &[] as &[u32]);
    assert_eq!(all_links(&b), vec![vec![3, 2, 1, 0]]);
}

#[test]
fn a_loop_is_ignored_and_in_no_block() {
    let links = [(0, 0), (0, 1), (1, 1)];
    let g = graph(2, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[1]);
    assert_eq!(b.cut_vertices(), &[] as &[u32]);
    assert_eq!(blocks_of_links(&b, 3), vec![None, Some(0), None]);
    assert_eq!(all_links(&b), vec![vec![1]]);
}

#[test]
fn a_vertex_with_only_loops_is_an_isolated_vertex_and_its_own_block() {
    let links = [(0, 1), (1, 0), (1, 1), (1, 2), (3, 3)];
    let g = graph(4, &links);
    let b = blocks(&g);
    assert_eq!(b.bridges(), &[3]);
    assert_eq!(b.cut_vertices(), &[1]);
    assert_eq!(
        blocks_of_links(&b, 5),
        vec![Some(1), Some(1), None, Some(0), None]
    );
    assert_eq!(all_links(&b), vec![vec![3], vec![1, 0], vec![]]);
    assert_eq!(all_vertices(&b), vec![vec![1, 2], vec![0, 1], vec![3]]);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(parents(&f), vec![3, 1, 2, 1]);
    assert_eq!(depths(&f), vec![2, 0, 0, 1]);
    assert_eq!(nodes(&f, 4), vec![1, 3, 0, 2]);
    assert_eq!(f.separators(0, 2), Some(vec![1]));
    assert_eq!(f.separators(0, 3), None);
    assert_eq!(f.separators(3, 3), Some(vec![]));
    assert!(forest_matches(4, &links, &b, &f));
    // A vertex with no link at all is isolated the same way.
    let g = graph(1, &[]);
    let b = blocks(&g);
    assert_eq!(all_vertices(&b), vec![vec![0]]);
    assert_eq!(BlockCutForest::new(&g, &b).separators(0, 0), Some(vec![]));
    assert_eq!(blocks(&graph(0, &[])).count(), 0);
}

#[test]
fn siblings_meeting_at_one_parent_count_it_once() {
    // A star: 0 joined to 1, 2, 3. Nodes 1 and 2 are the blocks {0,1} and {0,2}, both under the
    // cut vertex 0; their path meets at 0's node once.
    let links = [(0, 1), (0, 2), (0, 3)];
    let g = graph(4, &links);
    let b = blocks(&g);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(f.separators(1, 2), Some(vec![0]));
    assert_eq!(f.separators(3, 1), Some(vec![0]));
    assert!(forest_matches(4, &links, &b, &f));
}

#[test]
#[should_panic(expected = "out of range")]
fn a_query_vertex_out_of_range_panics() {
    let g = graph(2, &[(0, 1)]);
    let b = blocks(&g);
    let _ = BlockCutForest::new(&g, &b).separators(0, 2);
}

#[test]
fn a_million_vertex_path_runs_without_the_call_stack() {
    // 256 KiB: any frame per vertex on the call stack would overflow it.
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let n = 1_000_000u32;
            let links: Vec<(u32, u32)> = (0..n - 1).map(|v| (v, v + 1)).collect();
            let g = graph(n as usize, &links);
            let b = blocks(&g);
            let every_link: Vec<u32> = (0..n - 1).collect();
            let inner: Vec<u32> = (1..n - 1).collect();
            assert_eq!(b.bridges(), &every_link[..]);
            assert_eq!(b.cut_vertices(), &inner[..]);
            assert_eq!(b.count(), (n - 1) as usize);
            let f = BlockCutForest::new(&g, &b);
            assert_eq!(f.separators(0, n as usize - 1), Some(inner));
        })
        .expect("spawning a thread")
        .join()
        .expect("the body panicked");
}

/// A number of vertices and some links between them, loops and doubled links common.
fn graphs() -> impl Strategy<Value = (usize, Vec<(u32, u32)>)> {
    (1usize..=7).prop_flat_map(|n| {
        let m = n as u32;
        (Just(n), prop::collection::vec((0..m, 0..m), 0..12))
    })
}

/// The walk against the oracles: bridges and cut vertices by deletion, the block relation by
/// cycles, isolated vertices, each block's vertices, the forest, and separators for every pair.
fn agrees_with_the_oracles(n: usize, links: &[(u32, u32)]) -> Result<(), TestCaseError> {
    let g = graph(n, links);
    let b = blocks(&g);
    let m = links.len();
    prop_assert_eq!(b.bridges(), &naive::bridges(n, links)[..]);
    prop_assert_eq!(b.cut_vertices(), &naive::cut_vertices(n, links)[..]);
    let together = naive::same_block(n, links);
    for e in 0..m {
        let loop_ = links[e].0 == links[e].1;
        prop_assert_eq!(b.block_of_link(e).is_none(), loop_);
        for (f, &want) in together[e].iter().enumerate() {
            let same = !loop_ && b.block_of_link(e) == b.block_of_link(f);
            prop_assert_eq!(same, want, "links {} and {}", e, f);
        }
    }
    // Every link in its block's list once; a block's vertices are its links' ends, or the
    // isolated vertex, which is exactly a vertex with no link but loops.
    let mut listed = vec![0usize; m];
    let mut isolated = Vec::new();
    for i in 0..b.count() {
        for &e in b.block_links(i) {
            listed[e as usize] += 1;
            prop_assert_eq!(b.block_of_link(e as usize), Some(i as u32));
        }
        let mut ends: Vec<u32> = b
            .block_links(i)
            .iter()
            .flat_map(|&e| [links[e as usize].0, links[e as usize].1])
            .collect();
        ends.sort_unstable();
        ends.dedup();
        if ends.is_empty() {
            prop_assert_eq!(b.block_vertices(i).len(), 1);
            isolated.push(b.block_vertices(i)[0]);
        } else {
            prop_assert_eq!(b.block_vertices(i), &ends[..]);
        }
    }
    for e in 0..m {
        prop_assert_eq!(listed[e], usize::from(links[e].0 != links[e].1));
    }
    let lonely: Vec<u32> = (0..n as u32)
        .filter(|&v| links.iter().all(|&(a, c)| a == c || (a != v && c != v)))
        .collect();
    prop_assert_eq!(isolated, lonely);
    let f = BlockCutForest::new(&g, &b);
    prop_assert!(forest_matches(n, links, &b, &f));
    for u in 0..n as u32 {
        for v in 0..n as u32 {
            prop_assert_eq!(
                f.separators(u as usize, v as usize),
                naive::separators(n, links, u, v),
                "vertices {} and {}",
                u,
                v
            );
        }
    }
    Ok(())
}

proptest! {
    #[test]
    fn on_any_small_multigraph_the_walk_agrees_with_the_oracles((n, links) in graphs()) {
        agrees_with_the_oracles(n, &links)?;
    }

    #[test]
    fn on_a_denser_multigraph_the_walk_agrees_with_the_oracles(
        (n, links) in (2usize..=5).prop_flat_map(|n| {
            let m = n as u32;
            (Just(n), prop::collection::vec((0..m, 0..m), 4..10))
        })
    ) {
        agrees_with_the_oracles(n, &links)?;
    }
}

/// The bowtie: 0–1, 1–2, 2–0, 1–3, 3–4, 4–1, plus a loop at 2 and an isolated vertex 5.
const BOWTIE: [(u32, u32); 7] = [(0, 1), (1, 2), (2, 0), (1, 3), (3, 4), (4, 1), (2, 2)];

#[test]
fn every_state_of_the_walk_is_valid() {
    // Lean: valid_start, Walk.traceValid
    let g = graph(6, &BOWTIE);
    let states = Walk::trace(&g);
    // Two roots entered, 14 row entries taken (the loop's two among them), four vertices finished
    // under a parent, two roots finished.
    assert_eq!(states.len(), 2 + 14 + 4 + 2);
    assert!(states.iter().all(|w| w.check_valid(&g).is_ok()));
}

/// The first state of the walk on the bowtie with a link on the stack, one part changed.
fn changed(f: impl FnOnce(&mut WalkParts)) -> Walk {
    let g = graph(6, &BOWTIE);
    let first = Walk::trace(&g)
        .into_iter()
        .find(|w| !w.link_stack.is_empty());
    let mut parts = first.unwrap().parts();
    f(&mut parts);
    Walk::from_parts(parts)
}

#[test]
fn each_broken_walk_state_names_its_piece() {
    let g = graph(6, &BOWTIE);
    assert_eq!(changed(|_| {}).check_valid(&g), Ok(()));
    // A climb-back number one lower than anything the subtree reaches.
    let low = changed(|p| {
        let v = p.path.last().unwrap().0 as usize;
        p.low[v] = 0;
    });
    assert_eq!(
        low.check_valid(&g),
        Err("invariant 1 (climb_back_is_earliest)")
    );
    // The top link of the stack taken off, not in any block.
    let lost = changed(|p| {
        p.link_stack.pop();
    });
    assert_eq!(
        lost.check_valid(&g),
        Err("invariant 2 (stack_holds_open_links)")
    );
    // A link on the stack twice.
    let twice = changed(|p| {
        let top = *p.link_stack.last().unwrap();
        p.link_stack.push(top);
    });
    assert_eq!(
        twice.check_valid(&g),
        Err("invariant 2 (stack_holds_open_links)")
    );
    // A block without links whose vertex has a link.
    let empty = changed(|p| {
        p.link_offsets.push(p.links.len());
        p.alone.push(0);
    });
    assert_eq!(
        empty.check_valid(&g),
        Err("invariant 2 (stack_holds_open_links)")
    );
}

#[test]
fn the_block_relation_reads_cycles_through_distinct_vertices() {
    let g = graph(6, &BOWTIE);
    let same = SameBlock::new(&g);
    assert!(same.holds(0, 2) && same.holds(3, 5) && same.holds(1, 1));
    assert!(!same.holds(0, 3) && !same.holds(6, 6) && !same.holds(0, 7));
    let doubled = graph(3, &[(0, 1), (1, 0), (1, 2)]);
    let same = SameBlock::new(&doubled);
    assert!(same.holds(0, 1) && !same.holds(1, 2));
}

proptest! {
    #[test]
    fn on_any_graph_every_state_of_the_walk_is_valid((n, links) in graphs()) {
        let g = graph(n, &links);
        for w in Walk::trace(&g) {
            prop_assert_eq!(w.check_valid(&g), Ok(()));
        }
    }

    #[test]
    fn the_block_relation_is_the_oracle_s((n, links) in graphs()) {
        let g = graph(n, &links);
        let same = SameBlock::new(&g);
        let oracle = naive::same_block(n, &links);
        for (e, row) in oracle.iter().enumerate() {
            for (f, &together) in row.iter().enumerate() {
                prop_assert_eq!(same.holds(e, f), together);
            }
        }
    }
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "another graph's")]
fn the_forest_refuses_another_graphs_blocks() {
    // The path 0 – 1 – 2, given the blocks of 0 – 2 – 1: as many vertices and links, so only the
    // links read against the blocks show it (unchecked, separators(0, 2) would answer none).
    let g = graph(3, &[(0, 1), (1, 2)]);
    let other = blocks(&graph(3, &[(0, 2), (2, 1)]));
    let _ = BlockCutForest::new(&g, &other);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "another graph's")]
fn the_forest_refuses_blocks_of_another_size() {
    let g = graph(3, &[(0, 1), (1, 2)]);
    let other = blocks(&graph(3, &[(0, 1)]));
    let _ = BlockCutForest::new(&g, &other);
}

#[test]
fn a_forest_node_out_of_range_panics_with_the_range() {
    // The path 0 – 1 – 2 – 3: three blocks and two cut vertices, five nodes.
    let g = graph(4, &[(0, 1), (1, 2), (2, 3)]);
    let f = BlockCutForest::new(&g, &blocks(&g));
    assert_eq!(f.node_count(), 5);
    let _ = f.depth(4);
    for e in [
        std::panic::catch_unwind(|| f.parent(5)).unwrap_err(),
        std::panic::catch_unwind(|| f.depth(5)).unwrap_err(),
    ] {
        assert_eq!(
            e.downcast_ref::<String>().unwrap(),
            "node 5 out of range 0..5"
        );
    }
}
