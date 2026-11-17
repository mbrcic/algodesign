use super::*;
use crate::paths::{dijkstra, naive, Network};
use proptest::prelude::*;

fn graph(n: usize, arrows: &[(u32, u32)]) -> Digraph {
    Digraph::new(n, arrows).unwrap()
}

#[test]
fn each_vertex_gets_its_fewest_arrows_and_the_vertex_it_was_found_from() {
    // 0 → 1 → 3, 0 → 2 → 3, 3 → 4; 5 out of reach.
    let g = graph(6, &[(0, 1), (1, 3), (0, 2), (2, 3), (3, 4)]);
    let d = bfs(&g, 0);
    assert_eq!(d.cost, [Some(0), Some(1), Some(1), Some(2), Some(3), None]);
    // 3 is found from 1, the first of 1 and 2 to leave the queue.
    assert_eq!(d.previous, [None, Some(0), Some(0), Some(1), Some(3), None]);
    assert_eq!(d.path_to(4), Some(vec![0, 1, 3, 4]));
    assert_eq!(d.path_to(5), None);
}

#[test]
fn a_vertex_is_marked_when_first_found_not_when_it_leaves() {
    // 0 → 1, 0 → 2, 1 → 2. Marking on leaving would let 1 → 2 record 1 as 2's previous vertex.
    let g = graph(3, &[(0, 1), (0, 2), (1, 2)]);
    let d = bfs(&g, 0);
    assert_eq!(d.previous, [None, Some(0), Some(0)]);
}

#[test]
fn loops_and_doubled_arrows_change_nothing() {
    let g = graph(3, &[(0, 0), (0, 1), (0, 1), (1, 1), (1, 2)]);
    let d = bfs(&g, 0);
    assert_eq!(d.cost, [Some(0), Some(1), Some(2)]);
    assert_eq!(d.previous, [None, Some(0), Some(1)]);
}

#[test]
fn the_start_is_any_vertex_and_arrows_only_go_forward() {
    let g = graph(3, &[(0, 1), (1, 2)]);
    let d = bfs(&g, 1);
    assert_eq!(d.cost, [None, Some(0), Some(1)]);
}

#[test]
fn a_loop_a_link_back_to_the_start_and_an_unreachable_vertex() {
    // Lean: AlgoDesignTests.PathsBfs, `gA`
    let g = graph(4, &[(0, 1), (1, 2), (0, 2), (2, 2), (2, 0)]);
    let d = bfs(&g, 0);
    assert_eq!(d.cost, [Some(0), Some(1), Some(1), None]);
    // 2 is found first from 0, along the arrow 0 → 2, not later from 1.
    assert_eq!(d.previous, [None, Some(0), Some(0), None]);
}

#[test]
fn two_paths_of_two_arrows_to_3_then_one_more_to_4() {
    // Lean: AlgoDesignTests.PathsBfs, `gB`
    let g = graph(5, &[(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (1, 1)]);
    let d = bfs(&g, 0);
    assert_eq!(d.cost, [Some(0), Some(1), Some(1), Some(2), Some(3)]);
}

#[test]
#[should_panic(expected = "start 3 out of range 0..3")]
fn a_start_out_of_range_is_a_broken_contract() {
    let _ = bfs(&graph(3, &[]), 3);
}

/// A number of vertices and some arrows between them, loops and doubled arrows included.
fn graphs() -> impl Strategy<Value = (usize, Vec<(u32, u32)>)> {
    (1usize..=7).prop_flat_map(|n| {
        let m = n as u32;
        (Just(n), prop::collection::vec((0..m, 0..m), 0..14))
    })
}

proptest! {
    #[test]
    fn bfs_gives_the_fewest_arrows_and_dijkstra_on_unit_costs_agrees((n, arrows) in graphs()) {
        // Lean: Bfs.bfs_reached, Bfs.bfs_unreached (against `naive`), Bfs.bfs_previous (the paths)
        let g = graph(n, &arrows);
        let net = Network::new(g.clone(), vec![1; arrows.len()]).unwrap();
        let d = bfs(&g, 0);
        prop_assert_eq!(&d.cost, &naive::cheapest(&net, 0));
        prop_assert_eq!(&d.cost, &dijkstra(&net, 0).cost);
        for v in 0..n as u32 {
            if let Some(path) = d.path_to(v) {
                prop_assert_eq!(path.len() as i64 - 1, d.cost[v as usize].unwrap());
                for hop in path.windows(2) {
                    prop_assert!(arrows.contains(&(hop[0], hop[1])));
                }
            }
        }
    }
}
