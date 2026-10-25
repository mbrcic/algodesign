use super::*;
use crate::graphs::naive;
use proptest::prelude::*;

fn graph(n: usize, arrows: &[(u32, u32)]) -> Digraph {
    Digraph::new(n, arrows).unwrap()
}

fn stuck(vertices: &[u32]) -> Stuck {
    Stuck {
        vertices: vertices.to_vec(),
    }
}

fn cycle(vertices: &[u32]) -> Cycle {
    Cycle {
        vertices: vertices.to_vec(),
    }
}

/// Six vertices: 5 → 0, 5 → 2, 4 → 0, 4 → 1, 2 → 3, 3 → 1.
const SIX: [(u32, u32); 6] = [(5, 0), (5, 2), (4, 0), (4, 1), (2, 3), (3, 1)];

#[test]
fn kahn_places_the_sources_first_then_each_vertex_as_its_count_reaches_zero() {
    // Queue 4, 5; 4 lowers 0 and 1; 5 frees 0, then 2; 0; 2 frees 3; 3 frees 1.
    assert_eq!(
        topological_order(&graph(6, &SIX)),
        Ok(vec![4, 5, 0, 2, 3, 1])
    );
}

#[test]
fn dfs_order_is_the_reverse_finishing_order_from_vertex_0_upward() {
    // Finishing: 0, 1, then 3 and 2 (from 2 by 3, which finds 1 finished), 4, 5.
    assert_eq!(dfs_order(&graph(6, &SIX)), Ok(vec![5, 4, 2, 3, 1, 0]));
}

#[test]
fn each_method_gives_an_order_the_other_cannot() {
    // Two sources into one vertex. Kahn queues the sources from vertex 0 upward, so 0 comes first;
    // the search finishes root 0 before it starts root 1, so 1 comes first.
    let g = graph(3, &[(0, 2), (1, 2)]);
    assert_eq!(topological_order(&g), Ok(vec![0, 1, 2]));
    assert_eq!(dfs_order(&g), Ok(vec![1, 0, 2]));
}

#[test]
fn the_search_marks_a_vertex_when_it_enters_it() {
    // 0 → 1, 0 → 2, 2 → 1. A search that marks every neighbour as it stacks it finishes 2 before
    // 1 and answers 0, 1, 2, which breaks 2 → 1; marking on entry reaches 1 first from 0 and
    // answers 0, 2, 1.
    let arrows = [(0, 1), (0, 2), (2, 1)];
    let g = graph(3, &arrows);
    assert_eq!(dfs_order(&g), Ok(vec![0, 2, 1]));
    assert!(!naive::is_topological_order(3, &arrows, &[0, 1, 2]));
    assert_eq!(topological_order(&g), Ok(vec![0, 2, 1]));
}

#[test]
fn doubled_arrows_count_twice_and_go_forward_once() {
    let g = graph(3, &[(0, 1), (0, 1), (1, 2), (0, 2)]);
    assert_eq!(topological_order(&g), Ok(vec![0, 1, 2]));
    assert_eq!(dfs_order(&g), Ok(vec![0, 1, 2]));
}

#[test]
fn a_cycle_with_a_follower_leaves_all_three_stuck() {
    // A ↔ B → C: C waits on B, which never comes free.
    let g = graph(3, &[(0, 1), (1, 0), (1, 2)]);
    assert_eq!(topological_order(&g), Err(stuck(&[0, 1, 2])));
    assert_eq!(dfs_order(&g), Err(cycle(&[0, 1, 0])));
}

#[test]
fn a_loop_makes_its_vertex_wait_on_itself() {
    // 2 → 0 → 1 with a loop at 1: 2 and 0 are placed, 1 is stuck.
    let g = graph(3, &[(0, 1), (1, 1), (2, 0)]);
    assert_eq!(topological_order(&g), Err(stuck(&[1])));
    assert_eq!(dfs_order(&g), Err(cycle(&[1, 1])));
}

#[test]
fn the_cycle_runs_from_the_vertex_the_back_arrow_enters() {
    // 3 → 0 → 1 → 2 → 0: the search enters 0, 1, 2, and 2 → 0 closes the cycle.
    let g = graph(4, &[(0, 1), (1, 2), (2, 0), (3, 0)]);
    assert_eq!(dfs_order(&g), Err(cycle(&[0, 1, 2, 0])));
    // Entered from a vertex before it: 0 → 1 → 2 → 3 → 1 gives 1, 2, 3, 1.
    let g = graph(4, &[(0, 1), (1, 2), (2, 3), (3, 1)]);
    assert_eq!(dfs_order(&g), Err(cycle(&[1, 2, 3, 1])));
    assert_eq!(topological_order(&g), Err(stuck(&[1, 2, 3])));
}

#[test]
fn an_arrow_to_a_finished_vertex_closes_nothing() {
    // 0 → 1 and 2 → 1: when root 2 reaches 1, 1 is finished, not on the stack.
    assert_eq!(dfs_order(&graph(3, &[(0, 1), (2, 1)])), Ok(vec![2, 0, 1]));
}

#[test]
fn no_vertices_and_vertices_with_no_arrows() {
    assert_eq!(topological_order(&graph(0, &[])), Ok(vec![]));
    assert_eq!(dfs_order(&graph(0, &[])), Ok(vec![]));
    assert_eq!(topological_order(&graph(3, &[])), Ok(vec![0, 1, 2]));
    assert_eq!(dfs_order(&graph(3, &[])), Ok(vec![2, 1, 0]));
}

#[test]
fn the_checkers_reject_what_they_should() {
    let arrows = [(0, 1), (1, 0), (1, 2)];
    // The bare cycle {0, 1} is not the stuck set: 2 waits on it too.
    assert!(naive::is_stuck(3, &arrows, &[0, 1, 2]));
    assert!(!naive::is_stuck(3, &arrows, &[0, 1]));
    assert!(!naive::is_stuck(3, &arrows, &[1, 0, 2]));
    assert!(!naive::is_stuck(3, &arrows, &[]));
    // 2 alone waits on a vertex outside it.
    assert!(!naive::is_stuck(3, &[(0, 1), (1, 2)], &[2]));
    assert!(naive::is_cycle(3, &arrows, &[0, 1, 0]));
    assert!(!naive::is_cycle(3, &arrows, &[0, 1]));
    assert!(!naive::is_cycle(3, &arrows, &[0, 1, 0, 1, 0]));
    assert!(!naive::is_cycle(3, &arrows, &[1, 2, 1]));
    assert!(!naive::is_cycle(3, &arrows, &[0]));
    assert!(!naive::is_topological_order(3, &[], &[0, 1]));
    assert!(!naive::is_topological_order(3, &[], &[0, 1, 1]));
    assert!(!naive::is_topological_order(1, &[(0, 0)], &[0]));
    assert!(naive::has_cycle(1, &[(0, 0)]));
    assert!(!naive::has_cycle(3, &[(0, 1), (0, 1), (1, 2)]));
}

/// A path through `n` vertices, `0 → 1 → … → n - 1`, closed back to 0 when `closed`.
fn long(n: u32, closed: bool) -> Vec<(u32, u32)> {
    let mut arrows: Vec<(u32, u32)> = (1..n).map(|v| (v - 1, v)).collect();
    if closed {
        arrows.push((n - 1, 0));
    }
    arrows
}

#[test]
fn a_path_of_a_million_vertices_runs_on_a_small_stack() {
    // 256 KiB: any frame per vertex on the call stack would overflow it.
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let n = 1_000_000u32;
            let g = graph(n as usize, &long(n, false));
            let along: Vec<u32> = (0..n).collect();
            assert_eq!(dfs_order(&g).unwrap(), along);
            assert_eq!(topological_order(&g).unwrap(), along);
            let g = graph(n as usize, &long(n, true));
            let mut around = along.clone();
            around.push(0);
            assert_eq!(dfs_order(&g), Err(Cycle { vertices: around }));
            assert_eq!(topological_order(&g), Err(Stuck { vertices: along }));
        })
        .expect("spawning a thread")
        .join()
        .expect("the body panicked");
}

/// A number of vertices and some arrows between them, loops and doubled arrows included.
fn graphs() -> impl Strategy<Value = (usize, Vec<(u32, u32)>)> {
    (1usize..=8).prop_flat_map(|n| {
        let m = n as u32;
        (Just(n), prop::collection::vec((0..m, 0..m), 0..16))
    })
}

/// A graph with no cycle: arrows from a smaller to a larger number, the vertices then renamed by a
/// shuffle so the order is not just the numbering.
fn acyclic() -> impl Strategy<Value = (usize, Vec<(u32, u32)>)> {
    (1usize..=8)
        .prop_flat_map(|n| {
            let m = n as u32;
            let names = Just((0..m).collect::<Vec<u32>>()).prop_shuffle();
            (Just(n), prop::collection::vec((0..m, 0..m), 0..20), names)
        })
        .prop_map(|(n, pairs, names)| {
            let arrows = pairs
                .into_iter()
                .filter(|&(a, b)| a != b)
                .map(|(a, b)| (names[a.min(b) as usize], names[a.max(b) as usize]))
                .collect();
            (n, arrows)
        })
}

/// Both methods answer an order exactly when the plain search finds no cycle, and every answer
/// passes its checker.
fn both_answer_as_the_checkers(n: usize, arrows: &[(u32, u32)]) -> Result<(), TestCaseError> {
    let g = graph(n, arrows);
    let cyclic = naive::has_cycle(n, arrows);
    match topological_order(&g) {
        Ok(order) => {
            prop_assert!(!cyclic);
            prop_assert!(naive::is_topological_order(n, arrows, &order));
        }
        Err(Stuck { vertices }) => {
            prop_assert!(cyclic);
            prop_assert!(naive::is_stuck(n, arrows, &vertices));
        }
    }
    match dfs_order(&g) {
        Ok(order) => {
            prop_assert!(!cyclic);
            prop_assert!(naive::is_topological_order(n, arrows, &order));
        }
        Err(Cycle { vertices }) => {
            prop_assert!(cyclic);
            prop_assert!(naive::is_cycle(n, arrows, &vertices));
        }
    }
    Ok(())
}

proptest! {
    #[test]
    fn on_any_graph_each_answer_passes_its_checker((n, arrows) in graphs()) {
        both_answer_as_the_checkers(n, &arrows)?;
    }

    #[test]
    fn on_a_graph_with_no_cycle_both_give_an_order((n, arrows) in acyclic()) {
        prop_assert!(!naive::has_cycle(n, &arrows));
        both_answer_as_the_checkers(n, &arrows)?;
    }
}

#[test]
fn every_state_of_kahns_walk_is_valid_and_the_walk_takes_one_step_per_vertex() {
    // Lean: valid_start, valid_step
    let g = graph(6, &SIX);
    let states = KahnState::trace(&g);
    assert_eq!(states.len(), 7);
    assert!(states.iter().all(|st| st.is_valid(&g)));
    // A ↔ B → C: nothing is ever ready, so the walk stops at its start.
    let stuck = graph(3, &[(0, 1), (1, 0), (1, 2)]);
    let states = KahnState::trace(&stuck);
    assert_eq!(states.len(), 1);
    assert!(states[0].is_valid(&stuck));
}

#[test]
fn each_broken_kahn_state_names_its_piece() {
    // 0 → 1 → 2 and 0 → 2, after placing 0: placed [0], queue [1], counts 1 waits 0, 2 waits 1.
    let g = graph(3, &[(0, 1), (1, 2), (0, 2)]);
    let good = KahnState::from_parts(vec![0, 1], 1, vec![0, 0, 1]);
    assert_eq!(good.check_valid(&g), Ok(()));
    // 1 placed before 0, which it waits for.
    let early = KahnState::from_parts(vec![1, 0], 2, vec![0, 0, 1]);
    assert_eq!(
        early.check_valid(&g),
        Err("invariant 1 (placed_after_waits)")
    );
    // 2's count still holds the arrow from 0, which is placed.
    let stale = KahnState::from_parts(vec![0, 1], 1, vec![0, 0, 2]);
    assert_eq!(
        stale.check_valid(&g),
        Err("invariant 2 (counts_unplaced_waits)")
    );
    // 1 is ready but not queued.
    let lost = KahnState::from_parts(vec![0], 1, vec![0, 0, 1]);
    assert_eq!(lost.check_valid(&g), Err("invariant 3 (ready_is_zero)"));
    // 1 queued twice.
    let twice = KahnState::from_parts(vec![0, 1, 1], 1, vec![0, 0, 1]);
    assert_eq!(twice.check_valid(&g), Err("invariant 3 (ready_is_zero)"));
}

proptest! {
    #[test]
    fn on_any_graph_every_state_of_kahns_walk_is_valid((n, arrows) in graphs()) {
        let g = graph(n, &arrows);
        let states = KahnState::trace(&g);
        prop_assert!(states.len() <= n + 1);
        for st in &states {
            prop_assert_eq!(st.check_valid(&g), Ok(()));
        }
    }
}

#[test]
fn stuck_and_cycle_are_errors_that_name_their_vertices() {
    let g = graph(3, &[(0, 1), (1, 0), (1, 2)]);
    let run = || -> Result<(), Box<dyn std::error::Error>> {
        topological_order(&g)?;
        Ok(())
    };
    assert_eq!(
        run().unwrap_err().to_string(),
        "no order: vertices [0, 1, 2] wait forever"
    );
    let run = || -> Result<(), Box<dyn std::error::Error>> {
        dfs_order(&g)?;
        Ok(())
    };
    assert_eq!(
        run().unwrap_err().to_string(),
        "no order: the cycle [0, 1, 0]"
    );
}
