use super::*;
use crate::graphs::Digraph;
use crate::paths::naive;
use proptest::prelude::*;

fn network(n: usize, arrows: &[(u32, u32, i64)]) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), costs).unwrap()
}

/// The walk as release builds run it, the Assumes unchecked.
fn unchecked(net: &Network, start: u32) -> Distances {
    walk(net, start, None, None, |_, _, _, _, _| {})
}

/// A three-vertex map with one negative arrow: 0 → 1 costs 1, 0 → 2 costs 2, 2 → 1 costs −2.
fn probe() -> Network {
    network(3, &[(0, 1, 1), (0, 2, 2), (2, 1, -2)])
}

/// Five vertices: 0 → 1 (4), 0 → 2 (1), 2 → 1 (2), 1 → 3 (1), 2 → 3 (5), 3 → 4 (3).
fn five() -> Network {
    network(
        5,
        &[
            (0, 1, 4),
            (0, 2, 1),
            (2, 1, 2),
            (1, 3, 1),
            (2, 3, 5),
            (3, 4, 3),
        ],
    )
}

/// Every state of the walk from `start` passes `Valid` and `WellFormed`, judged against the
/// references.
fn every_state_valid(net: &Network, start: u32) -> Result<Vec<State>, TestCaseError> {
    let cheapest = naive::cheapest(net, start);
    let states = State::trace(net, start);
    for st in &states {
        let through = naive::cheapest_through(net, start, st.parts().0);
        prop_assert_eq!(st.check_valid(net, start, &cheapest, &through), Ok(()));
    }
    Ok(states)
}

#[test]
fn the_walk_settles_by_cost_and_lowers_a_known_cost_when_a_cheaper_arrow_comes() {
    // Lean: Ops.ReachedGetCheapest, Ops.PreviousGivesPath
    let net = five();
    let (d, settled) = dijkstra_with_settled(&net, 0);
    assert_eq!(settled, [0, 2, 1, 3, 4]);
    // 1 is known at 4 from 0, then at 3 from 2; 3 at 6 from 2, then at 4 from 1.
    assert_eq!(d.cost, [Some(0), Some(3), Some(1), Some(4), Some(7)]);
    assert_eq!(d.previous, [None, Some(2), Some(0), Some(1), Some(3)]);
    assert_eq!(d.path_to(4), Some(vec![0, 2, 1, 3, 4]));
    assert_eq!(dijkstra(&net, 0), d);
}

#[test]
fn of_two_arrows_between_the_same_vertices_the_cheaper_counts() {
    // Lean: Network.Cheapest, the two arrows from 0 to 1
    let net = network(2, &[(0, 1, 5), (0, 1, 3)]);
    assert_eq!(dijkstra(&net, 0).cost, [Some(0), Some(3)]);
    assert_eq!(dijkstra(&net, 1).cost, [None, Some(0)]);
    // The cheaper arrow first: the dearer one tried after it changes nothing.
    let net = network(2, &[(0, 1, 3), (0, 1, 5)]);
    let states = State::trace(&net, 0);
    assert_eq!(states.last().unwrap().parts().4, 2);
    assert_eq!(dijkstra(&net, 0).cost, [Some(0), Some(3)]);
}

#[test]
fn ties_go_to_the_lower_vertex_id_and_an_equal_cost_keeps_the_previous_vertex() {
    // Every arrow costs 1: 0 → 3, 0 → 2, 0 → 1, then 1 → 4, 2 → 4, 3 → 4.
    let net = network(
        5,
        &[
            (0, 3, 1),
            (0, 2, 1),
            (0, 1, 1),
            (3, 4, 1),
            (2, 4, 1),
            (1, 4, 1),
        ],
    );
    let (d, settled) = dijkstra_with_settled(&net, 0);
    assert_eq!(settled, [0, 1, 2, 3, 4]);
    // 4 is reached at 2 first from 1; 2 and 3 offer 2 again and change nothing.
    assert_eq!(d.previous, [None, Some(0), Some(0), Some(0), Some(1)]);
    assert_eq!(d.cost, [Some(0), Some(1), Some(1), Some(1), Some(2)]);
}

#[test]
fn zero_cost_arrows_loops_and_unreachable_vertices() {
    // Lean: Ops.UnreachedReported
    // A loop at 0, 0 → 1 free, 1 → 2 free, 3 → 0 never reached from 0.
    let net = network(4, &[(0, 0, 0), (0, 1, 0), (1, 2, 0), (3, 0, 1)]);
    let d = dijkstra(&net, 0);
    assert_eq!(d.cost, [Some(0), Some(0), Some(0), None]);
    assert_eq!(d.previous, [None, Some(0), Some(1), None]);
    assert_eq!(d.path_to(3), None);
    // A loop on the start is never tried: the start is settled before its row.
    let net = network(1, &[(0, 0, 0)]);
    assert_eq!(dijkstra(&net, 0).previous, [None]);
}

/// The arrows the walk has tried: those out of each settled vertex, in its row's order.
fn tried(net: &Network, st: &State) -> Vec<u32> {
    st.parts()
        .0
        .iter()
        .flat_map(|&v| net.graph().out(v as usize).ids.to_vec())
        .collect()
}

/// Each arrow tried once, and the queue given at most one entry per arrow tried and one for the
/// start.
fn each_arrow_tried_once(net: &Network, st: &State) -> bool {
    let mut ids = tried(net, st);
    let all = ids.len();
    ids.sort_unstable();
    ids.dedup();
    ids.len() == all && st.parts().4 <= all + 1
}

#[test]
fn every_state_of_the_walk_is_valid() {
    // Lean: Ops.emptyValid, Ops.stepKeeps (valid_start, valid_step)
    let states = every_state_valid(&five(), 0).unwrap();
    // One state at the start and one per entry taken off: 1 entry for 0, 2 for 1, 1 for 2, 2
    // for 3 and 1 for 4.
    assert_eq!(states.len(), 8);
    assert!(states.last().unwrap().parts().3.is_empty());
}

#[test]
fn each_arrow_is_tried_once_and_each_try_adds_at_most_one_entry() {
    // Lean: Contract.cost (dijkstra_cost), and pushed_final_le
    let net = five();
    let last = State::trace(&net, 0).pop().unwrap();
    assert_eq!(tried(&net, &last), [0, 1, 2, 4, 3, 5]);
    assert_eq!(last.parts().4, 7);
    assert!(each_arrow_tried_once(&net, &last));
    assert!(last.parts().4 <= net.graph().arrow_count() + 1);
}

#[test]
fn on_the_probe_the_walk_settles_vertex_1_at_the_wrong_cost() {
    // Lean: the Assumes' second sentence, on that three-vertex map
    let net = probe();
    // 0 settles and knows 1 at 1 and 2 at 2; 1 settles at 1; 2 settles and skips 2 → 1.
    let d = unchecked(&net, 0);
    assert_eq!(d.cost, [Some(0), Some(1), Some(2)]);
    assert_eq!(d.previous, [None, Some(0), Some(0)]);
    // 0 → 2 → 1 costs 0.
    let cheapest = naive::cheapest(&net, 0);
    assert_eq!(cheapest, [Some(0), Some(0), Some(2)]);
    // Vertex 1 is settled at 1 by the second state: the first box piece fails there.
    let states = State::trace(&net, 0);
    let st = &states[2];
    assert_eq!(st.parts().0, [0, 1]);
    let through = naive::cheapest_through(&net, 0, st.parts().0);
    assert_eq!(
        st.check_valid(&net, 0, &cheapest, &through),
        Err("invariant 1 (settled_are_cheapest)")
    );
    // Before, with only 0 settled, every piece holds.
    let through = naive::cheapest_through(&net, 0, states[1].parts().0);
    assert_eq!(states[1].check_valid(&net, 0, &cheapest, &through), Ok(()));
}

#[test]
fn on_the_four_vertex_map_the_frozen_vertex_and_the_one_after_it_are_wrong() {
    // 0 → 1 (1), 0 → 2 (2), 2 → 1 (−2), 1 → 3 (1). The cheapest: 1 at 0 and 3 at 1, through
    // 0 → 2 → 1. Freezing 1 at 1 gives 3 at 2; updating 1 to 0 without trying its arrows again
    // would also leave 3 at 2. Kept for reference: no negative arrow is the box's Assumes.
    let net = network(4, &[(0, 1, 1), (0, 2, 2), (2, 1, -2), (1, 3, 1)]);
    let (d, settled) = {
        let mut order = Vec::new();
        let d = walk(&net, 0, None, Some(&mut order), |_, _, _, _, _| {});
        (d, order)
    };
    assert_eq!(settled, [0, 1, 2, 3]);
    assert_eq!(d.cost, [Some(0), Some(1), Some(2), Some(2)]);
    assert_eq!(
        naive::cheapest(&net, 0),
        [Some(0), Some(0), Some(2), Some(1)]
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "an arrow costs less than nothing")]
fn debug_builds_refuse_an_arrow_below_zero() {
    let _ = dijkstra(&probe(), 0);
}

#[cfg(not(debug_assertions))]
#[test]
fn release_builds_take_an_arrow_below_zero_and_give_the_wrong_answer() {
    assert_eq!(dijkstra(&probe(), 0).cost, [Some(0), Some(1), Some(2)]);
}

#[test]
fn the_walk_to_a_goal_stops_when_the_goal_comes_off_the_queue() {
    let net = five();
    // 1 comes off third, after 0 and 2; its arrow to 3 is not tried.
    let d = dijkstra_to(&net, 0, 1);
    assert_eq!(d.cost, [Some(0), Some(3), Some(1), Some(6), None]);
    assert_eq!(d.path_to(1), Some(vec![0, 2, 1]));
    // The start is the goal: nothing is tried.
    assert_eq!(
        dijkstra_to(&net, 0, 0).cost,
        [Some(0), None, None, None, None]
    );
    // A goal out of reach: the walk runs to the end.
    assert_eq!(dijkstra_to(&net, 1, 0), dijkstra(&net, 1));
}

#[test]
#[should_panic(expected = "start 5 out of range 0..5")]
fn a_start_out_of_range_is_a_broken_contract() {
    let _ = dijkstra(&five(), 5);
}

#[test]
#[should_panic(expected = "goal 5 out of range 0..5")]
fn a_goal_out_of_range_is_a_broken_contract() {
    let _ = dijkstra_to(&five(), 0, 5);
}

#[test]
fn each_broken_state_names_its_piece() {
    // 0 → 1 (1), 1 → 2 (1), 0 → 2 (5), after settling 0.
    let net = network(3, &[(0, 1, 1), (1, 2, 1), (0, 2, 5)]);
    let cheapest = naive::cheapest(&net, 0);
    let through = naive::cheapest_through(&net, 0, &[0]);
    assert_eq!(cheapest, [Some(0), Some(1), Some(2)]);
    assert_eq!(through, [Some(0), Some(1), Some(5)]);
    let state = |settled: Vec<u32>, known: Vec<Option<i64>>, prev, queue| {
        State::from_parts(settled, known, prev, queue, 3)
    };
    let known = vec![Some(0), Some(1), Some(5)];
    let prev = vec![None, Some(0), Some(0)];
    let good = state(vec![0], known.clone(), prev.clone(), vec![(1, 1), (5, 2)]);
    assert_eq!(good.check_valid(&net, 0, &cheapest, &through), Ok(()));
    assert_eq!(State::trace(&net, 0)[1], good);

    // 0 settled twice.
    let twice = state(
        vec![0, 0],
        known.clone(),
        prev.clone(),
        vec![(1, 1), (5, 2)],
    );
    assert_eq!(
        twice.check_valid(&net, 0, &cheapest, &through),
        Err("invariant 1 (settled_are_cheapest)")
    );
    // 2 known at 6, above the arrow from 0.
    let dear = state(
        vec![0],
        vec![Some(0), Some(1), Some(6)],
        prev.clone(),
        vec![(1, 1), (6, 2)],
    );
    assert_eq!(
        dear.check_valid(&net, 0, &cheapest, &through),
        Err("invariant 2 (known_is_cheapest_through_settled)")
    );
    // The queue out of order.
    let jumbled = state(vec![0], known.clone(), prev.clone(), vec![(5, 2), (1, 1)]);
    assert_eq!(
        jumbled.check_valid(&net, 0, &cheapest, &through),
        Err("not in the box (queue_holds_known)")
    );
    // An entry for a vertex past the graph, its cost recorded past the vertices: the one piece
    // that reads the entry's vertex against the graph fails, and no other.
    let past = State::from_parts(
        vec![0],
        vec![Some(0), Some(1), Some(5), Some(9)],
        prev.clone(),
        vec![(1, 1), (5, 2), (9, 3)],
        4,
    );
    assert!(past.is_settled_are_cheapest(&net, &cheapest));
    assert!(past.is_known_is_cheapest_through_settled(&net, &through));
    assert!(past.is_start_settled_first(0));
    assert!(past.is_settled_rows_tried(&net));
    assert!(!past.is_queue_holds_known(&net));
    assert!(past.is_previous_leads_back(&net, 0));
    // 2 records 1, but 1 is not settled and 0 → 1 → 2 costs 2.
    let astray = state(
        vec![0],
        known.clone(),
        vec![None, Some(0), Some(1)],
        vec![(1, 1), (5, 2)],
    );
    assert_eq!(
        astray.check_valid(&net, 0, &cheapest, &through),
        Err("not in the box (previous_leads_back)")
    );

    // 0 ⇄ 1 free: 1 settled before the start.
    let net = network(2, &[(0, 1, 0), (1, 0, 0)]);
    let late = State::from_parts(
        vec![1, 0],
        vec![Some(0), Some(0)],
        vec![None, Some(0)],
        vec![],
        2,
    );
    let cheapest = naive::cheapest(&net, 0);
    let through = naive::cheapest_through(&net, 0, &[1, 0]);
    assert_eq!(
        late.check_valid(&net, 0, &cheapest, &through),
        Err("not in the box (start_settled_first)")
    );

    // 0 → 1 (0), 1 → 2 (0), 0 → 2 (5), 2 → 3 (1): 2 settled before 1, its arrow to 3 untried.
    let net = network(4, &[(0, 1, 0), (1, 2, 0), (0, 2, 5), (2, 3, 1)]);
    let settled = vec![0, 2];
    let cheapest = naive::cheapest(&net, 0);
    let through = naive::cheapest_through(&net, 0, &settled);
    assert_eq!(through, [Some(0), Some(0), Some(5), Some(6)]);
    let untried = State::from_parts(
        settled,
        vec![Some(0), Some(0), Some(0), Some(6)],
        vec![None, Some(0), Some(1), Some(2)],
        vec![(0, 1), (6, 3)],
        4,
    );
    assert_eq!(
        untried.check_valid(&net, 0, &cheapest, &through),
        Err("not in the box (settled_rows_tried)")
    );
}

#[test]
fn the_pieces_answer_false_on_parts_of_the_wrong_size() {
    let net = network(2, &[(0, 1, 1)]);
    let cheapest = naive::cheapest(&net, 0);
    let short = State::from_parts(vec![0, 7], vec![Some(0)], vec![], vec![(3, 9)], 1);
    assert!(!short.is_settled_are_cheapest(&net, &cheapest));
    assert!(!short.is_queue_holds_known(&net));
    assert!(!short.is_settled_rows_tried(&net));
    assert!(!short.is_valid(&net, 0, &cheapest, &[]));
}

/// A small network with no negative arrow: loops, doubled arrows and ties on every key come
/// often, since the costs are few.
fn networks() -> impl Strategy<Value = (Network, u32)> {
    (1usize..=6).prop_flat_map(|n| {
        let m = n as u32;
        (
            Just(n),
            prop::collection::vec((0..m, 0..m, 0i64..4), 0..11),
            0..m,
        )
            .prop_map(|(n, arrows, start)| (network(n, &arrows), start))
    })
}

proptest! {
    #[test]
    fn on_any_network_the_walk_gives_the_cheapest_costs_and_paths_of_those_costs(
        (net, start) in networks()
    ) {
        // Lean: Ops.ReachedGetCheapest, Ops.PreviousGivesPath, Ops.UnreachedReported
        let d = dijkstra(&net, start);
        prop_assert_eq!(&d.cost, &naive::cheapest(&net, start));
        let g = net.graph();
        for v in 0..g.n() as u32 {
            let Some(path) = d.path_to(v) else {
                prop_assert!(d.cost[v as usize].is_none());
                continue;
            };
            prop_assert_eq!(path[0], start);
            // The cheapest arrow of each hop: the path costs no less, so exactly the cost.
            let mut total = 0;
            for hop in path.windows(2) {
                let row = g.out(hop[0] as usize);
                let c = row
                    .iter()
                    .filter(|&(w, _)| w == hop[1])
                    .map(|(_, id)| net.arrow_cost(id as usize))
                    .min();
                prop_assert!(c.is_some());
                total += c.unwrap();
            }
            prop_assert_eq!(Some(total), d.cost[v as usize]);
        }
    }

    #[test]
    fn on_any_network_every_state_of_the_walk_is_valid((net, start) in networks()) {
        // Lean: Ops.emptyValid, Ops.stepKeeps (valid_start, valid_step); Contract.cost
        // (dijkstra_cost)
        let states = every_state_valid(&net, start)?;
        let last = states.last().unwrap();
        let (settled, known, previous, queue, pushed) = last.parts();
        prop_assert!(queue.is_empty());
        prop_assert!(each_arrow_tried_once(&net, last));
        prop_assert!(pushed <= net.graph().arrow_count() + 1);
        prop_assert_eq!(states.len(), pushed + 1);
        let (d, order) = dijkstra_with_settled(&net, start);
        prop_assert_eq!(settled, &order[..]);
        prop_assert_eq!(known, &d.cost[..]);
        prop_assert_eq!(previous, &d.previous[..]);
        // Settled in order of cost.
        prop_assert!(order.windows(2).all(|p| d.cost[p[0] as usize] <= d.cost[p[1] as usize]));
    }

    #[test]
    fn on_any_network_the_walk_to_a_goal_settles_a_prefix_and_gets_the_goal_right(
        (net, start) in networks(), goal in 0u32..6
    ) {
        let goal = goal % net.n() as u32;
        let (all, order) = dijkstra_with_settled(&net, start);
        let d = dijkstra_to(&net, start, goal);
        prop_assert_eq!(d.cost[goal as usize], all.cost[goal as usize]);
        prop_assert_eq!(d.path_to(goal), all.path_to(goal));
        match order.iter().position(|&v| v == goal) {
            // Every vertex settled before the goal has its final cost.
            Some(k) => {
                for &v in &order[..k] {
                    prop_assert_eq!(d.cost[v as usize], all.cost[v as usize]);
                }
            }
            None => prop_assert_eq!(&d, &all),
        }
    }
}
