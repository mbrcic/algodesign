use super::*;
use crate::graphs::Digraph;
use crate::paths::dijkstra::{dijkstra_to, walk_keyed};
use crate::paths::naive;
use proptest::prelude::*;

fn network(n: usize, arrows: &[(u32, u32, i64)]) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), costs).unwrap()
}

/// The Lean's map: 0 → 1 costs 1, 1 → 2 costs 1, 0 → 2 costs 3, 2 → 3 costs 5, 0 → 4 costs 1;
/// the goal is 3.
fn roads() -> Network {
    network(5, &[(0, 1, 1), (1, 2, 1), (0, 2, 3), (2, 3, 5), (0, 4, 1)])
}

/// The cheapest cost still to go from each vertex of `roads`, and 9 at 4, which reaches no goal.
const EXACT: [i64; 5] = [7, 6, 5, 0, 9];

/// Never above the cost still to go, but 1 → 2 costs 1 while the estimate drops by 5.
const OVEREAGER: [i64; 5] = [0, 5, 0, 0, 0];

/// The search and its settled order, the invariant unchecked, as release builds run it.
fn unchecked(net: &Network, start: u32, goal: u32, estimate: &[i64]) -> (Distances, Vec<u32>) {
    let mut order = Vec::new();
    let d = search(net, start, goal, estimate, Some(&mut order));
    (d, order)
}

/// Dijkstra's walk to `goal` and its settled order.
fn dijkstra_to_settled(net: &Network, start: u32, goal: u32) -> (Distances, Vec<u32>) {
    let mut order = Vec::new();
    let d = walk_keyed(
        net,
        start,
        Some(goal),
        |_| 0,
        Some(&mut order),
        |_, _, _, _, _| {},
    );
    (d, order)
}

/// Every state of the search passes `Valid` and `WellFormed`, judged against the references on the
/// changed costs.
fn every_state_valid(
    net: &Network,
    start: u32,
    goal: u32,
    estimate: &[i64],
) -> Result<Vec<State>, TestCaseError> {
    let on = changed(net, estimate).unwrap();
    let cheapest = naive::cheapest(&on, start);
    let states = trace(net, start, goal, estimate);
    for st in &states {
        let through = naive::cheapest_through(&on, start, st.parts().0);
        prop_assert_eq!(
            check_valid(net, start, goal, estimate, st, &cheapest, &through),
            Ok(())
        );
    }
    Ok(states)
}

#[test]
fn with_a_consistent_estimate_the_search_settles_only_the_path() {
    // Lean: AlgoDesignTests.PathsAStar, `exact`
    let net = roads();
    assert!(is_estimate_is_consistent(&net, 3, &EXACT));
    let (d, settled) = a_star_with_settled(&net, 0, 3, &EXACT).unwrap();
    assert_eq!(d.cost[3], Some(7));
    assert_eq!(naive::cheapest(&net, 0)[3], Some(7));
    assert_eq!((d.previous[3], d.previous[2]), (Some(2), Some(1)));
    assert_eq!(d.path_to(3), Some(vec![0, 1, 2, 3]));
    assert_eq!(settled, [0, 1, 2, 3]);
    assert_eq!(a_star(&net, 0, 3, &EXACT).unwrap(), d);
    // Dijkstra's walk to the goal settles 4 too.
    let (to, order) = dijkstra_to_settled(&net, 0, 3);
    assert_eq!(order, [0, 1, 4, 2, 3]);
    assert_eq!(to.cost[3], Some(7));
    assert_eq!(to, dijkstra_to(&net, 0, 3));
}

#[test]
fn every_state_of_the_search_on_the_map_is_valid() {
    // Lean: AlgoDesignTests.PathsAStar, `Valid` and `WellFormed` for the first four states;
    // Ops.emptyValid, Ops.stepKeeps
    let states = every_state_valid(&roads(), 0, 3, &EXACT).unwrap();
    // The start, then one state per entry taken off before the goal's: 0, 1, 2.
    assert_eq!(states.len(), 4);
    let (settled, known, _, queue, pushed) = states[3].parts();
    assert_eq!(settled, [0, 1, 2]);
    assert_eq!(known, [Some(0), Some(1), Some(2), Some(7), Some(1)]);
    // Each key is the known cost plus the estimate: 3 at 7 + 0, 4 at 1 + 9.
    assert_eq!(queue, [(7, 3), (8, 2), (10, 4)]);
    assert_eq!(pushed, 6);
}

#[test]
fn an_estimate_that_never_overstates_but_is_not_consistent_gives_a_dearer_path() {
    // Lean: AlgoDesignTests.PathsAStar, `overeager`; petgraph issue #378
    let net = roads();
    assert!(OVEREAGER
        .iter()
        .zip(EXACT)
        .take(4)
        .all(|(&low, exact)| low <= exact));
    assert!(!is_estimate_is_consistent(&net, 3, &OVEREAGER));
    // 2 is settled at 3 from the start before 1, and 1 → 2 is never tried.
    let (d, settled) = unchecked(&net, 0, 3, &OVEREAGER);
    assert_eq!(d.cost[3], Some(8));
    assert_eq!(d.path_to(3), Some(vec![0, 2, 3]));
    assert_eq!(settled, [0, 4, 2, 1, 3]);
    assert_eq!(naive::cheapest(&net, 0)[3], Some(7));
    // Every state names the box's invariant first.
    let on = changed(&net, &OVEREAGER).unwrap();
    let st = &trace(&net, 0, 3, &OVEREAGER)[0];
    let cheapest = naive::cheapest(&on, 0);
    let through = naive::cheapest_through(&on, 0, st.parts().0);
    assert_eq!(
        check_valid(&net, 0, 3, &OVEREAGER, st, &cheapest, &through),
        Err("invariant 1 (estimate_is_consistent)")
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "the estimate is not consistent")]
fn debug_builds_refuse_an_estimate_that_is_not_consistent() {
    let _ = a_star(&roads(), 0, 3, &OVEREAGER);
}

#[cfg(not(debug_assertions))]
#[test]
fn release_builds_take_an_estimate_that_is_not_consistent_and_give_the_wrong_answer() {
    assert_eq!(a_star(&roads(), 0, 3, &OVEREAGER).unwrap().cost[3], Some(8));
}

#[test]
fn the_zero_estimate_is_dijkstras_walk_to_the_goal() {
    // Lean: AlgoDesignTests.PathsAStar, `astar roads []`
    let net = roads();
    for goal in 0..5 {
        let (d, settled) = a_star_with_settled(&net, 0, goal, &[0; 5]).unwrap();
        assert_eq!((d, settled), dijkstra_to_settled(&net, 0, goal));
    }
}

#[test]
fn an_arrow_below_zero_is_fine_when_the_estimate_keeps_the_invariant() {
    // 0 → 1 costs −2, 1 → 2 costs 5, 0 → 2 costs 4; the estimate 3, 5, 0 drops by at most each
    // arrow, so every changed cost is at least zero: 0 → 1 costs 0, 1 → 2 costs 0, 0 → 2 costs 1.
    let net = network(3, &[(0, 1, -2), (1, 2, 5), (0, 2, 4)]);
    let estimate = [3, 5, 0];
    assert!(is_estimate_is_consistent(&net, 2, &estimate));
    assert_eq!(changed(&net, &estimate).unwrap().cost(), [0, 0, 1]);
    let d = a_star(&net, 0, 2, &estimate).unwrap();
    assert_eq!(d.cost[2], Some(3));
    assert_eq!(d.path_to(2), Some(vec![0, 1, 2]));
    every_state_valid(&net, 0, 2, &estimate).unwrap();
}

#[test]
fn on_a_grid_a_good_estimate_settles_fewer_vertices() {
    // Six by six, each step to a neighbor costs 1 both ways; from the top-left corner to the
    // top-right one, the estimate the steps left along the row and column.
    let side = 6u32;
    let id = |r: u32, c: u32| r * side + c;
    let mut arrows = Vec::new();
    for r in 0..side {
        for c in 0..side {
            if c + 1 < side {
                arrows.push((id(r, c), id(r, c + 1), 1));
                arrows.push((id(r, c + 1), id(r, c), 1));
            }
            if r + 1 < side {
                arrows.push((id(r, c), id(r + 1, c), 1));
                arrows.push((id(r + 1, c), id(r, c), 1));
            }
        }
    }
    let net = network((side * side) as usize, &arrows);
    let goal = id(0, side - 1);
    let estimate: Vec<i64> = (0..side * side)
        .map(|v| i64::from((v / side).abs_diff(0) + (v % side).abs_diff(side - 1)))
        .collect();
    assert!(is_estimate_is_consistent(&net, goal, &estimate));
    let (d, settled) = a_star_with_settled(&net, 0, goal, &estimate).unwrap();
    let (to, order) = dijkstra_to_settled(&net, 0, goal);
    assert_eq!(d.cost[goal as usize], Some(5));
    assert_eq!(to.cost[goal as usize], Some(5));
    assert_eq!(settled, [0, 1, 2, 3, 4, 5]);
    // Dijkstra settles every vertex within four steps of the corner, fifteen, then the goal.
    assert_eq!(order.len(), 16);
}

#[test]
fn the_start_is_the_goal_and_a_goal_out_of_reach() {
    let net = roads();
    // Nothing is tried: the start comes off first.
    let (d, settled) = a_star_with_settled(&net, 0, 0, &[0, 0, 0, 0, 0]).unwrap();
    assert_eq!(settled, [0]);
    assert_eq!(d.cost, [Some(0), None, None, None, None]);
    // 0 is out of reach from 3: the search runs to the empty queue.
    let (d, settled) = a_star_with_settled(&net, 3, 0, &[0; 5]).unwrap();
    assert_eq!(settled, [3]);
    assert_eq!(d.cost[0], None);
}

#[test]
fn an_estimate_of_the_wrong_length_is_an_error() {
    let net = roads();
    assert_eq!(
        a_star(&net, 0, 3, &[7, 6, 5, 0]),
        Err(PathsError::EstimateCountMismatch {
            estimates: 4,
            vertices: 5
        })
    );
    assert_eq!(
        a_star_with_settled(&net, 0, 3, &[0; 6]).map(|_| ()),
        Err(PathsError::EstimateCountMismatch {
            estimates: 6,
            vertices: 5
        })
    );
    assert_eq!(
        PathsError::EstimateCountMismatch {
            estimates: 4,
            vertices: 5
        }
        .to_string(),
        "4 estimates for 5 vertices: one estimate per vertex"
    );
}

#[test]
#[should_panic(expected = "goal 5 out of range 0..5")]
fn a_goal_out_of_range_is_a_broken_contract() {
    let _ = a_star(&roads(), 0, 5, &[0; 5]);
}

#[test]
#[should_panic(expected = "start 5 out of range 0..5")]
fn a_start_out_of_range_is_a_broken_contract() {
    let _ = a_star(&roads(), 5, 3, &EXACT);
}

#[test]
fn each_part_of_the_box_invariant_breaks_it_alone() {
    // Lean: EstimateIsConsistent, its three conjuncts
    let net = roads();
    assert!(!is_estimate_is_consistent(&net, 3, &[7, 6, 5, 0, -1]));
    assert!(!is_estimate_is_consistent(&net, 3, &[7, 6, 5, 1, 9]));
    assert!(!is_estimate_is_consistent(&net, 3, &[8, 6, 5, 0, 9]));
    // An estimate past the list counts as 0, as the Lean's: the empty one keeps the invariant.
    assert!(is_estimate_is_consistent(&net, 3, &[]));
    // Only the vertices' estimates are read.
    assert!(is_estimate_is_consistent(&net, 3, &[0, 0, 0, 0, 0, -1]));
}

#[test]
fn a_broken_state_names_the_piece_not_in_the_box() {
    let net = roads();
    let on = changed(&net, &EXACT).unwrap();
    let st = trace(&net, 0, 3, &EXACT).pop().unwrap();
    let cheapest = naive::cheapest(&on, 0);
    let through = naive::cheapest_through(&on, 0, st.parts().0);
    let (settled, known, previous, queue, pushed) = st.parts();
    // The key of 3 without its estimate is no longer the shifted walk's key.
    let mut wrong = queue.to_vec();
    wrong[0] = (6, 3);
    wrong.sort_unstable();
    let bad = State::from_parts(
        settled.to_vec(),
        known.to_vec(),
        previous.to_vec(),
        wrong,
        pushed,
    );
    assert_eq!(
        check_valid(&net, 0, 3, &EXACT, &bad, &cheapest, &through),
        Err("not in the box (walk_is_cheapest_paths_on_changed_costs)")
    );
    assert!(is_estimate_is_consistent(&net, 3, &EXACT));
    // A known cost or a changed cost leaving i64: the pieces answer false, never panic.
    let far = [0, i64::MAX, 0, 0, 0];
    assert!(changed(&net, &far).is_none());
    assert!(!is_walk_is_cheapest_paths_on_changed_costs(
        &net, 0, &far, &st, &cheapest, &through
    ));
    assert!(shifted(&st, &[0, 0, 0, 0, i64::MAX], -1).is_none());
}

#[test]
fn the_shifted_state_is_dijkstras_on_the_changed_costs() {
    // Lean: shifted_step, shifted_final
    let net = roads();
    let on = changed(&net, &EXACT).unwrap();
    let ours: Vec<State> = trace(&net, 0, 3, &EXACT)
        .iter()
        .map(|st| shifted(st, &EXACT, EXACT[0]).unwrap())
        .collect();
    assert_eq!(ours, State::trace_keyed(&on, 0, Some(3), |_| 0));
    assert_eq!(
        a_star(&net, 0, 3, &EXACT).unwrap().previous,
        dijkstra_to(&on, 0, 3).previous
    );
}

/// A small network with no negative arrow and a goal: loops, doubled arrows and ties come
/// often.
fn networks() -> impl Strategy<Value = (Network, u32, u32)> {
    (1usize..=6).prop_flat_map(|n| {
        let m = n as u32;
        (
            Just(n),
            prop::collection::vec((0..m, 0..m, 0i64..4), 0..11),
            0..m,
            0..m,
        )
            .prop_map(|(n, arrows, start, goal)| (network(n, &arrows), start, goal))
    })
}

/// A consistent estimate: the cheapest cost still to go scaled by `p / q` and rounded down, and
/// one shared value, at least every other, where the goal is out of reach.
fn scaled(net: &Network, goal: u32, p: i64, q: i64, far: i64) -> Vec<i64> {
    let to = naive::cheapest_to(net, goal);
    let top = to.iter().flatten().map(|&d| d * p / q).max().unwrap_or(0);
    to.iter()
        .map(|d| d.map_or(top + far, |d| d * p / q))
        .collect()
}

proptest! {
    #[test]
    fn on_any_network_the_goal_gets_its_cheapest_cost_and_a_path_of_that_cost(
        (net, start, goal) in networks(), p in 0i64..=4, far in 0i64..3
    ) {
        // Lean: Ops.GoalGetsCheapest, Ops.PreviousGivesPath, Ops.UnreachedReported
        let estimate = scaled(&net, goal, p, 4, far);
        prop_assert!(is_estimate_is_consistent(&net, goal, &estimate));
        let (d, settled) = a_star_with_settled(&net, start, goal, &estimate).unwrap();
        prop_assert_eq!(d.cost[goal as usize], naive::cheapest(&net, start)[goal as usize]);
        if let Some(path) = d.path_to(goal) {
            prop_assert_eq!(path[0], start);
            let g = net.graph();
            let mut total = 0;
            for hop in path.windows(2) {
                let c = g.out(hop[0] as usize).iter().filter(|&(w, _)| w == hop[1])
                    .map(|(_, id)| net.arrow_cost(id as usize)).min();
                prop_assert!(c.is_some());
                total += c.unwrap();
            }
            prop_assert_eq!(Some(total), d.cost[goal as usize]);
            prop_assert_eq!(settled.last(), Some(&goal));
        }
        // Contract.cost: each vertex settled at most once.
        let mut once = settled.clone();
        once.sort_unstable();
        once.dedup();
        prop_assert_eq!(once.len(), settled.len());
    }

    #[test]
    fn on_any_network_every_state_of_the_search_is_valid(
        (net, start, goal) in networks(), p in 0i64..=4, far in 0i64..3
    ) {
        // Lean: Ops.emptyValid, Ops.stepKeeps (valid_start, valid_step); Contract.cost
        // (final_counted)
        let estimate = scaled(&net, goal, p, 4, far);
        let states = every_state_valid(&net, start, goal, &estimate)?;
        let last = states.last().unwrap();
        let (settled, _, _, _, pushed) = last.parts();
        let tried: Vec<u32> = settled.iter()
            .flat_map(|&v| net.graph().out(v as usize).ids.to_vec()).collect();
        let mut distinct = tried.clone();
        distinct.sort_unstable();
        distinct.dedup();
        prop_assert_eq!(distinct.len(), tried.len());
        prop_assert!(pushed <= tried.len() + 1);
    }

    #[test]
    fn on_any_network_the_zero_estimate_settles_as_dijkstras_walk_to_the_goal(
        (net, start, goal) in networks()
    ) {
        let zero = vec![0; net.n()];
        let (d, settled) = a_star_with_settled(&net, start, goal, &zero).unwrap();
        prop_assert_eq!(&d, &dijkstra_to(&net, start, goal));
        prop_assert_eq!((d, settled), dijkstra_to_settled(&net, start, goal));
    }
}
