use super::*;
use crate::graphs::Digraph;
use crate::paths::{dijkstra, naive};
use proptest::prelude::*;

fn network(n: usize, arrows: &[(u32, u32, i64)]) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), costs).unwrap()
}

/// A three-vertex map with one negative arrow: 0 → 1 costs 1, 0 → 2 costs 2, 2 → 1 costs −2.
fn probe() -> Network {
    network(3, &[(0, 1, 1), (0, 2, 2), (2, 1, -2)])
}

/// `check_valid` with the answers about paths it needs: the costs of every path of at most
/// `naive::walk_arrows_after` arrows, of at most the tried arrows, and the cheapest over paths of
/// at most the rounds arrows.
fn check(net: &Network, start: u32, st: &State) -> Result<(), &'static str> {
    let (_, _, rounds, _, tried) = st.parts();
    let walks = naive::walk_costs(net, start, naive::walk_arrows_after(net, tried));
    let within = naive::walk_costs(net, start, tried);
    let cheapest = &naive::cheapest_walks(net, start, rounds)[rounds];
    st.check_valid(net, start, &walks, &within, cheapest)
}

/// Every state of the rounds from `start` passes `Valid` and `WellFormed`, the `k`-th after `k`
/// rounds.
fn every_state_valid(net: &Network, start: u32) -> Result<Vec<State>, TestCaseError> {
    let states = State::trace(net, start);
    for (k, st) in states.iter().enumerate() {
        prop_assert_eq!(check(net, start, st), Ok(()));
        prop_assert_eq!(st.parts().2, k);
    }
    Ok(states)
}

/// The cost of a path's vertices, taking the cheapest arrow of each hop; `None` if a hop has no
/// arrow.
fn cheapest_hops(net: &Network, path: &[u32]) -> Option<i64> {
    path.windows(2)
        .map(|hop| {
            net.graph()
                .out(hop[0] as usize)
                .iter()
                .filter(|&(w, _)| w == hop[1])
                .map(|(_, id)| net.arrow_cost(id as usize))
                .min()
        })
        .sum()
}

#[test]
fn on_the_probe_vertex_1_costs_0_through_vertex_2() {
    // Lean: Ops.NoCycleGivesCheapest, on that three-vertex map
    let net = probe();
    let d = bellman_ford(&net, 0).unwrap();
    assert_eq!(d.cost, [Some(0), Some(0), Some(2)]);
    assert_eq!(d.previous, [None, Some(2), Some(0)]);
    assert_eq!(d.path_to(1), Some(vec![0, 2, 1]));
    // Round 1 reaches 1 at 1 and 2 at 2, and then, from 2's new cost, lowers 1 to 0; round 2
    // lowers nothing.
    let (same, rounds, tried) = bellman_ford_with_rounds(&net, 0);
    assert_eq!(same, Ok(d));
    assert_eq!((rounds, tried), (2, 6));
    let states = every_state_valid(&net, 0).unwrap();
    let costs: Vec<&[Option<i64>]> = states.iter().map(|st| st.parts().0).collect();
    assert_eq!(
        costs,
        [
            &[Some(0), None, None][..],
            &[Some(0), Some(0), Some(2)],
            &[Some(0), Some(0), Some(2)],
        ]
    );
    let lowered: Vec<Option<u32>> = states.iter().map(|st| st.parts().3).collect();
    assert_eq!(lowered, [None, Some(1), None]);
}

#[test]
fn a_cost_lowered_earlier_in_the_round_is_used_later_in_it() {
    // 0 → 1 then 1 → 2: in the first round 1 gets its cost before its row is tried, so 2 is
    // reached in the same round.
    let net = network(3, &[(0, 1, 1), (1, 2, 1)]);
    let states = State::trace(&net, 0);
    assert_eq!(states[1].parts().0, [Some(0), Some(1), Some(2)]);
    // Every arrow counts as a try, also out of a vertex with no cost: 2 → 1 is tried each round.
    let net = network(3, &[(0, 1, 1), (2, 1, 1)]);
    assert_eq!(State::trace(&net, 0)[1].parts().4, 2);
    assert_eq!(bellman_ford_with_rounds(&net, 0).1, 2);
}

#[test]
fn in_place_the_rounds_differ_from_round_by_round() {
    // 0 → 1 costs 4, 0 → 2 costs 2, 2 → 1 costs −3, 1 → 3 costs 1, 2 → 3 costs 5. Round 1 tries
    // 2 → 1 with 2's new cost, so 1 costs −1 after it, where a round reading only the last
    // round's costs would leave 4, the cheapest over paths of one arrow.
    let net = network(4, &[(0, 1, 4), (0, 2, 2), (2, 1, -3), (1, 3, 1), (2, 3, 5)]);
    let states = every_state_valid(&net, 0).unwrap();
    let costs: Vec<&[Option<i64>]> = states.iter().map(|st| st.parts().0).collect();
    assert_eq!(
        costs,
        [
            &[Some(0), None, None, None][..],
            &[Some(0), Some(-1), Some(2), Some(5)],
            &[Some(0), Some(-1), Some(2), Some(0)],
            &[Some(0), Some(-1), Some(2), Some(0)],
        ]
    );
    assert_eq!(
        naive::cheapest_walks(&net, 0, 1)[1],
        [Some(0), Some(4), Some(2), None]
    );
    let (_, rounds, tried) = bellman_ford_with_rounds(&net, 0);
    assert_eq!((rounds, tried), (3, 15));
}

#[test]
fn a_loop_that_lowers_its_vertex_is_read_by_the_rest_of_its_row() {
    // 0 → 0 costs −1, then 0 → 1 costs 0: the loop lowers 0 to −1 first, and 0 → 1 reads that.
    let net = network(2, &[(0, 0, -1), (0, 1, 0)]);
    let states = State::trace(&net, 0);
    assert_eq!(states[1].parts().0, [Some(-1), Some(-1)]);
    assert!(every_state_valid(&net, 0).is_ok());
}

#[test]
fn the_rounds_stop_after_the_first_that_lowers_nothing() {
    // Lean: Contract.cost
    // Five vertices, one arrow: round 1 reaches 1, round 2 is the check; no round after it.
    let net = network(5, &[(0, 1, 5)]);
    let (d, rounds, tried) = bellman_ford_with_rounds(&net, 0);
    assert_eq!(d.unwrap().cost, [Some(0), Some(5), None, None, None]);
    assert_eq!((rounds, tried), (2, 2));
    assert_eq!(State::trace(&net, 0).len(), 3);
    // No arrow at all: the first round is the check.
    let net = network(2, &[]);
    assert_eq!(bellman_ford_with_rounds(&net, 1).1, 1);
}

#[test]
fn an_equal_cost_keeps_the_previous_vertex() {
    // 0 → 1, 0 → 2, 1 → 3, 2 → 3, each costing 1: 3 is reached from 1 first, and 2 offers the
    // same cost.
    let net = network(4, &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)]);
    let d = bellman_ford(&net, 0).unwrap();
    assert_eq!(d.cost, [Some(0), Some(1), Some(1), Some(2)]);
    assert_eq!(d.previous, [None, Some(0), Some(0), Some(1)]);
}

#[test]
fn of_two_arrows_between_the_same_vertices_the_cheaper_counts() {
    // Lean: Network.Cheapest, the two arrows from 0 to 1
    for costs in [[5, -3], [-3, 5]] {
        let net = network(2, &[(0, 1, costs[0]), (0, 1, costs[1])]);
        let d = bellman_ford(&net, 0).unwrap();
        assert_eq!(d.cost, [Some(0), Some(-3)]);
        assert_eq!(d.previous, [None, Some(0)]);
    }
}

#[test]
fn a_loop_below_zero_is_a_cycle_of_one_arrow() {
    // Lean: Ops.CycleIsBelowZero
    let net = network(2, &[(0, 1, 1), (1, 1, -1)]);
    let c = bellman_ford(&net, 0).unwrap_err();
    assert_eq!(c.vertices, [1, 1]);
    assert!(naive::is_cycle_below_zero(&net, 0, &c.vertices));
    // On the start itself.
    let net = network(1, &[(0, 0, -1)]);
    assert_eq!(bellman_ford(&net, 0).unwrap_err().vertices, [0, 0]);
    // A loop of cost 0 lowers nothing.
    let net = network(1, &[(0, 0, 0)]);
    let d = bellman_ford(&net, 0).unwrap();
    assert_eq!((d.cost, d.previous), (vec![Some(0)], vec![None]));
}

#[test]
fn a_cycle_below_zero_the_start_reaches_is_the_answer() {
    // Lean: Ops.CycleWhenOneExists, Ops.CycleIsBelowZero
    // 0 → 1 (1), 1 → 2 (−3), 2 → 1 (2): 1 → 2 → 1 totals −1. Round 3 lowers 1 last; three steps
    // back from 1 is 2, and from 2 the records lead round to 2 again.
    let net = network(3, &[(0, 1, 1), (1, 2, -3), (2, 1, 2)]);
    let (c, rounds, tried) = bellman_ford_with_rounds(&net, 0);
    assert_eq!(c.unwrap_err().vertices, [2, 1, 2]);
    assert_eq!((rounds, tried), (3, 9));
    // A tail after the cycle: 2 → 3 is lowered last in each round, and the n steps back reach
    // the cycle.
    let net = network(4, &[(0, 1, 1), (1, 2, -3), (2, 1, 2), (2, 3, 0)]);
    let c = bellman_ford(&net, 0).unwrap_err();
    assert!(naive::is_cycle_below_zero(&net, 0, &c.vertices));
    assert_eq!(*c.vertices.first().unwrap(), *c.vertices.last().unwrap());
}

#[test]
fn a_cycle_below_zero_the_start_does_not_reach_changes_nothing() {
    // 2 → 3 (−5) and 3 → 2 (1) total −4, but nothing leads from 0 to them.
    let net = network(4, &[(0, 1, 1), (2, 3, -5), (3, 2, 1), (2, 0, 1)]);
    assert!(!naive::reaches_cycle_below_zero(&net, 0));
    let d = bellman_ford(&net, 0).unwrap();
    assert_eq!(d.cost, [Some(0), Some(1), None, None]);
    // From 2 it is reached.
    assert!(naive::reaches_cycle_below_zero(&net, 2));
    assert!(bellman_ford(&net, 2).is_err());
}

#[test]
#[should_panic(expected = "start 3 out of range 0..3")]
fn a_start_out_of_range_is_a_broken_contract() {
    let _ = bellman_ford(&probe(), 3);
}

/// The labels of every piece `st` fails, not only the first.
fn failing(net: &Network, start: u32, st: &State) -> Vec<&'static str> {
    let (_, _, rounds, _, tried) = st.parts();
    let walks = naive::walk_costs(net, start, naive::walk_arrows_after(net, tried));
    let within = naive::walk_costs(net, start, tried);
    let cheapest = &naive::cheapest_walks(net, start, rounds)[rounds];
    let pieces = [
        st.is_cost_is_walk_at_most_cheapest(net, &walks, cheapest),
        st.is_path_within_tries(net, &within),
        st.is_previous_arrow_fits(net),
        st.is_recorded_cycles_below_zero(net),
        st.is_no_previous_keeps_start(net, start),
    ];
    LABELS
        .iter()
        .zip(pieces)
        .filter(|&(_, ok)| !ok)
        .map(|(label, _)| *label)
        .collect()
}

#[test]
fn each_broken_state_names_its_piece_and_fails_it_alone() {
    // 0 → 1 (1), 1 → 2 (1), 0 → 2 (5), after one round: 2 is lowered to 2 from 1's new cost.
    let net = network(3, &[(0, 1, 1), (1, 2, 1), (0, 2, 5)]);
    let good = State::from_parts(
        vec![Some(0), Some(1), Some(2)],
        vec![None, Some(0), Some(1)],
        1,
        Some(2),
        3,
    );
    assert_eq!(check(&net, 0, &good), Ok(()));
    assert_eq!(State::trace(&net, 0)[1], good);
    let st = |cost: Vec<Option<i64>>, prev: Vec<Option<u32>>, rounds| {
        State::from_parts(cost, prev, rounds, Some(2), 3 * rounds)
    };

    // After two rounds 2 still at 5, though 0 → 1 → 2 costs 2.
    let dear = st(
        vec![Some(0), Some(1), Some(5)],
        vec![None, Some(0), Some(0)],
        2,
    );
    assert_eq!(
        failing(&net, 0, &dear),
        ["invariant 1 (cost_is_walk_at_most_cheapest)"]
    );
    // 1 records 2, but no arrow leads from 2 to 1.
    let astray = st(
        vec![Some(0), Some(1), Some(5)],
        vec![None, Some(2), Some(0)],
        1,
    );
    assert_eq!(
        failing(&net, 0, &astray),
        ["not in the box (previous_arrow_fits)"]
    );
    // 2 records 0, but 0's cost and the arrow 0 → 2 make 5, more than 2's cost.
    let short = st(
        vec![Some(0), Some(1), Some(2)],
        vec![None, Some(0), Some(0)],
        2,
    );
    assert_eq!(
        failing(&net, 0, &short),
        ["not in the box (previous_arrow_fits)"]
    );
    // 1 has a cost but records no previous vertex.
    let orphan = st(
        vec![Some(0), Some(1), Some(5)],
        vec![None, None, Some(0)],
        1,
    );
    assert_eq!(
        failing(&net, 0, &orphan),
        ["not in the box (no_previous_keeps_start)"]
    );

    // 0 → 1 (1) and a loop 1 → 1 (0): 1 records itself, a cycle of total 0. Every arrow fits.
    let net = network(2, &[(0, 1, 1), (1, 1, 0)]);
    let level = State::from_parts(vec![Some(0), Some(1)], vec![None, Some(1)], 1, None, 2);
    assert_eq!(
        failing(&net, 0, &level),
        ["not in the box (recorded_cycles_below_zero)"]
    );
    // The same around 1 → 2 → 1, costing −2 and 2.
    let net = network(3, &[(0, 1, 1), (1, 2, -2), (2, 1, 2)]);
    let level = State::from_parts(
        vec![Some(0), Some(1), Some(-1)],
        vec![None, Some(2), Some(1)],
        2,
        None,
        6,
    );
    assert_eq!(
        failing(&net, 0, &level),
        ["not in the box (recorded_cycles_below_zero)"]
    );

    // 0 → 1 (1) and 0 → 1 (3): before any round, 1 at 3, the cost of a path of one arrow, though
    // no arrow has been tried.
    let net = network(2, &[(0, 1, 1), (0, 1, 3)]);
    let early = State::from_parts(vec![Some(0), Some(3)], vec![None, Some(0)], 0, None, 0);
    assert_eq!(
        failing(&net, 0, &early),
        ["not in the box (path_within_tries)"]
    );
    // One arrow tried, and 1 is no longer early.
    let tried = State::from_parts(vec![Some(0), Some(3)], vec![None, Some(0)], 0, None, 1);
    assert_eq!(check(&net, 0, &tried), Ok(()));
}

#[test]
fn every_cost_is_a_walk_within_the_arrows_tried() {
    // Lean: PathWithinTries
    // The chain 0 → 1 → 2 → 3, written in one round: after it 3 costs a path of 3 arrows, and 3
    // arrows have been tried.
    let net = network(4, &[(0, 1, 1), (1, 2, 1), (2, 3, 1)]);
    let states = State::trace(&net, 0);
    assert_eq!(states[1].parts().0, [Some(0), Some(1), Some(2), Some(3)]);
    assert_eq!(states[1].parts().4, 3);
    assert!(states[1].is_path_within_tries(&net, &naive::walk_costs(&net, 0, 3)));
    assert!(!states[1].is_path_within_tries(&net, &naive::walk_costs(&net, 0, 2)));
}

#[test]
fn a_cycle_the_records_close_below_zero_passes() {
    // Lean: RecordedCyclesBelowZero
    // 0 → 1 (1), 1 → 2 (−3), 2 → 1 (2): after three rounds 1 and 2 record each other.
    let net = network(3, &[(0, 1, 1), (1, 2, -3), (2, 1, 2)]);
    let last = State::trace(&net, 0).pop().unwrap();
    assert_eq!(last.parts().1, [None, Some(2), Some(1)]);
    assert!(last.is_recorded_cycles_below_zero(&net));
    // With 2 → 1 dearer by one, the same records total 0.
    let net = network(3, &[(0, 1, 1), (1, 2, -3), (2, 1, 3)]);
    assert!(!last.is_recorded_cycles_below_zero(&net));
    // Of two arrows along a step, the cheaper counts.
    let net = network(3, &[(0, 1, 1), (1, 2, -3), (2, 1, 3), (2, 1, 2)]);
    assert!(last.is_recorded_cycles_below_zero(&net));
}

#[test]
fn the_pieces_answer_on_parts_of_the_wrong_size() {
    let net = network(2, &[(0, 1, 1)]);
    let short = State::from_parts(vec![Some(0)], vec![Some(7)], 1, None, 0);
    assert!(!short.is_cost_is_walk_at_most_cheapest(&net, &[], &[]));
    assert!(!short.is_path_within_tries(&net, &[]));
    assert!(!short.is_previous_arrow_fits(&net));
    assert!(short.is_recorded_cycles_below_zero(&net));
    assert!(short.is_no_previous_keeps_start(&net, 0));
    assert!(!short.is_valid(&net, 0, &[], &[], &[]));
    // A cheapest list with nothing in it fails the box piece.
    let st = State::trace(&net, 0).pop().unwrap();
    let walks = naive::walk_costs(&net, 0, 4);
    assert!(!st.is_valid(&net, 0, &walks, &walks, &[]));
    // Records that leave the vertices: 1 records 7, which records nothing.
    let astray = State::from_parts(vec![Some(0), Some(1)], vec![None, Some(7)], 1, None, 1);
    assert!(astray.is_recorded_cycles_below_zero(&net));
    assert!(!astray.is_previous_arrow_fits(&net));
}

#[test]
fn costs_at_the_edge_of_the_input_range_do_not_overflow() {
    // The module's input range: n (n + ℓ) times the largest arrow cost fits an i64.
    for n in 2..=6usize {
        let w = i64::MAX / (n * n) as i64;
        // A chain 0 → 1 → … → n − 1, every arrow −W: one round goes down it.
        let chain: Vec<(u32, u32, i64)> = (1..n as u32).map(|v| (v - 1, v, -w)).collect();
        let d = bellman_ford(&network(n, &chain), 0).unwrap();
        assert_eq!(d.cost[n - 1], Some(-(n as i64 - 1) * w));
        // The chain closed into a negative cycle: each round goes once round it, and after n
        // rounds the start costs −n² W, past n W, the range when a round read only the last
        // round's costs.
        let mut cycle = chain;
        cycle.push(((n - 1) as u32, 0, -w));
        let net = network(n, &cycle);
        let last = State::trace(&net, 0).pop().unwrap();
        assert_eq!(last.parts().0[0], Some(-((n * n) as i64) * w));
        let c = bellman_ford(&net, 0).unwrap_err();
        assert_eq!(c.vertices.len(), n + 1);
    }
    // Two negative loops at one vertex, ℓ = 2: one round tries the second from the first's
    // cost, −2 W.
    let w = i64::MAX / 3;
    let net = network(1, &[(0, 0, -w), (0, 0, -w)]);
    assert_eq!(State::trace(&net, 0)[1].parts().0, [Some(-2 * w)]);
    assert_eq!(bellman_ford(&net, 0).unwrap_err().vertices, [0, 0]);
    // A loop at the start and an arrow on, ℓ = 1, W = i64::MAX / 6.
    let w = i64::MAX / 6;
    let net = network(2, &[(0, 0, -w), (0, 1, -w)]);
    let last = State::trace(&net, 0).pop().unwrap();
    assert_eq!(last.parts().0, [Some(-2 * w), Some(-3 * w)]);
}

/// A small network whose arrows cost from `low` to `high`: loops, doubled arrows and ties come
/// often, since the costs are few.
fn networks(low: i64, high: i64) -> impl Strategy<Value = (Network, u32)> {
    (1usize..=5).prop_flat_map(move |n| {
        let m = n as u32;
        (
            Just(n),
            prop::collection::vec((0..m, 0..m, low..=high), 0..9),
            0..m,
        )
            .prop_map(|(n, arrows, start)| (network(n, &arrows), start))
    })
}

proptest! {
    #[test]
    fn on_any_network_the_answer_is_the_cheapest_or_a_cycle_below_zero(
        (net, start) in networks(-4, 6)
    ) {
        // Lean: Ops.NoCycleGivesCheapest, Ops.CycleIsBelowZero, Ops.CycleWhenOneExists
        match bellman_ford(&net, start) {
            Err(c) => {
                prop_assert!(naive::reaches_cycle_below_zero(&net, start));
                prop_assert!(naive::is_cycle_below_zero(&net, start, &c.vertices));
            }
            Ok(d) => {
                prop_assert!(!naive::reaches_cycle_below_zero(&net, start));
                prop_assert_eq!(&d.cost, &naive::cheapest(&net, start));
                for v in 0..net.n() as u32 {
                    let Some(path) = d.path_to(v) else {
                        prop_assert!(d.cost[v as usize].is_none());
                        continue;
                    };
                    prop_assert_eq!(path[0], start);
                    let mut seen = path.clone();
                    seen.sort_unstable();
                    seen.dedup();
                    prop_assert_eq!(seen.len(), path.len());
                    prop_assert_eq!(cheapest_hops(&net, &path), d.cost[v as usize]);
                }
            }
        }
    }

    #[test]
    fn on_any_network_every_state_of_the_rounds_is_valid((net, start) in networks(-4, 6)) {
        // Lean: Ops.emptyValid, Ops.stepKeeps, Contract.cost
        let states = every_state_valid(&net, start)?;
        let (_, _, rounds, _, tried) = states.last().unwrap().parts();
        prop_assert!(rounds <= net.n());
        prop_assert_eq!(tried, rounds * net.graph().arrow_count());
        prop_assert_eq!(states.len(), rounds + 1);
        let (answer, r, t) = bellman_ford_with_rounds(&net, start);
        prop_assert_eq!((r, t), (rounds, tried));
        prop_assert_eq!(answer, bellman_ford(&net, start));
        // Only the last round may stop the rounds.
        for st in &states[1..states.len() - 1] {
            prop_assert!(st.parts().3.is_some());
        }
    }

    #[test]
    fn with_no_arrow_below_zero_the_costs_are_dijkstras((net, start) in networks(0, 3)) {
        let d = bellman_ford(&net, start).unwrap();
        prop_assert_eq!(d.cost, dijkstra(&net, start).cost);
    }
}
