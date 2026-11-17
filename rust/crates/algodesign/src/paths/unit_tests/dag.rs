use super::*;
use crate::graphs::Digraph;
use crate::paths::naive;
use proptest::prelude::*;

fn network(n: usize, arrows: &[(u32, u32, i64)]) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), costs).unwrap()
}

/// A negative arrow: 0 → 1 (5), 0 → 2 (2), 2 → 1 (−4), 1 → 3 (1). The way round through 2 costs
/// less than the direct arrow to 1. The Lean's `neg`.
fn neg() -> Network {
    network(4, &[(0, 1, 5), (0, 2, 2), (2, 1, -4), (1, 3, 1)])
}

#[test]
fn a_negative_arrow_gives_the_cheaper_way_round() {
    // Lean: Ops.ReachedGetCheapest, Ops.PreviousGivesPath, the example on `neg`
    let net = neg();
    assert_eq!(topological_order(net.graph()).unwrap(), [0, 2, 1, 3]);
    let d = dag_paths(&net, 0).unwrap();
    assert_eq!(d.cost, [Some(0), Some(-2), Some(2), Some(-1)]);
    assert_eq!(d.previous, [None, Some(2), Some(0), Some(1)]);
    assert_eq!(d.cost, naive::cheapest(&net, 0));
}

#[test]
fn a_vertex_that_cannot_be_reached_is_reported_and_its_row_is_not_tried() {
    // Lean: Ops.UnreachedReported; from 2, vertex 0 cannot be reached
    let d = dag_paths(&neg(), 2).unwrap();
    assert_eq!(d.cost, [None, Some(-4), Some(0), Some(-3)]);
    assert_eq!(d.previous, [None, Some(2), None, Some(1)]);
    // 1 → 2 is out of reach from 0: 1 is taken with no cost, and 2 stays unknown.
    let net = network(3, &[(1, 2, 1)]);
    assert_eq!(dag_paths(&net, 0).unwrap().cost, [Some(0), None, None]);
}

#[test]
fn of_two_arrows_between_the_same_vertices_the_cheaper_counts() {
    // Lean: the two arrows from 0 to 1
    let d = dag_paths(&network(2, &[(0, 1, 5), (0, 1, 3)]), 0).unwrap();
    assert_eq!(d.cost, [Some(0), Some(3)]);
    assert_eq!(d.previous, [None, Some(0)]);
}

#[test]
fn an_equal_cost_keeps_the_previous_vertex() {
    // 0 → 1 (1), 0 → 2 (1), 1 → 3 (1), 2 → 3 (1): 3 is reached at 2 from 1 first.
    let net = network(4, &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1)]);
    let d = dag_paths(&net, 0).unwrap();
    assert_eq!(d.previous, [None, Some(0), Some(0), Some(1)]);
}

#[test]
fn a_loop_or_a_cycle_gives_kahns_stuck_set() {
    // Lean: Ops.CycleGivesStuck; a loop is a cycle
    let net = network(2, &[(0, 1, 1), (1, 1, 1)]);
    assert_eq!(dag_paths(&net, 0).unwrap_err().vertices, [1]);
    // A cycle of two: the vertices after it are stuck too.
    let net = network(3, &[(0, 1, 1), (1, 0, 1), (1, 2, 1)]);
    assert_eq!(dag_paths(&net, 0).unwrap_err().vertices, [0, 1, 2]);
}

#[test]
#[should_panic(expected = "start 2 out of range 0..2")]
fn a_start_out_of_range_panics() {
    let _ = dag_paths(&network(2, &[(0, 1, 1)]), 2);
}

#[test]
#[should_panic(expected = "start 2 out of range 0..2")]
fn a_start_out_of_range_panics_before_the_order_is_sought() {
    let _ = dag_paths(&network(2, &[(0, 1, 1), (1, 0, 1)]), 2);
}

/// A small network with no cycle: every arrow from a lower position to a higher one of a shuffled
/// order of the vertices, doubled arrows and negative costs included.
fn dags() -> impl Strategy<Value = (Network, u32)> {
    (1usize..=6).prop_flat_map(|n| {
        let m = n as u32;
        (
            Just(n),
            Just((0..m).collect::<Vec<u32>>()).prop_shuffle(),
            prop::collection::vec((0..m, 0..m, -5i64..6), 0..11),
            0..m,
        )
            .prop_map(|(n, rank, arrows, start)| {
                let forward: Vec<(u32, u32, i64)> = arrows
                    .into_iter()
                    .filter(|&(a, b, _)| a < b)
                    .map(|(a, b, c)| (rank[a as usize], rank[b as usize], c))
                    .collect();
                (network(n, &forward), start)
            })
    })
}

/// A small network, cycles and loops included.
fn networks() -> impl Strategy<Value = (Network, u32)> {
    (1usize..=6).prop_flat_map(|n| {
        let m = n as u32;
        (
            Just(n),
            prop::collection::vec((0..m, 0..m, -5i64..6), 0..9),
            0..m,
        )
            .prop_map(|(n, arrows, start)| (network(n, &arrows), start))
    })
}

proptest! {
    #[test]
    fn on_any_graph_with_no_cycle_the_walk_gives_the_cheapest_costs_and_paths_of_those_costs(
        (net, start) in dags()
    ) {
        // Lean: Ops.ReachedGetCheapest, Ops.PreviousGivesPath, Ops.UnreachedReported
        let d = dag_paths(&net, start).unwrap();
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
                let c = g.out(hop[0] as usize).iter().filter(|&(w, _)| w == hop[1])
                    .map(|(_, id)| net.arrow_cost(id as usize)).min();
                prop_assert!(c.is_some());
                total += c.unwrap();
            }
            prop_assert_eq!(Some(total), d.cost[v as usize]);
        }
    }

    #[test]
    fn on_any_graph_the_walk_answers_or_gives_kahns_stuck_set((net, start) in networks()) {
        // Lean: Ops.CycleGivesStuck, and dagPaths through TopoOrder.kahn
        match (dag_paths(&net, start), topological_order(net.graph())) {
            (Ok(d), Ok(_)) => prop_assert_eq!(d.cost, naive::cheapest(&net, start)),
            (Err(stuck), Err(kahn)) => prop_assert_eq!(stuck, kahn),
            (got, kahn) => prop_assert!(false, "{:?} against Kahn's {:?}", got, kahn),
        }
    }
}
