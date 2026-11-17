use super::*;
use crate::graphs::Graph;
use crate::paths::naive;
use proptest::prelude::*;

fn net(n: usize, links: &[(u32, u32, i64)]) -> LinkNetwork {
    let ends: Vec<(u32, u32)> = links.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = links.iter().map(|&(_, _, c)| c).collect();
    LinkNetwork::new(Graph::new(n, &ends).unwrap(), costs).unwrap()
}

/// A triangle whose three links all cost 1.
fn triangle() -> LinkNetwork {
    net(3, &[(0, 1, 1), (1, 2, 1), (0, 2, 1)])
}

/// The triangle with link 2 made dearer.
fn dear_triangle() -> LinkNetwork {
    net(3, &[(0, 1, 1), (1, 2, 1), (0, 2, 4)])
}

/// A union-find over `n` items with the pairs `merges` merged, in order.
fn merged(n: usize, merges: &[(usize, usize)]) -> UnionFind {
    let mut uf = UnionFind::new(n);
    for &(a, b) in merges {
        uf.union(a, b);
    }
    uf
}

/// Every state of the walk passes `Valid` and `WellFormed`, judged against the cheapest forests.
fn every_state_valid(net: &LinkNetwork) -> Result<Vec<State>, TestCaseError> {
    let cheapest = naive::cheapest_forests(net);
    let states = State::trace(net);
    for st in &states {
        prop_assert_eq!(st.check_valid(net, &cheapest), Ok(()));
    }
    Ok(states)
}

/// Each piece of `Valid` and `WellFormed` on `st`, in the Lean order.
fn pieces(st: &State, net: &LinkNetwork) -> [bool; 6] {
    let cheapest = naive::cheapest_forests(net);
    [
        st.is_part_of_cheapest(&cheapest),
        st.is_groups_are_kept_joins(net),
        st.is_union_find_ready(net),
        st.is_kept_closes_no_cycle(net),
        st.is_rest_cheapest_first(net),
        st.is_passed_are_joined(net),
    ]
}

/// The pieces of `st` all hold but the one at `broken`, and `check_valid` names it.
fn breaks_only(st: &State, net: &LinkNetwork, broken: usize) {
    let mut want = [true; 6];
    want[broken] = false;
    assert_eq!(pieces(st, net), want);
    assert_eq!(
        st.check_valid(net, &naive::cheapest_forests(net)),
        Err(LABELS[broken])
    );
}

#[test]
fn on_equal_costs_the_tie_goes_by_id_and_the_walk_stops_at_one_group() {
    // Lean: AlgoDesignTests.Kruskal, the triangle
    let tri = triangle();
    assert_eq!(order(&tri), [0, 1, 2]);
    assert_eq!(kruskal(&tri), [0, 1]);
    let cheapest = naive::cheapest_forests(&tri);
    assert_eq!(cheapest, [vec![0, 1], vec![0, 2], vec![1, 2]]);
    // One group is left after two links, so link 2 is never tried.
    assert_eq!(kruskal_with_tried(&tri), (vec![0, 1], vec![0, 1]));
    let states = every_state_valid(&tri).unwrap();
    assert_eq!(states.len(), 3);
    assert_eq!(states[2].parts().0, [2]);
}

#[test]
fn a_graph_in_two_pieces_gets_a_spanning_forest() {
    // Lean: AlgoDesignTests.Kruskal, twoPieces
    let two = net(4, &[(2, 3, 5), (0, 1, 2)]);
    let kept = kruskal(&two);
    assert_eq!(kept, [1, 0]);
    assert!(two.is_spanning_forest(&kept));
    assert!(!two.joins(&kept, 0, 2));
    // Two groups are left at the end, so every link is tried.
    assert_eq!(kruskal_with_tried(&two).1, [1, 0]);
}

#[test]
fn a_loop_is_skipped_and_of_two_doubled_links_the_cheaper_is_kept() {
    // Lean: AlgoDesignTests.Kruskal, loopAndDouble
    let ld = net(2, &[(0, 0, -1), (0, 1, 4), (0, 1, 3)]);
    assert_eq!(order(&ld), [0, 2, 1]);
    assert_eq!(kruskal_with_tried(&ld), (vec![2], vec![0, 2]));
    assert_eq!(naive::cheapest_forests(&ld), [vec![2]]);
    every_state_valid(&ld).unwrap();
}

/// Each vertex's cheapest link, equal costs by id.
fn nearest_links(net: &LinkNetwork) -> Vec<u32> {
    let g = net.graph();
    let mut links: Vec<u32> = (0..g.n())
        .filter_map(|v| {
            g.adj(v)
                .iter()
                .map(|(_, id)| (net.link_cost(id as usize), id))
                .min()
                .map(|(_, id)| id)
        })
        .collect();
    links.sort_unstable();
    links.dedup();
    links
}

#[test]
fn nearest_neighbor_links_leave_islands_and_kruskal_joins_them() {
    // Lean: AlgoDesignTests.Kruskal, islands
    // Two close pairs, {0, 1} and {2, 3}, far apart.
    let islands = net(4, &[(0, 1, 1), (2, 3, 1), (1, 2, 5), (0, 3, 6)]);
    let nearest = nearest_links(&islands);
    assert_eq!(nearest, [0, 1]);
    assert!(!islands.joins_what_graph_joins(&nearest));
    let kept = kruskal(&islands);
    assert_eq!(kept, [0, 1, 2]);
    assert!(islands.joins_what_graph_joins(&kept));
}

#[test]
fn no_vertex_or_one_vertex_keeps_nothing() {
    assert_eq!(kruskal_with_tried(&net(0, &[])), (vec![], vec![]));
    // One vertex is one group from the start: its loop is never tried.
    assert_eq!(kruskal_with_tried(&net(1, &[(0, 0, 3)])), (vec![], vec![]));
    assert_eq!(State::trace(&net(1, &[(0, 0, 3)])).len(), 1);
}

#[test]
fn costs_below_zero_are_taken_first() {
    let neg = net(3, &[(0, 1, 2), (1, 2, -5), (0, 2, -1)]);
    assert_eq!(kruskal(&neg), [1, 2]);
    assert_eq!(neg.total(&kruskal(&neg)), -6);
}

#[test]
fn each_broken_state_names_its_piece() {
    // Lean: AlgoDesignTests.Kruskal, keptDear: link 2 kept first, part of no cheapest tree.
    let dear = dear_triangle();
    let kept_dear = State::from_parts(vec![0, 1], vec![2], vec![2], merged(3, &[(0, 2)]));
    breaks_only(&kept_dear, &dear, 0);
    // Link 0 kept, but the union-find still has every vertex alone.
    let unmerged = State::from_parts(vec![1, 2], vec![0], vec![0], UnionFind::new(3));
    breaks_only(&unmerged, &dear, 1);
    // A union-find over four items for a graph of three.
    let wide = State::from_parts(vec![0, 1, 2], vec![], vec![], UnionFind::new(4));
    breaks_only(&wide, &dear, 2);
    // Link 0 kept twice.
    let twice = State::from_parts(vec![1, 2], vec![0, 0], vec![0], merged(3, &[(0, 1)]));
    breaks_only(&twice, &dear, 3);
    // The dear link before the cheap one.
    let jumbled = State::from_parts(vec![0, 2, 1], vec![], vec![], UnionFind::new(3));
    breaks_only(&jumbled, &dear, 4);
    // Link 0 taken and skipped, though its ends were apart.
    let dropped = State::from_parts(vec![1, 2], vec![], vec![0], UnionFind::new(3));
    breaks_only(&dropped, &dear, 5);
    // The walk's own second state is legal.
    let st = &State::trace(&dear)[1];
    assert_eq!(st.parts().0, [1, 2]);
    assert_eq!(
        st.check_valid(&dear, &naive::cheapest_forests(&dear)),
        Ok(())
    );
}

#[cfg(feature = "unchecked")]
#[test]
fn a_union_find_with_a_cycle_of_parents_gets_an_answer() {
    // 0 and 1 point at each other: three steps up from 0 reach 1, and from 1 reach 0, so the two
    // read as apart, though link 0 is kept.
    let dear = dear_triangle();
    let looped = UnionFind::from_parts(vec![1, 0, 2], vec![0; 3], 3);
    let st = State::from_parts(vec![1, 2], vec![0], vec![0], looped);
    assert!(!st.is_union_find_ready(&dear));
    assert!(!st.is_groups_are_kept_joins(&dear));
    assert_eq!(
        st.check_valid(&dear, &naive::cheapest_forests(&dear)),
        Err(LABELS[1])
    );
}

#[test]
fn the_pieces_answer_on_parts_of_the_wrong_size() {
    let dear = dear_triangle();
    let cheapest = naive::cheapest_forests(&dear);
    let past = State::from_parts(vec![7, 0], vec![9], vec![9], UnionFind::new(1));
    assert!(!past.is_part_of_cheapest(&cheapest));
    assert!(!past.is_union_find_ready(&dear));
    assert!(!past.is_kept_closes_no_cycle(&dear));
    assert!(!past.is_rest_cheapest_first(&dear));
    assert!(!past.is_passed_are_joined(&dear));
    // A union-find over one item reads vertices 1 and 2 as alone, as the kept links leave them.
    assert!(past.is_groups_are_kept_joins(&dear));
    assert!(!past.is_valid(&dear, &cheapest));
    assert!(!past.is_valid(&dear, &[]));
}

/// A small link network: up to seven vertices and twelve links, so trying every set of links
/// stays quick; loops, doubled links, pieces and ties on cost come often, and negative costs.
fn link_networks() -> impl Strategy<Value = LinkNetwork> {
    (1usize..=7).prop_flat_map(|n| {
        let m = n as u32;
        prop::collection::vec((0..m, 0..m, -2i64..4), 0..=12).prop_map(move |links| net(n, &links))
    })
}

proptest! {
    #[test]
    fn on_any_network_the_kept_links_are_a_cheapest_spanning_forest(net in link_networks()) {
        // Lean: Ops.JoinsWhatGraphJoins, Ops.ClosesNoCycle, Ops.NoCheaperForest
        let kept = kruskal(&net);
        prop_assert!(net.is_spanning_forest(&kept));
        let cheapest = naive::cheapest_forests(&net);
        prop_assert_eq!(Some(net.total(&kept)), cheapest.iter().map(|f| net.total(f)).min());
        // The kept links come in the order taken: by cost, equal costs by id.
        let keys: Vec<(i64, u32)> = kept.iter().map(|&i| (net.link_cost(i as usize), i)).collect();
        prop_assert!(keys.windows(2).all(|p| p[0] < p[1]));
    }

    #[test]
    fn on_any_network_every_state_of_the_walk_is_valid(net in link_networks()) {
        // Lean: Ops.emptyValid and Ops.stepKeeps (valid_start, valid_step), Contract.cost
        // (kruskal_cost)
        let states = every_state_valid(&net)?;
        let last = states.last().unwrap();
        let (rest, kept, tried, uf) = last.parts();
        prop_assert!(rest.is_empty() || uf.count() == 1);
        prop_assert_eq!(kept, &kruskal(&net)[..]);
        prop_assert_eq!(states.len(), tried.len() + 1);
        // Each link tried at most once, in the order: the tried links and the rest are the order.
        let ord = order(&net);
        prop_assert_eq!([tried, rest].concat(), ord);
        prop_assert!(tried.len() <= net.graph().link_count());
        prop_assert_eq!(kruskal_with_tried(&net), (kept.to_vec(), tried.to_vec()));
    }
}
