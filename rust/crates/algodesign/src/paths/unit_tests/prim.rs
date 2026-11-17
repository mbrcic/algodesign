use super::*;
use crate::graphs::Graph;
use crate::paths::{kruskal, naive};
use proptest::prelude::*;

fn net(n: usize, links: &[(u32, u32, i64)]) -> LinkNetwork {
    let ends: Vec<(u32, u32)> = links.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = links.iter().map(|&(_, _, c)| c).collect();
    LinkNetwork::new(Graph::new(n, &ends).unwrap(), costs).unwrap()
}

fn sorted(mut ids: Vec<u32>) -> Vec<u32> {
    ids.sort_unstable();
    ids
}

#[test]
fn the_tree_grows_from_vertex_0_by_the_cheapest_link_out() {
    // 0 – 1 (4), 0 – 2 (1), 2 – 1 (2), 1 – 3 (1), 2 – 3 (5).
    let five = net(4, &[(0, 1, 4), (0, 2, 1), (2, 1, 2), (1, 3, 1), (2, 3, 5)]);
    // From 0: link 1 to 2, then link 2 to 1, then link 3 to 3. Kruskal keeps 1 and 3 first.
    assert_eq!(prim(&five), [1, 2, 3]);
    assert_eq!(kruskal(&five), [1, 3, 2]);
}

#[test]
fn equal_costs_go_by_link_id() {
    // The triangle whose links all cost 1: from 0, links 0 and 2 tie, and 0 goes first.
    let tri = net(3, &[(0, 1, 1), (1, 2, 1), (0, 2, 1)]);
    assert_eq!(prim(&tri), [0, 1]);
    // Two doubled links of one cost: the lower id.
    let double = net(2, &[(0, 1, 3), (1, 0, 3)]);
    assert_eq!(prim(&double), [0]);
}

#[test]
fn each_piece_gets_its_own_tree_from_its_lowest_vertex() {
    // {0, 3} and {1, 2}, and 4 alone, with a loop at 4.
    let pieces = net(5, &[(2, 1, 7), (3, 0, 2), (4, 4, 0)]);
    assert_eq!(prim(&pieces), [1, 0]);
    assert!(pieces.is_spanning_forest(&prim(&pieces)));
    assert_eq!(prim(&net(0, &[])), Vec::<u32>::new());
}

fn pushed(net: &LinkNetwork) -> usize {
    let mut count = 0;
    walk(net, |p| count = p);
    count
}

#[test]
fn a_link_is_pushed_only_when_cheaper_than_every_link_pushed_towards_its_vertex() {
    // From 0, links 0 and 1 reach 1 and 2 at cost 1; from 1, link 2 reaches 2 at cost 5, dearer
    // than link 1, so it is not pushed.
    let dear = net(3, &[(0, 1, 1), (0, 2, 1), (1, 2, 5)]);
    assert_eq!(prim(&dear), [0, 1]);
    assert_eq!(pushed(&dear), 2);
    // Link 2 at cost 1 ties link 1 on cost and has the larger id: not pushed either.
    let tie = net(3, &[(0, 1, 1), (0, 2, 1), (1, 2, 1)]);
    assert_eq!(prim(&tie), [0, 1]);
    assert_eq!(pushed(&tie), 2);
    // Link 2 at cost 0 is cheaper than link 1: pushed, and taken.
    let cheap = net(3, &[(0, 1, 1), (0, 2, 1), (1, 2, 0)]);
    assert_eq!(prim(&cheap), [0, 2]);
    assert_eq!(pushed(&cheap), 3);
}

#[test]
fn nearest_neighbor_islands_are_joined() {
    let islands = net(4, &[(0, 1, 1), (2, 3, 1), (1, 2, 5), (0, 3, 6)]);
    assert_eq!(prim(&islands), [0, 2, 1]);
}

/// A small link network, ties on cost common, negative costs included.
fn link_networks(costs: std::ops::Range<i64>) -> impl Strategy<Value = LinkNetwork> {
    (1usize..=7).prop_flat_map(move |n| {
        let m = n as u32;
        prop::collection::vec((0..m, 0..m, costs.clone()), 0..=12)
            .prop_map(move |links| net(n, &links))
    })
}

proptest! {
    #[test]
    fn on_any_network_prim_gives_a_cheapest_spanning_forest(net in link_networks(-2..4)) {
        let added = prim(&net);
        prop_assert!(net.is_spanning_forest(&added));
        let least = naive::cheapest_forests(&net).iter().map(|f| net.total(f)).min();
        prop_assert_eq!(Some(net.total(&added)), least);
        prop_assert_eq!(net.total(&added), net.total(&kruskal(&net)));
        // Both take the cheapest link by (cost, id), so the set is Kruskal's, ties or not.
        prop_assert_eq!(sorted(added), sorted(kruskal(&net)));
    }

    #[test]
    fn on_distinct_costs_prim_keeps_kruskals_links(
        (n, links) in (1usize..=7).prop_flat_map(|n| {
            let m = n as u32;
            (Just(n), prop::collection::vec((0..m, 0..m), 0..=12))
        }),
        shuffle in prop::collection::vec(any::<u64>(), 12),
    ) {
        // Distinct costs: the link ids reordered by the shuffle keys.
        let mut ids: Vec<usize> = (0..links.len()).collect();
        ids.sort_by_key(|&i| shuffle[i]);
        let mut cost = vec![0i64; links.len()];
        for (rank, &i) in ids.iter().enumerate() {
            cost[i] = rank as i64 - 3;
        }
        let with_costs: Vec<(u32, u32, i64)> =
            links.iter().zip(&cost).map(|(&(a, b), &c)| (a, b, c)).collect();
        let net = net(n, &with_costs);
        prop_assert_eq!(sorted(prim(&net)), sorted(kruskal(&net)));
    }
}
