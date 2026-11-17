use super::*;

fn net(n: usize, links: &[(u32, u32, i64)]) -> LinkNetwork {
    let ends: Vec<(u32, u32)> = links.iter().map(|&(a, b, _)| (a, b)).collect();
    let costs = links.iter().map(|&(_, _, c)| c).collect();
    LinkNetwork::new(Graph::new(n, &ends).unwrap(), costs).unwrap()
}

#[test]
fn a_cost_list_of_the_wrong_length_is_refused() {
    let g = Graph::new(2, &[(0, 1)]).unwrap();
    assert_eq!(
        LinkNetwork::new(g.clone(), vec![]),
        Err(PathsError::LinkCostCountMismatch { costs: 0, links: 1 })
    );
    assert_eq!(
        PathsError::LinkCostCountMismatch { costs: 0, links: 1 }.to_string(),
        "0 costs for 1 links: one cost per link"
    );
    let ok = LinkNetwork::new(g.clone(), vec![-4]).unwrap();
    assert_eq!((ok.n(), ok.cost(), ok.link_cost(0)), (2, &[-4][..], -4));
    assert_eq!(ok.into_parts(), (g, vec![-4]));
}

#[test]
fn two_links_between_the_same_vertices_and_a_loop() {
    // Lean: the examples of `LinkNetwork.lean`
    let double = net(2, &[(0, 1, 5), (0, 1, 3)]);
    assert!(double.is_spanning_forest(&[1]));
    assert!(double.is_spanning_forest(&[0]));
    assert!(!double.closes_no_cycle(&[0, 1]));
    assert_eq!(double.total(&[0, 1]), 8);
    let lp = net(2, &[(1, 1, 0)]);
    assert!(!lp.closes_no_cycle(&[0]));
    // Not joining 0 and 1 is right: the graph does not join them either.
    assert!(lp.is_spanning_forest(&[]));
}

#[test]
fn joining_is_a_chain_of_links_read_either_way() {
    let path = net(4, &[(1, 0, 1), (1, 2, 1), (3, 3, 1)]);
    assert!(path.joins(&[0, 1], 0, 2));
    assert!(path.joins(&[0, 1], 2, 0));
    assert!(!path.joins(&[0], 0, 2));
    assert!(path.joins(&[], 3, 3));
    assert!(!path.joins(&[0, 1, 2], 0, 3));
    assert!(path.joins_what_graph_joins(&[0, 1]));
    assert!(!path.joins_what_graph_joins(&[1]));
}

#[test]
fn ids_past_the_links_read_as_a_loop_at_0_that_costs_nothing() {
    let path = net(3, &[(0, 1, 2), (1, 2, 3)]);
    assert_eq!(path.ends(9), (0, 0));
    assert_eq!(path.cost_at(9), 0);
    assert_eq!(path.total(&[0, 9]), 2);
    assert!(!path.joins(&[9], 1, 2));
    assert!(path.joins(&[9], 7, 7));
    assert!(!path.joins(&[0, 1], 0, 7));
    // A link listed twice closes a cycle, and so does an id past the links.
    assert!(!path.closes_no_cycle(&[0, 0]));
    assert!(!path.closes_no_cycle(&[9]));
    assert!(!path.is_spanning_forest(&[0, 1, 9]));
    assert!(path.is_spanning_forest(&[1, 0]));
}
