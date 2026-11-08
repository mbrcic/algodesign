use super::*;

#[test]
fn a_network_takes_one_cost_per_arrow() {
    let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 1)]).unwrap();
    let net = Network::new(g.clone(), vec![4, -2, 7]).unwrap();
    assert_eq!(net.cost(), [4, -2, 7]);
    assert_eq!(net.arrow_cost(1), -2);
    assert_eq!(net.n(), 3);
    assert_eq!(net.graph(), &g);
    assert_eq!(net.clone().into_parts(), (g, vec![4, -2, 7]));
}

#[test]
fn too_few_or_too_many_costs_are_refused() {
    let g = Digraph::new(2, &[(0, 1), (1, 0)]).unwrap();
    for costs in [vec![], vec![1], vec![1, 2, 3]] {
        let k = costs.len();
        assert_eq!(
            Network::new(g.clone(), costs),
            Err(PathsError::CostCountMismatch {
                costs: k,
                arrows: 2
            })
        );
    }
    let err = Network::new(g, vec![1]).unwrap_err();
    assert_eq!(err.to_string(), "1 costs for 2 arrows: one cost per arrow");
}

#[test]
fn no_arrows_and_no_costs_make_a_network() {
    let g = Digraph::new(1, &[]).unwrap();
    assert!(Network::new(g, Vec::new()).is_ok());
}
