// SPDX-License-Identifier: Apache-2.0
//! The Paths module driven from outside the crate, through its public API only, as a reader's
//! program would use it.

use std::error::Error;

use algodesign::graphs::Digraph;
use algodesign::paths::{
    a_star, a_star_with_settled, bfs, dijkstra, dijkstra_to, dijkstra_with_settled, Distances,
    Network, PathsError,
};

/// A small town: 0 home, 1 bakery, 2 school, 3 park, 4 station; minutes on each one-way street.
fn town() -> Result<Network, Box<dyn Error>> {
    let streets = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (2, 4), (4, 0)];
    let minutes = vec![4, 1, 1, 2, 6, 9, 3];
    Ok(Network::new(Digraph::new(5, &streets)?, minutes)?)
}

#[test]
fn the_cheapest_routes_from_home() -> Result<(), Box<dyn Error>> {
    let net = town()?;
    let d = dijkstra(&net, 0);
    assert_eq!(d.cost, [Some(0), Some(4), Some(1), Some(3), Some(9)]);
    assert_eq!(d.path_to(4), Some(vec![0, 2, 3, 4]));
    let (same, settled) = dijkstra_with_settled(&net, 0);
    assert_eq!(same, d);
    assert_eq!(settled, [0, 2, 3, 1, 4]);
    // To the park only: the walk stops there, before the station is known at 9.
    let to_park = dijkstra_to(&net, 0, 3);
    assert_eq!(to_park.cost[3], Some(3));
    assert_eq!(to_park.cost[4], Some(10));
    Ok(())
}

#[test]
fn counting_streets_instead_of_minutes() -> Result<(), Box<dyn Error>> {
    let net = town()?;
    let d = bfs(net.graph(), 0);
    assert_eq!(d.cost, [Some(0), Some(1), Some(1), Some(2), Some(2)]);
    assert_eq!(d.path_to(4), Some(vec![0, 2, 4]));
    Ok(())
}

#[test]
fn a_cost_list_of_the_wrong_length_is_an_error_that_travels() {
    let run = || -> Result<Distances, Box<dyn Error>> {
        let g = Digraph::new(2, &[(0, 1)])?;
        let net = Network::new(g, vec![1, 2])?;
        Ok(dijkstra(&net, 0))
    };
    let err = run().unwrap_err();
    assert_eq!(
        err.downcast_ref::<PathsError>(),
        Some(&PathsError::CostCountMismatch {
            costs: 2,
            arrows: 1
        })
    );
}

#[test]
fn heading_for_the_park_with_an_estimate() -> Result<(), Box<dyn Error>> {
    let net = town()?;
    // The fewest minutes still to go to the park, from each place; the station reaches it only
    // through home, so 3 + 3.
    let estimate = [3, 1, 2, 0, 6];
    let d = a_star(&net, 0, 3, &estimate)?;
    assert_eq!(d.cost[3], Some(3));
    assert_eq!(d.path_to(3), Some(vec![0, 2, 3]));
    let (_, settled) = a_star_with_settled(&net, 0, 3, &estimate)?;
    assert_eq!(settled, [0, 2, 3]);
    // One estimate short is an error, as a cost list of the wrong length is.
    let err = a_star(&net, 0, 3, &estimate[..4]).unwrap_err();
    assert_eq!(
        err,
        PathsError::EstimateCountMismatch {
            estimates: 4,
            vertices: 5
        }
    );
    Ok(())
}

use algodesign::paths::{bellman_ford, bellman_ford_with_rounds, NegativeCycle};

/// A delivery round: 0 depot, 1 shop, 2 market, 3 client; a trip that earns a fee costs less
/// than nothing.
fn deliveries(fee: i64) -> Result<Network, Box<dyn Error>> {
    let trips = [(0, 1), (0, 2), (1, 2), (2, 3), (3, 1)];
    let cost = vec![4, 2, -3, 1, fee];
    Ok(Network::new(Digraph::new(4, &trips)?, cost)?)
}

#[test]
fn the_cheapest_trips_with_fees() -> Result<(), Box<dyn Error>> {
    let net = deliveries(3)?;
    let d = bellman_ford(&net, 0)?;
    assert_eq!(d.cost, [Some(0), Some(4), Some(1), Some(2)]);
    assert_eq!(d.path_to(3), Some(vec![0, 1, 2, 3]));
    let (_, rounds, tried) = bellman_ford_with_rounds(&net, 0);
    assert!(rounds <= net.n());
    assert_eq!(tried, rounds * net.graph().arrow_count());
    Ok(())
}

#[test]
fn a_round_trip_that_pays_is_reported() -> Result<(), Box<dyn Error>> {
    // 1 → 2 → 3 → 1 totals −3 + 1 + 1 = −1.
    let net = deliveries(1)?;
    let err = bellman_ford(&net, 0).unwrap_err();
    assert!(err.to_string().starts_with("a cycle below zero: "));
    let NegativeCycle { vertices } = err;
    assert_eq!(vertices.first(), vertices.last());
    assert_eq!(vertices.len(), 4);
    // The depot is on no cycle, and nothing leads back to it.
    assert!(!vertices.contains(&0));
    Ok(())
}

mod spanning_forests {
    use std::error::Error;

    use algodesign::graphs::Graph;
    use algodesign::paths::{kruskal, kruskal_with_tried, prim, LinkNetwork, PathsError};

    /// Five villages to wire up: 0 – 1 (3), 1 – 2 (1), 0 – 2 (2), 2 – 3 (4), 3 – 4 (2), 1 – 3 (4),
    /// and a sixth village, 5, with no road to anyone.
    fn villages() -> Result<LinkNetwork, Box<dyn Error>> {
        let roads = [(0, 1), (1, 2), (0, 2), (2, 3), (3, 4), (1, 3)];
        Ok(LinkNetwork::new(
            Graph::new(6, &roads)?,
            vec![3, 1, 2, 4, 2, 4],
        )?)
    }

    #[test]
    fn the_cheapest_wiring_of_the_villages() -> Result<(), Box<dyn Error>> {
        let net = villages()?;
        let kept = kruskal(&net);
        // By cost, equal costs by id: 1 (1), 2 (2), 4 (2), then 3 (4) before 5 (4).
        assert_eq!(kept, [1, 2, 4, 3]);
        assert!(net.is_spanning_forest(&kept));
        assert_eq!(net.total(&kept), 9);
        // Village 5 stays a piece of its own, so the walk never stops early.
        assert!(!net.joins(&kept, 0, 5));
        assert_eq!(kruskal_with_tried(&net).1, [1, 2, 4, 0, 3, 5]);
        let mut grown = prim(&net);
        assert_eq!(grown, [2, 1, 3, 4]);
        grown.sort_unstable();
        let mut sorted = kept.clone();
        sorted.sort_unstable();
        assert_eq!(grown, sorted);
        Ok(())
    }

    #[test]
    fn a_cost_list_of_the_wrong_length_is_an_error_that_travels() {
        let run = || -> Result<Vec<u32>, Box<dyn Error>> {
            let g = Graph::new(2, &[(0, 1)])?;
            Ok(kruskal(&LinkNetwork::new(g, vec![])?))
        };
        let err = run().unwrap_err();
        assert_eq!(
            err.downcast_ref::<PathsError>(),
            Some(&PathsError::LinkCostCountMismatch { costs: 0, links: 1 })
        );
    }
}
