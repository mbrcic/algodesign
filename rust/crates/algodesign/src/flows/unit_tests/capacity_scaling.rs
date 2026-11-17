use super::*;
use crate::flows::max_flow::{max_flow_with, max_flow_with_rounds};
use crate::flows::network::Network;
use crate::flows::residual::Augmentation;
use crate::graphs::Digraph;
use crate::rng::SplitMix64;

fn network(n: usize, arrows: &[(u32, u32, u64)], s: u32, t: u32) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let capacity = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), capacity, s, t).unwrap()
}

#[test]
fn the_first_threshold_is_the_largest_power_of_two_below_the_largest_capacity_of_any_arrow() {
    // The largest capacity, 12, is not on an arrow out of the source, whose largest is 3.
    let net = network(3, &[(0, 1, 3), (1, 2, 12)], 0, 2);
    let mut r = Residual::new(&net);
    let mut rule = CapacityScaling::new();
    rule.start(&r);
    assert_eq!(rule.threshold(), 8);
    // Round 1: Δ = 8 and Δ = 4 find nothing; Δ = 2 finds 0 → 1 → 2 and sends its bottleneck.
    assert!(rule.round(&mut r));
    assert_eq!(rule.threshold(), 2);
    assert_eq!(
        r.added,
        [Augmentation {
            path: vec![0, 2],
            amount: 3
        }]
    );
    // Round 2: Δ = 2 and Δ = 1 find nothing, and the round sends nothing.
    assert!(!rule.round(&mut r));
    assert_eq!(rule.threshold(), 0);
    assert_eq!(r.flow(), [3, 3]);
}

#[test]
fn a_rule_never_started_starts_itself_at_its_first_round() {
    let net = network(3, &[(0, 1, 3), (1, 2, 12), (0, 2, 5)], 0, 2);
    let mut r = Residual::new(&net);
    let mut rule = CapacityScaling::new();
    assert!(rule.round(&mut r));
    while rule.round(&mut r) {}
    assert_eq!(rule.threshold(), 0);
    assert_eq!(r.flow(), max_flow_with(&net, CapacityScaling::new()).flow);
    // Started on a flow that is not zero, the threshold is still read from the capacities.
    let mut again = CapacityScaling::<u64>::new();
    again.start(&r);
    assert_eq!(again.threshold(), 8);
}

#[test]
fn a_spent_rule_starts_afresh_on_a_second_run() {
    let net = network(3, &[(0, 1, 3), (1, 2, 12), (0, 2, 5)], 0, 2);
    let mut rule = CapacityScaling::new();
    let mut first = Residual::new(&net);
    while rule.round(&mut first) {}
    assert_eq!(rule.threshold(), 0);
    // The second run reads the threshold, 8, again: Δ = 8 finds nothing, Δ = 4 sends 5 along 0 → 2,
    // and Δ stays 4 for the next round.
    let mut second = Residual::new(&net);
    assert!(rule.round(&mut second));
    assert_eq!(rule.threshold(), 4);
    assert_eq!(second.flow(), [0, 0, 5]);
    while rule.round(&mut second) {}
    assert_eq!(second.flow(), first.flow());
}

#[test]
fn with_every_capacity_zero_the_threshold_is_zero_and_the_search_needs_residual_capacity() {
    let net = network(2, &[(0, 1, 0)], 0, 1);
    let (answer, rounds) = max_flow_with_rounds(&net, CapacityScaling::new());
    assert!(rounds.is_empty());
    assert_eq!(answer.value, 0);
}

#[test]
fn every_path_sent_carries_at_least_the_threshold_it_was_found_at() {
    // Random networks of up to 12 vertices, rounds stepped one at a time.
    let mut g = SplitMix64::new(11);
    for _ in 0..300 {
        let n = 2 + (g.next_u64() % 11) as usize;
        let m = (g.next_u64() % 40) as usize;
        let arrows: Vec<(u32, u32, u64)> = (0..m)
            .map(|_| {
                let a = (g.next_u64() % n as u64) as u32;
                let b = (g.next_u64() % n as u64) as u32;
                (a, b, g.next_u64() % 1000)
            })
            .collect();
        let net = network(n, &arrows, 0, n as u32 - 1);
        let mut r = Residual::new(&net);
        let mut rule = CapacityScaling::new();
        rule.start(&r);
        let mut before = rule.threshold();
        loop {
            r.added.clear();
            if !rule.round(&mut r) {
                break;
            }
            assert_eq!(r.added.len(), 1);
            let now = rule.threshold();
            assert!(now <= before && now >= 1);
            assert!(r.added[0].amount >= now);
            before = now;
        }
        assert_eq!(rule.threshold(), 0);
    }
}
