// SPDX-License-Identifier: Apache-2.0
//! The Flows module driven from outside the crate, through its public API only, as a reader's
//! program would use it: the library's rules, and a rule of the reader's own.

use std::error::Error;

use algodesign::flows::{
    max_flow, max_flow_with, CapacityScaling, Dinic, EdmondsKarp, FlowsError, MaxFlow, Network,
    PathRule, Residual,
};
use algodesign::graphs::Digraph;

/// The chapter's network: 0 → 1 and 0 → 2 carry 1000, 1 → 3 and 2 → 3 carry 1000, and the middle
/// arrow 1 → 2 carries 1.
fn one_and_thousand() -> Result<Network, Box<dyn Error>> {
    let arrows = [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)];
    let g = Digraph::new(4, &arrows)?;
    Ok(Network::new(g, vec![1000, 1000, 1, 1000, 1000], 0, 3)?)
}

/// Whether `answer` passes the library's own check, `MaxFlow::check_valid`, a flow within the
/// capacities that loses nothing on the way and a cut of its amount, and reports what the flow
/// sends from the source.
fn certified(net: &Network, answer: &MaxFlow) -> bool {
    if answer.check_valid(net).is_err() {
        return false;
    }
    let g = net.graph();
    let s = net.source();
    let mut sent = 0i128;
    for i in 0..g.arrow_count() {
        let (tail, head) = g.arrow(i);
        sent += i128::from(answer.flow[i]) * (i128::from(tail == s) - i128::from(head == s));
    }
    sent == i128::from(answer.value)
}

/// A path rule of the reader's own: each round sends along the longest augmenting path, found by
/// trying every one. It keeps the promise, and is slow on purpose. Counts its rounds.
#[derive(Default)]
struct Longest {
    rounds: usize,
}

impl PathRule<u64> for Longest {
    fn round(&mut self, r: &mut Residual) -> bool {
        self.rounds += 1;
        let (s, t) = (r.source(), r.sink());
        let mut best: Option<Vec<u32>> = None;
        // Each partial path: where it ends, its arrows, the vertices it passes.
        let mut open = vec![(s, Vec::new(), vec![s])];
        while let Some((u, path, passed)) = open.pop() {
            if u == t {
                if best.as_ref().is_none_or(|b| path.len() > b.len()) {
                    best = Some(path);
                }
                continue;
            }
            for &e in r.out(u) {
                let v = r.head(e);
                if r.residual_capacity(e) > 0 && !passed.contains(&v) {
                    let mut longer = path.clone();
                    longer.push(e);
                    let mut more = passed.clone();
                    more.push(v);
                    open.push((v, longer, more));
                }
            }
        }
        let Some(path) = best else {
            return false;
        };
        let amount = path
            .iter()
            .map(|&e| r.residual_capacity(e))
            .min()
            .unwrap_or(0);
        for &e in &path {
            r.send(e, amount);
        }
        true
    }
}

#[test]
fn a_rule_that_takes_the_long_way_needs_two_thousand_rounds() -> Result<(), Box<dyn Error>> {
    let net = one_and_thousand()?;
    // Every path of three arrows crosses the middle arrow, one way and then back, one unit each.
    let mut longest = Longest::default();
    let answer = max_flow_with(&net, &mut longest);
    assert_eq!(answer.value, 2000);
    assert_eq!(longest.rounds, 2001);
    assert!(certified(&net, &answer));
    // The library's rules take the two short paths.
    assert_eq!(max_flow(&net), answer);
    Ok(())
}

#[test]
fn every_rule_gives_the_same_largest_amount() -> Result<(), Box<dyn Error>> {
    // A city's water: the plant 0, pumping stations 1 to 4, the reservoir 5; mains in both
    // directions between 2 and 3.
    let mains = [
        (0, 1),
        (0, 2),
        (1, 3),
        (2, 3),
        (3, 2),
        (2, 4),
        (3, 5),
        (4, 5),
        (1, 2),
    ];
    let litres = vec![16, 13, 12, 9, 4, 14, 20, 4, 10];
    let net = Network::new(Digraph::new(6, &mains)?, litres, 0, 5)?;
    let dinic = max_flow_with(&net, Dinic::new());
    let ek = max_flow_with(&net, EdmondsKarp::new());
    let scaling = max_flow_with(&net, CapacityScaling::new());
    assert_eq!(dinic.value, 24);
    for answer in [&dinic, &ek, &scaling] {
        assert_eq!(answer.value, dinic.value);
        assert!(certified(&net, answer));
        // The cut every rule finds is the one the residual graph leaves: the same set.
        assert_eq!(answer.side, dinic.side);
    }
    Ok(())
}

#[test]
fn a_broken_answer_is_named_by_its_first_broken_piece() -> Result<(), Box<dyn Error>> {
    let net = one_and_thousand()?;
    let mut answer = max_flow(&net);
    assert!(answer.is_valid(&net));
    // The middle arrow carries 2 over its 1, and the arrows after it make up the difference.
    answer.flow = vec![1000, 1000, 2, 998, 1002];
    assert_eq!(
        answer.check_valid(&net),
        Err("invariant 1 (within_capacity)")
    );
    assert!(!answer.is_within_capacity(&net) && answer.is_conserved(&net));
    Ok(())
}

#[test]
fn a_bad_network_is_an_error_that_travels() {
    let run = || -> Result<MaxFlow, Box<dyn Error>> {
        let g = Digraph::new(2, &[(0, 1)])?;
        let net = Network::new(g, vec![1], 0, 0)?;
        Ok(max_flow(&net))
    };
    let err = run().unwrap_err();
    assert_eq!(
        err.downcast_ref::<FlowsError>(),
        Some(&FlowsError::SourceIsSink { vertex: 0 })
    );
}

#[test]
fn a_rule_can_read_and_change_the_remaining_capacity() -> Result<(), Box<dyn Error>> {
    let net = one_and_thousand()?;
    let mut r = Residual::new(&net);
    // Vertex 1: back against 0 → 1, along 1 → 2, along 1 → 3.
    assert_eq!(r.out(1), [1, 4, 6]);
    r.send(0, 7);
    r.send(6, 7);
    assert_eq!(r.flow(), [7, 0, 0, 7, 0]);
    assert_eq!(r.reached(), [true, true, true, true]);
    Ok(())
}
