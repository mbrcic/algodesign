use super::*;
use crate::flows::{naive, CapacityScaling, EdmondsKarp};
use crate::graphs::Digraph;
use crate::rng::SplitMix64;
use proptest::prelude::*;

fn network_of<C: Capacity>(n: usize, arrows: &[(u32, u32, C)], s: u32, t: u32) -> Network<C> {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let capacity = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), capacity, s, t).unwrap()
}

fn network(n: usize, arrows: &[(u32, u32, u64)], s: u32, t: u32) -> Network {
    network_of(n, arrows, s, t)
}

/// The rounds of one run: the paths each round added, in order.
type Rounds<C> = Vec<Vec<Augmentation<C>>>;

/// Each of the library's rules by name, with its answer and its rounds.
fn every_rule<C: Capacity>(net: &Network<C>) -> [(&'static str, MaxFlow<C>, Rounds<C>); 3] {
    let (dinic, dinic_rounds) = max_flow_with_rounds(net, Dinic::new());
    let (ek, ek_rounds) = max_flow_with_rounds(net, EdmondsKarp::new());
    let (scaling, scaling_rounds) = max_flow_with_rounds(net, CapacityScaling::new());
    [
        ("Dinic", dinic, dinic_rounds),
        ("Edmonds–Karp", ek, ek_rounds),
        ("capacity scaling", scaling, scaling_rounds),
    ]
}

/// Whether `rounds`, applied in order from the zero flow, are augmenting paths in turn, each
/// carrying at least one unit within the residual capacity of every arrow on it, and lead to the
/// answer's flow; and no round is empty. The first thing that fails, in words.
fn replays<C: Capacity>(
    net: &Network<C>,
    answer: &MaxFlow<C>,
    rounds: &Rounds<C>,
) -> Result<(), String> {
    let mut r = Residual::new(net);
    let (s, t) = (net.source(), net.sink());
    for (k, round) in rounds.iter().enumerate() {
        if round.is_empty() {
            return Err(format!("round {k} is listed and added nothing"));
        }
        for x in round {
            // Lean: IsAugmentingPath, FitInTurn, PathRule.AddsAtLeastOne
            let mut passed = vec![false; net.n()];
            passed[s as usize] = true;
            let mut at = s;
            for &e in &x.path {
                if (e as usize) >= r.arrow_count() || r.tail(e) != at {
                    return Err(format!("round {k}: {:?} is not a path", x.path));
                }
                at = r.head(e);
                if passed[at as usize] {
                    return Err(format!("round {k}: {:?} passes {at} twice", x.path));
                }
                passed[at as usize] = true;
                if x.amount > r.residual_capacity(e) {
                    return Err(format!("round {k}: {:?} overfills {e}", x.path));
                }
            }
            if at != t {
                return Err(format!("round {k}: {:?} does not reach the sink", x.path));
            }
            if x.amount < C::ONE {
                return Err(format!("round {k}: {:?} carries nothing", x.path));
            }
            for &e in &x.path {
                r.send(e, x.amount);
            }
        }
    }
    // Lean: Ops.walks
    if r.flow() != answer.flow {
        return Err("the rounds do not add up to the answer's flow".to_string());
    }
    Ok(())
}

/// Every rule's answer meets the contract on `net` and is backed by its rounds, all rules agree
/// on the amount, and the bounds of each hold. With `oracle`, the amount is also the smallest cut
/// found by trying every one. The amount.
fn every_rule_meets_the_contract<C: Capacity>(
    net: &Network<C>,
    oracle: bool,
) -> Result<u64, TestCaseError> {
    let (n, m) = (net.n(), net.arrow_count());
    let runs = every_rule(net);
    let value = runs[0].1.value;
    for (name, answer, rounds) in &runs {
        // Lean: Ops.ReturnsAFlow, Ops.CutMatchesFlow
        prop_assert_eq!(naive::check(net, answer), Ok(()), "{}", name);
        prop_assert_eq!(replays(net, answer, rounds), Ok(()), "{}", name);
        prop_assert_eq!(answer.value, value, "{}", name);
        // Lean: Ops.FinishesWithIntegers
        let added: usize = rounds.iter().map(Vec::len).sum();
        prop_assert!(added as u64 <= answer.value, "{}", name);
    }
    if oracle {
        // Lean: Ops.Largest
        prop_assert_eq!(u128::from(value), naive::min_cut(net));
    }
    // Lean: Ops.RoundsAtMostN
    prop_assert!(runs[0].2.len() <= n);
    // Lean: Ops.AugmentationsAtMostNM
    prop_assert!(runs[1].2.iter().map(Vec::len).sum::<usize>() <= n * m);
    // Edmonds–Karp and capacity scaling send one path per round.
    prop_assert!(runs[1..]
        .iter()
        .all(|(_, _, rounds)| rounds.iter().all(|x| x.len() == 1)));
    prop_assert_eq!(&max_flow(net), &runs[0].1);
    Ok(value)
}

/// The chapter's network: 0 → 1 and 0 → 2 carry 1000, 1 → 3 and 2 → 3 carry 1000, and the middle
/// arrow 1 → 2 carries 1.
fn one_and_thousand() -> Network {
    network(
        4,
        &[
            (0, 1, 1000),
            (0, 2, 1000),
            (1, 2, 1),
            (1, 3, 1000),
            (2, 3, 1000),
        ],
        0,
        3,
    )
}

fn x(path: &[u32], amount: u64) -> Augmentation {
    Augmentation {
        path: path.to_vec(),
        amount,
    }
}

#[test]
fn on_the_one_and_thousand_network_no_rule_touches_the_middle_arrow() {
    // Lean: Ops.walks, Ops.rounds
    let net = one_and_thousand();
    let value = every_rule_meets_the_contract(&net, true).unwrap();
    assert_eq!(value, 2000);
    let [(_, dinic, dinic_rounds), (_, ek, ek_rounds), (_, scaling, scaling_rounds)] =
        every_rule(&net);
    // Dinic: one phase sends both two-arrow paths.
    assert_eq!(dinic_rounds, [vec![x(&[0, 6], 1000), x(&[2, 8], 1000)]]);
    // Edmonds–Karp and capacity scaling (Δ = 512): the same paths, one per round.
    assert_eq!(ek_rounds, [vec![x(&[0, 6], 1000)], vec![x(&[2, 8], 1000)]]);
    assert_eq!(scaling_rounds, ek_rounds);
    for answer in [&dinic, &ek, &scaling] {
        assert_eq!(answer.flow, [1000, 1000, 0, 1000, 1000]);
        assert_eq!(answer.side, [true, false, false, false]);
    }
}

#[test]
fn parallel_and_antiparallel_arrows_stay_separate_arrows() {
    // 0 → 1 twice (2 and 3), 1 → 0 (4) against them, then 1 → 2 (10).
    let net = network(3, &[(0, 1, 2), (0, 1, 3), (1, 0, 4), (1, 2, 10)], 0, 2);
    assert_eq!(every_rule_meets_the_contract(&net, true).unwrap(), 5);
    for (name, answer, _) in every_rule(&net) {
        assert_eq!(answer.flow, [2, 3, 0, 5], "{name}");
        assert_eq!(answer.side, [true, false, false], "{name}");
    }
    // Both directions between 1 and 2 with a loop at 1: only 1 → 2 is used.
    let net = network(3, &[(0, 1, 7), (1, 1, 9), (2, 1, 4), (1, 2, 6)], 0, 2);
    assert_eq!(every_rule_meets_the_contract(&net, true).unwrap(), 6);
    for (name, answer, _) in every_rule(&net) {
        assert_eq!(answer.flow, [6, 0, 0, 6], "{name}");
        assert_eq!(answer.side, [true, true, false], "{name}");
    }
}

#[test]
fn a_sink_out_of_reach_gets_nothing_and_the_side_is_what_the_source_reaches() {
    // Lean: PathRule.NoneOnlyWhenDone, Flows.reached
    // 0 → 1 and 2 → 3, the sink 3; and 3 → 0 points the wrong way.
    let net = network(4, &[(0, 1, 5), (2, 3, 5), (3, 0, 5)], 0, 3);
    for (name, answer, rounds) in every_rule(&net) {
        assert_eq!(answer.value, 0, "{name}");
        assert_eq!(answer.flow, [0, 0, 0], "{name}");
        assert_eq!(answer.side, [true, true, false, false], "{name}");
        assert!(rounds.is_empty(), "{name}");
    }
    // No arrows at all, and arrows of capacity zero.
    let net = network(2, &[], 0, 1);
    assert_eq!(max_flow(&net).side, [true, false]);
    let net = network(2, &[(0, 1, 0), (0, 1, 0)], 0, 1);
    assert_eq!(every_rule_meets_the_contract(&net, true).unwrap(), 0);
}

/// A rule that sends what Edmonds–Karp's sends for `rounds` rounds, then nothing, counting the
/// rounds it was asked for.
struct Stopping {
    inner: EdmondsKarp,
    rounds: usize,
    asked: usize,
}

impl PathRule<u64> for Stopping {
    fn start(&mut self, r: &Residual<u64>) {
        PathRule::<u64>::start(&mut self.inner, r);
    }

    fn round(&mut self, r: &mut Residual<u64>) -> bool {
        self.asked += 1;
        self.asked <= self.rounds && self.inner.round(r)
    }
}

#[test]
fn the_loop_ends_at_the_first_round_that_sends_nothing() {
    // Lean: PathRule.runRounds
    let net = one_and_thousand();
    let mut rule = Stopping {
        inner: EdmondsKarp::new(),
        rounds: 1,
        asked: 0,
    };
    let (answer, rounds) = max_flow_with_rounds(&net, &mut rule);
    assert_eq!(rule.asked, 2);
    assert_eq!(rounds, [vec![x(&[0, 6], 1000)]]);
    // The answer is the flow so far, and the side what it leaves reachable: 2 and 3 along
    // 0 → 2 → 3, and 1 back against 1 → 3. This rule broke its promise, so the sink is reached
    // and the cut is no cut.
    assert_eq!(answer.value, 1000);
    assert_eq!(answer.side, [true, true, true, true]);
    assert_eq!(
        naive::check(&net, &answer),
        Err("promise (cut_matches_flow)")
    );
}

/// A rule that breaks the promise: it sends one unit along arrow 1, into the source, then stops.
struct IntoTheSource {
    sent: bool,
}

impl PathRule<u64> for IntoTheSource {
    fn round(&mut self, r: &mut Residual<u64>) -> bool {
        if self.sent {
            return false;
        }
        self.sent = true;
        r.send(2, 1);
        true
    }
}

#[test]
#[should_panic(expected = "the path rule broke its promise: more flow enters the source")]
fn a_rule_that_leaves_more_flow_entering_the_source_than_leaving_it_panics() {
    // Arrow 0 is 0 → 2, arrow 1 is 1 → 0: one unit along arrow 1 enters the source.
    let net = network(3, &[(0, 2, 1), (1, 0, 1)], 0, 2);
    let _ = max_flow_with(&net, IntoTheSource { sent: false });
}

#[test]
fn capacities_of_u32_give_the_same_answers_as_of_u64() {
    let arrows = [
        (0, 1, 3),
        (0, 2, 2),
        (1, 2, 2),
        (1, 3, 1),
        (2, 3, 3),
        (3, 1, 2),
    ];
    let wide = network(4, &arrows, 0, 3);
    let narrow_arrows: Vec<(u32, u32, u32)> =
        arrows.iter().map(|&(a, b, c)| (a, b, c as u32)).collect();
    let narrow = network_of(4, &narrow_arrows, 0, 3);
    let wide_runs = every_rule(&wide);
    for (k, (name, answer, _)) in every_rule(&narrow).into_iter().enumerate() {
        assert_eq!(answer.value, wide_runs[k].1.value, "{name}");
        let flow: Vec<u64> = answer.flow.iter().map(|&c| u64::from(c)).collect();
        assert_eq!(flow, wide_runs[k].1.flow, "{name}");
        assert_eq!(answer.side, wide_runs[k].1.side, "{name}");
    }
    assert_eq!(every_rule_meets_the_contract(&narrow, true).unwrap(), 4);
    // The largest capacities: the amount is summed in a u64.
    let net = network_of(
        3,
        &[(0, 1, u32::MAX), (0, 2, u32::MAX), (1, 2, u32::MAX)],
        0,
        2,
    );
    assert_eq!(
        every_rule_meets_the_contract(&net, true).unwrap(),
        2 * u64::from(u32::MAX)
    );
}

/// A small network: loops, doubled and opposite arrows, zero capacities and ties come often.
fn networks() -> impl Strategy<Value = Network> {
    (2usize..=7).prop_flat_map(|n| {
        let m = n as u32;
        (
            prop::collection::vec((0..m, 0..m, 0u64..6), 0..15),
            0..m,
            1..m,
        )
            .prop_map(move |(arrows, s, k)| network(n, &arrows, s, (s + k) % m))
    })
}

proptest! {
    #[test]
    fn on_any_small_network_every_rule_keeps_the_promise_and_finds_the_smallest_cut(
        net in networks()
    ) {
        // Lean: PathRule.Promise, Contract.promise, Ops.RoundsAtMostN, Ops.AugmentationsAtMostNM
        every_rule_meets_the_contract(&net, true)?;
    }
}

/// A draw below `k`.
fn below(r: &mut SplitMix64, k: u64) -> u64 {
    r.next_u64() % k
}

#[test]
fn on_larger_networks_every_rule_agrees_and_the_bounds_hold() {
    // Up to 40 vertices and 160 arrows, capacities spread over three scales so that capacity
    // scaling halves often; the cut is the certificate, no oracle.
    let mut r = SplitMix64::new(7);
    let mut positive = 0;
    for _ in 0..300 {
        let n = 2 + below(&mut r, 39) as usize;
        let m = below(&mut r, 161) as usize;
        let scale = [4, 100, 1 << 20][below(&mut r, 3) as usize];
        let arrows: Vec<(u32, u32, u64)> = (0..m)
            .map(|_| {
                let a = below(&mut r, n as u64) as u32;
                let b = below(&mut r, n as u64) as u32;
                (a, b, below(&mut r, scale))
            })
            .collect();
        let s = below(&mut r, n as u64) as u32;
        let t = (s + 1 + below(&mut r, n as u64 - 1) as u32) % n as u32;
        let net = network(n, &arrows, s, t);
        if every_rule_meets_the_contract(&net, false).unwrap() > 0 {
            positive += 1;
        }
    }
    assert!(positive > 100, "{positive} networks with a positive flow");
}

#[test]
fn check_valid_names_each_broken_piece_alone() {
    // The library's answer on the chapter's network, then one piece broken at a time.
    let net = one_and_thousand();
    let good = max_flow(&net);
    assert_eq!(good.check_valid(&net), Ok(()));
    assert!(good.is_valid(&net));
    let answer = |flow: &[u64], side: &[bool]| MaxFlow {
        value: 2000,
        flow: flow.to_vec(),
        side: side.to_vec(),
    };
    let mut longer = good.flow.clone();
    longer.push(0);
    let cases = [
        // Lean: WithinCapacity; the middle arrow carries 2 over its 1, and the arrows after it
        // make up the difference.
        (
            answer(&[1000, 1000, 2, 998, 1002], &good.side),
            "invariant 1 (within_capacity)",
        ),
        // Lean: Conserved; vertex 1 takes in 1000 and lets out 999.
        (
            answer(&[1000, 1000, 0, 999, 1000], &good.side),
            "invariant 2 (conserved)",
        ),
        // Lean: WellFormed; one amount too many, a zero on no arrow.
        (answer(&longer, &good.side), "not in the box (well_formed)"),
        // Lean: Ops.CutMatchesFlow; the side holds the sink, misses the source, has the wrong
        // capacity, or marks too few vertices.
        (answer(&good.flow, &[true; 4]), "promise (cut_matches_flow)"),
        (
            answer(&good.flow, &[false; 4]),
            "promise (cut_matches_flow)",
        ),
        (
            answer(&good.flow, &[true, true, false, false]),
            "promise (cut_matches_flow)",
        ),
        (answer(&good.flow, &[true]), "promise (cut_matches_flow)"),
    ];
    for (a, label) in &cases {
        assert_eq!(a.check_valid(&net), Err(*label), "{a:?}");
        assert!(!a.is_valid(&net));
    }
    // A short flow list breaks only `WellFormed`: a missing amount reads as 0.
    let zero = network(
        4,
        &[(0, 1, 0), (0, 2, 0), (1, 2, 0), (1, 3, 0), (2, 3, 0)],
        0,
        3,
    );
    let short = MaxFlow {
        value: 0,
        flow: vec![0u64; 4],
        side: vec![true, false, false, false],
    };
    assert_eq!(
        short.check_valid(&zero),
        Err("not in the box (well_formed)")
    );
    // The reported amount has no piece; the test helper checks it.
    let wrong_value = MaxFlow {
        value: 1999,
        ..good.clone()
    };
    assert_eq!(wrong_value.check_valid(&net), Ok(()));
    assert_eq!(naive::check(&net, &wrong_value), Err("value"));
}
