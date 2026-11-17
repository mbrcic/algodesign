use super::*;
use crate::flows::{max_flow, naive};
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

/// Push-relabel's answer on `net`, with its counts, after checking it: it passes max flow's checks
/// (a flow, a cut with the source and without the sink, of the flow amount), every loop carries
/// nothing, its amount is Dinic's, and the run without counts gives the same answer.
fn checked<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
) -> Result<(MaxFlow<C>, Counts), TestCaseError> {
    let (answer, counts) = push_relabel_with_counts(net);
    // Lean: PushRelabel.PassesChecks, so PushRelabel.largest_of_passesChecks
    prop_assert_eq!(naive::check(net, &answer), Ok(()));
    let g = net.graph();
    for i in 0..g.arrow_count() {
        let (a, b) = g.arrow(i);
        prop_assert!(a != b || answer.flow[i] == C::ZERO, "loop {} carries", i);
    }
    prop_assert_eq!(answer.value, max_flow(net).value);
    prop_assert_eq!(&push_relabel(net), &answer);
    Ok((answer, counts))
}

fn counts(pushes: u64, relabels: u64, gaps: u64, global_relabels: u64) -> Counts {
    Counts {
        pushes,
        relabels,
        gaps,
        global_relabels,
    }
}

#[test]
fn on_the_one_and_thousand_network_the_excess_runs_straight_down() {
    // 0 → 1 and 0 → 2 carry 1000, 1 → 3 and 2 → 3 carry 1000, the middle arrow 1 → 2 carries 1.
    // Both full source arrows leave 1 and 2 at height 1; 2, put on the stack last, pushes first.
    let net = network(
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
    );
    let (answer, counts_seen) = checked(&net).unwrap();
    assert_eq!(answer.value, 2000);
    assert_eq!(answer.flow, [1000, 1000, 0, 1000, 1000]);
    assert_eq!(answer.flow, max_flow(&net).flow);
    assert_eq!(answer.side, [true, false, false, false]);
    assert_eq!(counts_seen, counts(2, 0, 0, 1));
}

#[test]
fn stranded_excess_goes_back_to_the_source_in_the_second_phase() {
    // 0 → 1 → 2 → 3 with capacities 5, 2, 1: the first phase leaves 3 on 1 and 1 on 2, each
    // relabel to n leaving its height empty (two gap steps); the second phase lifts 2 above 1, then
    // 1 above the source, and sends both back.
    let net = network(4, &[(0, 1, 5), (1, 2, 2), (2, 3, 1)], 0, 3);
    let (answer, counts_seen) = checked(&net).unwrap();
    assert_eq!(answer.value, 1);
    assert_eq!(answer.flow, [1, 1, 1]);
    assert_eq!(answer.side, [true, true, true, false]);
    assert_eq!(counts_seen, counts(4, 4, 2, 1));
}

#[test]
fn parallel_and_antiparallel_arrows_stay_separate_arrows() {
    // 0 → 1 twice (2 and 3), 1 → 0 (4) against them, then 1 → 2 (10).
    let net = network(3, &[(0, 1, 2), (0, 1, 3), (1, 0, 4), (1, 2, 10)], 0, 2);
    let (answer, _) = checked(&net).unwrap();
    assert_eq!(answer.flow, [2, 3, 0, 5]);
    assert_eq!(answer.side, [true, false, false]);
    // Both directions between 1 and 2 with a loop at 1: only 1 → 2 is used, and what does not fit
    // goes back to the source.
    let net = network(3, &[(0, 1, 7), (1, 1, 9), (2, 1, 4), (1, 2, 6)], 0, 2);
    let (answer, _) = checked(&net).unwrap();
    assert_eq!(answer.flow, [6, 0, 0, 6]);
    assert_eq!(answer.side, [true, true, false]);
    // A loop at the source is not filled.
    let net = network(2, &[(0, 0, 9), (0, 1, 4)], 0, 1);
    assert_eq!(checked(&net).unwrap().0.flow, [0, 4]);
}

#[test]
fn a_sink_out_of_reach_gets_nothing_and_the_side_is_what_the_source_reaches() {
    // 0 → 1 and 2 → 3, the sink 3; and 3 → 0 points the wrong way. All of 1's excess goes back.
    let net = network(4, &[(0, 1, 5), (2, 3, 5), (3, 0, 5)], 0, 3);
    let (answer, _) = checked(&net).unwrap();
    assert_eq!(answer.value, 0);
    assert_eq!(answer.flow, [0, 0, 0]);
    assert_eq!(answer.side, [true, true, false, false]);
    // No arrows at all, and arrows of capacity zero.
    assert_eq!(push_relabel(&network(2, &[], 0, 1)).side, [true, false]);
    let net = network(2, &[(0, 1, 0), (0, 1, 0)], 0, 1);
    let (answer, counts_seen) = checked(&net).unwrap();
    assert_eq!((answer.value, answer.flow), (0, vec![0, 0]));
    assert_eq!(counts_seen, counts(0, 0, 0, 1));
}

#[test]
fn capacities_of_u32_hold_excess_beyond_one_capacity() {
    // 2 receives u32::MAX twice: its excess is counted in a u64.
    let net = network_of(
        3,
        &[(0, 1, u32::MAX), (0, 2, u32::MAX), (1, 2, u32::MAX)],
        0,
        2,
    );
    let (answer, _) = checked(&net).unwrap();
    assert_eq!(answer.value, 2 * u64::from(u32::MAX));
    // Through a middle vertex that must hold two full arrows before passing them on.
    let net = network_of(
        4,
        &[
            (0, 1, u32::MAX),
            (0, 1, u32::MAX),
            (1, 2, u32::MAX),
            (2, 3, 7),
        ],
        0,
        3,
    );
    assert_eq!(checked(&net).unwrap().0.value, 7);
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
    fn on_any_small_network_the_amount_is_the_smallest_cut(net in networks()) {
        // Lean: PushRelabel.PushRelabelPromise, by trying every cut
        let (answer, _) = checked(&net)?;
        prop_assert_eq!(u128::from(answer.value), naive::min_cut(&net));
    }
}

/// A draw below `k`.
fn below(r: &mut SplitMix64, k: u64) -> u64 {
    r.next_u64() % k
}

#[test]
fn on_larger_networks_the_amount_is_dinics_and_every_step_is_exercised() {
    // Up to 40 vertices and 160 arrows, capacities over three scales; the cut is the certificate.
    let mut r = SplitMix64::new(11);
    let (mut positive, mut total) = (0, Counts::default());
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
        let (answer, c) = checked(&network(n, &arrows, s, t)).unwrap();
        if answer.value > 0 {
            positive += 1;
        }
        total.pushes += c.pushes;
        total.relabels += c.relabels;
        total.gaps += c.gaps;
        total.global_relabels += c.global_relabels;
    }
    assert!(positive > 100, "{positive} networks with a positive flow");
    // Gap steps fire, and global relabels run after the first one of each network: 30 more than
    // the 300 at the start. The Python's test pins the same totals, step for step.
    assert_eq!(total, counts(6869, 2910, 170, 330));
}
