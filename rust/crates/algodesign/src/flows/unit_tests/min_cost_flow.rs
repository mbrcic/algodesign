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

/// A network and its costs from arrows `(tail, head, capacity, cost)`.
fn priced(n: usize, arrows: &[(u32, u32, u64, i64)], s: u32, t: u32) -> (Network, Vec<i64>) {
    let plain: Vec<(u32, u32, u64)> = arrows.iter().map(|&(a, b, c, _)| (a, b, c)).collect();
    let cost = arrows.iter().map(|&(_, _, _, k)| k).collect();
    (network_of(n, &plain, s, t), cost)
}

fn x(path: &[u32], amount: u64) -> Augmentation {
    Augmentation {
        path: path.to_vec(),
        amount,
    }
}

/// The chapter's vehicles: the source 0; the flats Juan 1, Tomás 2, Anita 3, Daniel 4; the van 5,
/// the car 6; the sink 7. Arrows 0–3 lead from the source to each flat (1 each, free); arrows
/// 4–11 from each flat to the van, then the car (1 each): Juan 1 and 100, Tomás 1 and 100, Anita
/// 3 and 2, Daniel 10 and 5; arrow 12 is the van to the sink (3), arrow 13 the car (1), both free.
fn vehicles() -> (Network, Vec<i64>) {
    priced(
        8,
        &[
            (0, 1, 1, 0),
            (0, 2, 1, 0),
            (0, 3, 1, 0),
            (0, 4, 1, 0),
            (1, 5, 1, 1),
            (1, 6, 1, 100),
            (2, 5, 1, 1),
            (2, 6, 1, 100),
            (3, 5, 1, 3),
            (3, 6, 1, 2),
            (4, 5, 1, 10),
            (4, 6, 1, 5),
            (5, 7, 3, 0),
            (6, 7, 1, 0),
        ],
        0,
        7,
    )
}

/// Whether `answer` and `rounds` meet the contract on the problem `(net, cost, amount)`; the first
/// thing that fails, in words. With `oracle`, the cost is also the smallest found by trying every
/// flow of the same amount.
fn meets_the_contract<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
    cost: &[i64],
    amount: u64,
    answer: &MinCostFlow<C>,
    rounds: &[MinCostRound<C>],
    oracle: bool,
) -> Result<(), String> {
    let (n, m) = (net.n(), net.arrow_count());
    let (s, t) = (net.source() as usize, net.sink() as usize);
    let sent = net_out(net, |i| answer.flow[i].to_u64())[s];
    // Lean: Valid, WellFormed, Ops.SendsAFlow, Ops.CheapestForItsAmount, Ops.HeightsFit,
    // Ops.ShortOnlyAtACut. Without the oracle, invariant 2 is left to the heights, whose fit
    // proves it (Lean `cheapest_of_heightsFit`).
    let cheapest = match u64::try_from(sent) {
        Ok(v) if oracle => naive::cheapest_cost(net, cost, v),
        _ => None,
    };
    answer.check_valid(net, cost, amount, cheapest)?;
    if sent != i128::from(answer.value) {
        return Err(format!(
            "value {} where the flow sends {sent}",
            answer.value
        ));
    }
    let total: i64 = (0..m)
        .map(|i| cost[i] * answer.flow[i].to_u64() as i64)
        .sum();
    if total != answer.cost {
        return Err(format!("cost {} where the flow costs {total}", answer.cost));
    }
    if answer.value != amount.min(max_flow(net).value) {
        return Err("the amount is not the requested one or the largest".into());
    }
    // Lean: Ops.RoundsAtMostAmount
    if rounds.len() as u64 > amount {
        return Err(format!("{} rounds for amount {amount}", rounds.len()));
    }
    // Lean: Ops.walks, Ops.roundsKeep (invariant 3 after every round)
    let mut r = Residual::new(net);
    let mut heights = vec![0; n];
    for (k, round) in rounds.iter().enumerate() {
        let mut at = s as u32;
        for &e in &round.sent.path {
            if (e as usize) >= r.arrow_count()
                || r.tail(e) != at
                || round.sent.amount > r.residual_capacity(e)
            {
                return Err(format!("round {k}: {:?} is no augmenting path", round.sent));
            }
            at = r.head(e);
        }
        if at as usize != t || round.sent.amount < C::ONE {
            return Err(format!(
                "round {k}: {:?} sends nothing to the sink",
                round.sent
            ));
        }
        for &e in &round.sent.path {
            r.send(e, round.sent.amount);
        }
        let state = MinCostFlow {
            value: 0,
            cost: 0,
            flow: r.flow(),
            heights: round.heights.clone(),
            side: Vec::new(),
        };
        if !state.is_heights_fit_everywhere(net, cost) {
            return Err(format!("round {k}: the heights after it do not fit"));
        }
        if round.settled < 2 || round.settled > n {
            return Err(format!("round {k}: {} settled", round.settled));
        }
        heights.clone_from(&round.heights);
    }
    if r.flow() != answer.flow || heights != answer.heights {
        return Err("the rounds do not lead to the answer".into());
    }
    // Lean: Ops.CheapestForItsAmount
    if oracle && naive::cheapest_cost(net, cost, answer.value) != Some(answer.cost) {
        return Err("a cheaper flow of the same amount exists".into());
    }
    Ok(())
}

/// The answer and rounds of the problem, checked against the contract.
fn checked<C: Capacity + TryFrom<u64>>(
    net: &Network<C>,
    cost: &[i64],
    amount: u64,
    oracle: bool,
) -> (MinCostFlow<C>, Vec<MinCostRound<C>>, Vec<usize>) {
    let (answer, rounds, searches) = min_cost_flow_with_rounds(net, cost, amount).unwrap();
    assert_eq!(
        meets_the_contract(net, cost, amount, &answer, &rounds, oracle),
        Ok(())
    );
    // Every round's search, and one more that missed the sink only when the amount was not met.
    let settled: Vec<usize> = rounds.iter().map(|s| s.settled).collect();
    assert_eq!(searches[..rounds.len()], settled[..]);
    let missed = usize::from(answer.value < amount);
    assert_eq!(searches.len(), rounds.len() + missed);
    assert_eq!(min_cost_flow(net, cost, amount).unwrap(), answer);
    (answer, rounds, searches)
}

#[test]
fn the_vehicles_take_the_four_cheapest_rounds_and_the_last_moves_anita_back_to_the_van() {
    // Lean: Ops.steps, Ops.heightsAfter, Ops.walks
    let (net, cost) = vehicles();
    let (answer, rounds, _) = checked(&net, &cost, 4, true);
    let paths: Vec<Augmentation> = rounds.iter().map(|s| s.sent.clone()).collect();
    assert_eq!(
        paths,
        [
            // Juan → van.
            x(&[0, 8, 24], 1),
            // Tomás → van.
            x(&[2, 12, 24], 1),
            // Anita → car.
            x(&[4, 18, 26], 1),
            // Daniel → car, Anita back from the car (back 9, index 19) to the van.
            x(&[6, 22, 19, 16, 24], 1),
        ]
    );
    // By hand. Round 1, all heights 0: the search settles 0, Juan, Tomás, Anita, Daniel at 0, the
    // van at 1 (Juan's arrow labels it first; Tomás's ties and does not take it over) and the sink
    // at 1; the car, known at 2, stays unsettled and adds the sink's 1. Round 2 settles everything
    // but the car at 0, so no height moves. Round 3: from the source only Anita and Daniel have
    // residual capacity, both at 0; the car at 2 + 0 − 1 = 1 (Anita's arrow), the van at 3 − 1 = 2,
    // then the sink at 1 through the car, settled before the van. Settled: the source, Anita,
    // Daniel, the car and the sink, each adding its distance (car and sink 1); Juan, Tomás and the
    // van add the sink's 1.
    assert_eq!(rounds[0].heights, [0, 0, 0, 0, 0, 1, 1, 1]);
    assert_eq!(rounds[1].heights, rounds[0].heights);
    assert_eq!(rounds[2].heights, [0, 1, 1, 0, 0, 2, 2, 2]);
    assert_eq!(rounds[3].heights, [0, 5, 5, 3, 0, 6, 5, 6]);
    assert_eq!(answer.heights, rounds[3].heights);
    assert_eq!(answer.value, 4);
    // The van takes Juan, Tomás and Anita (1 + 1 + 3), the car Daniel (5).
    assert_eq!(answer.cost, 10);
    assert_eq!(answer.flow, [1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 3, 1]);
}

#[test]
fn the_search_stops_as_soon_as_the_sink_is_settled() {
    // Round 3 of the vehicles settles 5 vertices; a search run until its queue is empty would also
    // settle the van at 2 and, back from the van, Juan and Tomás at 2: 8 in all.
    let (net, cost) = vehicles();
    let (_, rounds, searches) = checked(&net, &cost, 4, false);
    let settled: Vec<usize> = rounds.iter().map(|s| s.settled).collect();
    assert_eq!(settled, [7, 7, 5, 8]);
    // The run stops when the amount is sent: no fifth search.
    assert_eq!(searches, [7, 7, 5, 8]);
}

#[test]
fn a_network_that_cannot_carry_the_amount_sends_the_most_with_a_cut_that_proves_it() {
    // Lean: Ops.ShortOnlyAtACut
    let (net, cost) = vehicles();
    let (answer, rounds, searches) = checked(&net, &cost, 5, true);
    assert_eq!((answer.value, answer.cost, rounds.len()), (4, 10, 4));
    // Lean: settledEach. The fifth search settles the source alone and misses the sink.
    assert_eq!(searches, [7, 7, 5, 8, 1]);
    // The fifth search misses the sink: it is no round, and the heights stay as after the fourth.
    assert_eq!(answer.heights, rounds[3].heights);
    assert_eq!(
        answer.side,
        [true, false, false, false, false, false, false, false]
    );
    // A sink out of reach: no round, the side is what the source reaches.
    let (net, cost) = priced(3, &[(0, 1, 2, 1), (2, 1, 2, 1)], 0, 2);
    let (answer, rounds, _) = checked(&net, &cost, 3, true);
    assert_eq!((answer.value, answer.cost), (0, 0));
    assert!(rounds.is_empty());
    assert_eq!(answer.side, [true, true, false]);
    assert_eq!(answer.heights, [0, 0, 0]);
}

#[test]
fn on_a_tie_the_first_vertex_labeled_keeps_the_arrow_that_labeled_it() {
    // 0 → 1 costs 1 (arrow 0), 0 → 2 costs 0 (1), 2 → 1 costs 1 (2), 1 → 3 costs 0 (3). Vertex 1
    // is labeled at 1 from the source; the arrow from 2 also reaches it at 1 and does not take
    // the label over.
    let (net, cost) = priced(
        4,
        &[(0, 1, 1, 1), (0, 2, 1, 0), (2, 1, 1, 1), (1, 3, 1, 0)],
        0,
        3,
    );
    let (_, rounds, _) = checked(&net, &cost, 1, true);
    assert_eq!(rounds[0].sent, x(&[0, 6], 1));
    // Two arrows 0 → 1 of the same cost: the first in the row wins.
    let (net, cost) = priced(2, &[(0, 1, 1, 2), (0, 1, 1, 2)], 0, 1);
    let (_, rounds, _) = checked(&net, &cost, 1, true);
    assert_eq!(rounds[0].sent, x(&[0], 1));
}

#[test]
fn the_queue_breaks_a_tie_of_distances_by_vertex_id() {
    // 0 → 2 (arrow 0) and 0 → 1 (arrow 1), then 2 → 3 (2) and 1 → 3 (3), all free: 2 is queued
    // first, but 1 comes off first and labels the sink.
    let (net, cost) = priced(
        4,
        &[(0, 2, 1, 0), (0, 1, 1, 0), (2, 3, 1, 0), (1, 3, 1, 0)],
        0,
        3,
    );
    let (_, rounds, _) = checked(&net, &cost, 1, true);
    assert_eq!(rounds[0].sent, x(&[2, 6], 1));
}

#[test]
fn a_round_sends_its_bottleneck_or_what_is_still_requested_if_less() {
    let (net, cost) = priced(3, &[(0, 1, 10, 1), (1, 2, 7, 1), (0, 2, 4, 3)], 0, 2);
    let (answer, rounds, _) = checked(&net, &cost, 9, true);
    assert_eq!(rounds[0].sent, x(&[0, 2], 7));
    assert_eq!(rounds[1].sent, x(&[4], 2));
    assert_eq!((answer.value, answer.cost), (9, 7 * 2 + 2 * 3));
    // Nothing requested: no search, the zero flow, all heights zero.
    let (answer, rounds, _) = checked(&net, &cost, 0, true);
    assert!(rounds.is_empty());
    assert_eq!((answer.value, answer.cost), (0, 0));
    assert_eq!(answer.heights, [0, 0, 0]);
}

#[test]
fn a_cost_count_mismatch_and_a_negative_cost_are_refused() {
    // Lean: Problem.WellFormed, Problem.NoArrowBelowZero
    let (net, _) = priced(2, &[(0, 1, 1, 0), (0, 1, 1, 0)], 0, 1);
    assert_eq!(
        min_cost_flow(&net, &[1], 1),
        Err(FlowsError::CostCountMismatch {
            costs: 1,
            arrows: 2
        })
    );
    assert_eq!(
        min_cost_flow(&net, &[0, -3], 1),
        Err(FlowsError::NegativeCost { arrow: 1, cost: -3 })
    );
    assert_eq!(
        min_cost_flow_with_rounds(&net, &[0, -3], 1).err(),
        Some(FlowsError::NegativeCost { arrow: 1, cost: -3 })
    );
}

#[test]
fn costs_adding_up_past_a_quarter_of_i64_are_refused_and_at_the_limit_kept() {
    let limit = i64::MAX / 4;
    let (net, cost) = priced(3, &[(0, 1, 1, limit - 1), (1, 2, 1, 2)], 0, 2);
    assert_eq!(
        min_cost_flow(&net, &cost, 1),
        Err(FlowsError::CostSumTooLarge)
    );
    assert_eq!(
        FlowsError::CostSumTooLarge.to_string(),
        "the costs add up to more than i64::MAX / 4"
    );
    let (net, cost) = priced(3, &[(0, 1, 1, limit - 1), (1, 2, 1, 1)], 0, 2);
    let answer = min_cost_flow(&net, &cost, 1).unwrap();
    assert_eq!((answer.value, answer.cost), (1, limit));
    assert_eq!(answer.heights, [0, limit - 1, limit]);
}

#[test]
fn a_total_cost_past_i64_is_refused_and_one_at_the_edge_is_kept() {
    // One arrow, capacity 2^63 at cost 1: the total is 2^63, one past i64::MAX.
    let (net, cost) = priced(2, &[(0, 1, 1 << 63, 1)], 0, 1);
    assert_eq!(
        min_cost_flow(&net, &cost, 1 << 63),
        Err(FlowsError::TotalCostTooLarge)
    );
    // Capacity 2^62 at cost 4: the total is 2^64.
    let (net, cost) = priced(2, &[(0, 1, 1 << 62, 4)], 0, 1);
    assert_eq!(
        min_cost_flow(&net, &cost, 1 << 62),
        Err(FlowsError::TotalCostTooLarge)
    );
    assert_eq!(
        FlowsError::TotalCostTooLarge.to_string(),
        "the flow's total cost does not fit an i64"
    );
    // Capacity 2^63 - 1 at cost 1: the total is i64::MAX, which fits.
    let (net, cost) = priced(2, &[(0, 1, (1 << 63) - 1, 1)], 0, 1);
    let answer = min_cost_flow(&net, &cost, u64::MAX).unwrap();
    assert_eq!((answer.value, answer.cost), ((1 << 63) - 1, i64::MAX));
}

#[test]
fn capacities_of_u32_give_the_same_answers_as_of_u64() {
    let (wide, cost) = vehicles();
    let narrow_arrows: Vec<(u32, u32, u32)> = (0..wide.arrow_count())
        .map(|i| {
            let (a, b) = wide.graph().arrow(i);
            (a, b, wide.arrow_capacity(i) as u32)
        })
        .collect();
    let narrow = network_of(8, &narrow_arrows, 0, 7);
    let (w, _, _) = checked(&wide, &cost, 4, false);
    let (n, _, _) = checked(&narrow, &cost, 4, false);
    assert_eq!(
        (n.value, n.cost, &n.heights, &n.side),
        (w.value, w.cost, &w.heights, &w.side)
    );
    // An amount past u32::MAX: the rest does not fit a u32, the bottleneck is sent.
    let net = network_of(2, &[(0, 1, u32::MAX)], 0, 1);
    let (answer, _, _) = checked(&net, &[2], u64::MAX, false);
    assert_eq!(answer.value, u64::from(u32::MAX));
}

/// A tiny priced network: few arrows of capacity up to 2, so trying every flow stays quick.
fn tiny() -> impl Strategy<Value = (Network, Vec<i64>, u64)> {
    (2usize..=5).prop_flat_map(|n| {
        let m = n as u32;
        (
            prop::collection::vec((0..m, 0..m, 0u64..3, 0i64..6), 0..7),
            0..m,
            1..m,
            0u64..6,
        )
            .prop_map(move |(arrows, s, k, amount)| {
                let (net, cost) = priced(n, &arrows, s, (s + k) % m);
                (net, cost, amount)
            })
    })
}

proptest! {
    #[test]
    fn on_any_tiny_network_the_answer_is_the_cheapest_for_its_amount(
        (net, cost, amount) in tiny()
    ) {
        // Lean: Contract.promise, Ops.RoundsAtMostAmount
        let (answer, rounds, _) = min_cost_flow_with_rounds(&net, &cost, amount).unwrap();
        prop_assert_eq!(meets_the_contract(&net, &cost, amount, &answer, &rounds, true), Ok(()));
    }
}

/// A draw below `k`.
fn below(r: &mut SplitMix64, k: u64) -> u64 {
    r.next_u64() % k
}

#[test]
fn on_larger_networks_the_heights_certify_every_answer() {
    // Up to 30 vertices and 120 arrows; the heights are the certificate, no oracle.
    let mut r = SplitMix64::new(11);
    let mut positive = 0;
    for _ in 0..200 {
        let n = 2 + below(&mut r, 29) as usize;
        let m = below(&mut r, 121) as usize;
        let arrows: Vec<(u32, u32, u64, i64)> = (0..m)
            .map(|_| {
                let a = below(&mut r, n as u64) as u32;
                let b = below(&mut r, n as u64) as u32;
                (a, b, below(&mut r, 8), below(&mut r, 50) as i64)
            })
            .collect();
        let s = below(&mut r, n as u64) as u32;
        let t = (s + 1 + below(&mut r, n as u64 - 1) as u32) % n as u32;
        let (net, cost) = priced(n, &arrows, s, t);
        let amount = below(&mut r, 40);
        let (answer, _, _) = checked(&net, &cost, amount, false);
        if answer.value > 0 {
            positive += 1;
        }
    }
    assert!(positive > 60, "{positive} networks with a positive flow");
}

#[test]
fn on_the_tie_network_the_first_arrow_to_reach_the_sink_wins_and_the_heights_rise_together() {
    // The source 0, a 1, b 2, the sink 3; 0 → a (arrow 0), 0 → b (1), a → 3 twice (2 and 3),
    // b → 3 (4); each carries 1 and costs 1. Round 1: a and b both at 1 offer the sink at 2; a,
    // the lower id, comes off first and its first arrow labels the sink. Round 2: b at 0, then
    // the sink at 1 + 1 − 2 = 0 through b.
    let (net, cost) = priced(
        4,
        &[
            (0, 1, 1, 1),
            (0, 2, 1, 1),
            (1, 3, 1, 1),
            (1, 3, 1, 1),
            (2, 3, 1, 1),
        ],
        0,
        3,
    );
    let (answer, rounds, _) = checked(&net, &cost, 2, true);
    assert_eq!(rounds[0].sent, x(&[0, 4], 1));
    assert_eq!(rounds[0].heights, [0, 1, 1, 2]);
    assert_eq!(rounds[1].sent, x(&[2, 8], 1));
    assert_eq!((answer.value, answer.cost), (2, 4));
}

#[test]
fn check_valid_names_each_broken_piece_alone() {
    let (net, cost) = priced(3, &[(0, 1, 10, 1), (1, 2, 7, 1), (0, 2, 4, 3)], 0, 2);
    let good = min_cost_flow(&net, &cost, 9).unwrap();
    // Changed costs 0, -1 and 0: arrow 0 partly loaded, arrow 1 full, arrow 2 partly loaded.
    assert_eq!(
        (&good.flow[..], &good.heights[..], &good.side[..]),
        (&[7u64, 7, 2][..], &[0i64, 1, 3][..], &[true; 3][..])
    );
    assert_eq!(good.check_valid(&net, &cost, 9, Some(20)), Ok(()));
    assert!(good.is_valid(&net, &cost, 9, Some(20)));
    let cheapest = |a: &MinCostFlow| {
        let sent = net_out(&net, |i| a.flow.get(i).copied().unwrap_or(0))[0];
        naive::cheapest_cost(&net, &cost, u64::try_from(sent).unwrap())
    };
    let answer = |flow: &[u64], heights: &[i64], side: &[bool]| MinCostFlow {
        value: 0,
        cost: 0,
        flow: flow.to_vec(),
        heights: heights.to_vec(),
        side: side.to_vec(),
    };
    let all = [true; 3];
    let cases = [
        // Lean: FlowRespected; arrow 2 carries 5 over its 4, full, so its changed cost 0 fits.
        (
            answer(&[7, 7, 5], &[0, 1, 3], &all),
            12,
            "invariant 1 (flow_respected)",
        ),
        // Lean: FlowRespected; vertex 1 takes in 8 and lets out 7.
        (
            answer(&[8, 7, 2], &[0, 1, 3], &all),
            10,
            "invariant 1 (flow_respected)",
        ),
        // Lean: CheapestForAmount; 9 sent at cost 22, where 20 is the cheapest for 9.
        (
            answer(&[5, 5, 4], &[0, 1, 3], &all),
            9,
            "invariant 2 (cheapest_for_amount)",
        ),
        // Lean: HeightsFitEverywhere; arrow 2's changed cost 1 on a partly loaded arrow.
        (
            answer(&[7, 7, 2], &[0, 1, 2], &all),
            9,
            "invariant 3 (heights_fit_everywhere)",
        ),
        // Lean: WellFormed; a height or an amount too many.
        (
            answer(&[7, 7, 2], &[0, 1, 3, 0], &all),
            9,
            "not in the box (well_formed)",
        ),
        (
            answer(&[7, 7, 2, 0], &[0, 1, 3], &all),
            9,
            "not in the box (well_formed)",
        ),
        // Lean: Ops.SendsAFlow; 9 sent where 8 were requested.
        (
            answer(&[7, 7, 2], &[0, 1, 3], &all),
            8,
            "promise (sends_a_flow)",
        ),
        // Lean: Ops.ShortOnlyAtACut; 9 sent of 10, and the side holds the sink or marks too few.
        (
            answer(&[7, 7, 2], &[0, 1, 3], &all),
            10,
            "promise (short_only_at_a_cut)",
        ),
        (
            answer(&[7, 7, 2], &[0, 1, 3], &[true]),
            10,
            "promise (short_only_at_a_cut)",
        ),
    ];
    for (a, amount, label) in &cases {
        assert_eq!(
            a.check_valid(&net, &cost, *amount, cheapest(a)),
            Err(*label),
            "{a:?} {amount}"
        );
        assert!(!a.is_valid(&net, &cost, *amount, cheapest(a)));
    }
    // A short flow whose side is a cut of its amount passes.
    let short = min_cost_flow(&net, &cost, 12).unwrap();
    assert_eq!(
        (short.value, &short.side[..]),
        (11, &[true, true, false][..])
    );
    assert_eq!(short.check_valid(&net, &cost, 12, cheapest(&short)), Ok(()));
}

#[test]
fn cheapest_for_amount_compares_the_flows_cost_with_the_cheapest_given() {
    // Lean: CheapestForAmount; arrows 0 → 1 costing 1 and 3, each carrying up to 1.
    let (net, cost) = priced(2, &[(0, 1, 1, 1), (0, 1, 1, 3)], 0, 1);
    assert_eq!(naive::cheapest_cost(&net, &cost, 1), Some(1));
    let flow = |flow: &[u64]| MinCostFlow {
        value: 0,
        cost: 0,
        flow: flow.to_vec(),
        heights: Vec::new(),
        side: Vec::new(),
    };
    assert!(flow(&[1, 0]).is_cheapest_for_amount(&net, &cost, Some(1)));
    assert!(!flow(&[0, 1]).is_cheapest_for_amount(&net, &cost, Some(1)));
    // No flow sends 3, so no flow of that amount is cheaper; a missing amount reads as 0.
    assert_eq!(naive::cheapest_cost(&net, &cost, 3), None);
    assert!(flow(&[2, 1]).is_cheapest_for_amount(&net, &cost, None));
    assert!(flow(&[1]).is_cheapest_for_amount(&net, &cost, Some(1)));
}

#[test]
fn the_heights_fit_by_the_rule_per_arrow() {
    // One arrow 0 → 1 of capacity 2 and cost 0; its changed cost is h(0) - h(1).
    let (net, cost) = priced(2, &[(0, 1, 2, 0)], 0, 1);
    let fits = |changed: i64, x: u64| {
        MinCostFlow {
            value: 0,
            cost: 0,
            flow: vec![x],
            heights: vec![changed, 0],
            side: Vec::new(),
        }
        .is_heights_fit_everywhere(&net, &cost)
    };
    // Empty: at least zero; partly loaded: zero; full: at most zero.
    let table: Vec<bool> = [-1, 0, 1]
        .iter()
        .flat_map(|&c| [0, 1, 2].map(|x| fits(c, x)))
        .collect();
    assert_eq!(
        table,
        [false, false, true, true, true, true, true, false, false]
    );
    // An arrow of capacity 0 has no residual capacity either way, so any heights fit it.
    let (net, cost) = priced(2, &[(0, 1, 0, 0)], 0, 1);
    assert!([-5, 0, 5].iter().all(|&h| MinCostFlow {
        value: 0,
        cost: 0,
        flow: vec![0u64],
        heights: vec![h, 0],
        side: Vec::new(),
    }
    .is_heights_fit_everywhere(&net, &cost)));
}
