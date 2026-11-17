use super::*;
use crate::flows::max_flow::max_flow_with_rounds;
use crate::flows::network::Network;
use crate::flows::residual::Augmentation;
use crate::graphs::Digraph;

fn network(n: usize, arrows: &[(u32, u32, u64)], s: u32, t: u32) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let capacity = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), capacity, s, t).unwrap()
}

fn x(path: &[u32], amount: u64) -> Augmentation {
    Augmentation {
        path: path.to_vec(),
        amount,
    }
}

#[test]
fn after_each_path_the_sweep_starts_again_from_the_source() {
    // Lean: dinicSweepSteps
    // 0 → 1 carries 2; 1 → 2 → 4 and 1 → 3 → 4 carry 1. The first path fills 1 → 2.
    let net = network(
        5,
        &[(0, 1, 2), (1, 2, 1), (1, 3, 1), (2, 4, 1), (3, 4, 1)],
        0,
        4,
    );
    let mut rule = Dinic::new();
    let (answer, rounds) = max_flow_with_rounds(&net, &mut rule);
    assert_eq!(rounds, [vec![x(&[0, 2, 6], 1), x(&[0, 4, 8], 1)]]);
    assert_eq!(answer.value, 2);
    // By hand: along 0 → 1 (1), past 1's back arrow (2), along 1 → 2 (3), past 2's back arrow (4),
    // along 2 → 4 (5), send (6); from the source again, along 0 → 1 (7), past the full 1 → 2 (8),
    // along 1 → 3 (9), past 3's back arrow (10), along 3 → 4 (11), send (12); past the full
    // 0 → 1 (13), and the source is a dead end (14). Resuming at 1 after the first path would
    // skip step 7 and count 13.
    assert_eq!(rule.sweep_steps(), [14]);
}

#[test]
fn a_vertex_on_the_sinks_layer_is_a_dead_end_at_once() {
    // 0 → 1 → 3 → 4 and 0 → 2 → 4, every arrow carrying 1: the search labels 3 on the sink's
    // layer before it labels the sink.
    let net = network(
        5,
        &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 4, 1), (3, 4, 1)],
        0,
        4,
    );
    let mut rule = Dinic::new();
    let (answer, rounds) = max_flow_with_rounds(&net, &mut rule);
    assert_eq!(rounds, [vec![x(&[2, 6], 1)], vec![x(&[0, 4, 8], 1)]]);
    assert_eq!(answer.value, 2);
    // A dead end, back one arrow with the tail's pointer moved past it, is one step.
    // Phase 1: along 0 → 1 (1), past 1's back arrow (2), along 1 → 3 (3); 3 is a dead end at
    // once, back to 1 (4); 1 is done, back to 0 (5); along 0 → 2 (6), past 2's back arrow (7),
    // along 2 → 4 (8), send (9); past the full 0 → 2 (10); the source a dead end (11).
    // Phase 2: along 0 → 1 (1), past its back arrow (2), along 1 → 3 (3), past 3's back arrow
    // (4), along 3 → 4 (5), send (6); past the full 0 → 1 and 0 → 2 (8); the source a dead end
    // (9).
    assert_eq!(rule.sweep_steps(), [11, 9]);
    // The same rule on a second network counts that network's phases alone.
    let one = network(2, &[(0, 1, 3)], 0, 1);
    let _ = max_flow_with_rounds(&one, &mut rule);
    // Along 0 → 1 (1), send (2), past the full 0 → 1 (3), the source a dead end (4).
    assert_eq!(rule.sweep_steps(), [4]);
}

#[test]
fn one_phase_sends_a_blocking_flow_and_the_next_finds_longer_paths() {
    // Lean: Ops.RoundsAtMostN
    // Two two-arrow paths 0 → 1 → 5 and 0 → 2 → 5, and 0 → 3 → 4 → 5 three arrows long.
    let net = network(
        6,
        &[
            (0, 1, 1),
            (1, 5, 1),
            (0, 2, 1),
            (2, 5, 1),
            (0, 3, 1),
            (3, 4, 1),
            (4, 5, 1),
        ],
        0,
        5,
    );
    let (answer, rounds) = max_flow_with_rounds(&net, Dinic::new());
    assert_eq!(
        rounds,
        [vec![x(&[0, 2], 1), x(&[4, 6], 1)], vec![x(&[8, 10, 12], 1)]]
    );
    assert_eq!(answer.value, 3);
}
