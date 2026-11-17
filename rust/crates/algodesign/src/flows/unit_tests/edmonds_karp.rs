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
fn the_first_vertex_labeled_keeps_the_arrow_that_labeled_it() {
    // 0 → 1 → 3 and 0 → 2 → 3, then 3 → 4: vertex 3 is labeled from 1 first, and the arrow from
    // 2 does not take the label over.
    let net = network(
        5,
        &[(0, 1, 1), (0, 2, 1), (1, 3, 1), (2, 3, 1), (3, 4, 2)],
        0,
        4,
    );
    let (answer, rounds) = max_flow_with_rounds(&net, EdmondsKarp::new());
    assert_eq!(rounds, [vec![x(&[0, 4, 8], 1)], vec![x(&[2, 6, 8], 1)]]);
    assert_eq!(answer.value, 2);
}

#[test]
fn a_later_path_takes_back_part_of_what_an_earlier_one_sent() {
    // 0 → 1 → 2 → 3 is the first shortest path; then 0 → 4 → 2, back against 1 → 2, and
    // 1 → 5 → 3. Every arrow carries 1.
    let net = network(
        6,
        &[
            (0, 1, 1),
            (1, 2, 1),
            (2, 3, 1),
            (0, 4, 1),
            (4, 2, 1),
            (1, 5, 1),
            (5, 3, 1),
        ],
        0,
        3,
    );
    let (answer, rounds) = max_flow_with_rounds(&net, EdmondsKarp::new());
    assert_eq!(
        rounds,
        [vec![x(&[0, 2, 4], 1)], vec![x(&[6, 8, 3, 10, 12], 1)]]
    );
    assert_eq!(answer.flow, [1, 0, 1, 1, 1, 1, 1]);
    assert_eq!(answer.value, 2);
}

#[test]
fn a_search_that_misses_the_sink_sends_nothing() {
    // Lean: PathRule.NoneOnlyWhenDone
    let net = network(3, &[(0, 1, 4), (2, 1, 4)], 0, 2);
    let mut r = Residual::new(&net);
    let mut rule = EdmondsKarp::new();
    assert!(!PathRule::<u64>::round(&mut rule, &mut r));
    assert_eq!(r.flow(), [0, 0]);
}
