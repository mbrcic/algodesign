use super::*;
use crate::graphs::Digraph;

fn network(n: usize, arrows: &[(u32, u32, u64)], s: u32, t: u32) -> Network {
    let ends: Vec<(u32, u32)> = arrows.iter().map(|&(a, b, _)| (a, b)).collect();
    let capacity = arrows.iter().map(|&(_, _, c)| c).collect();
    Network::new(Digraph::new(n, &ends).unwrap(), capacity, s, t).unwrap()
}

#[test]
fn each_row_lists_along_at_the_tail_and_back_at_the_head_in_input_order() {
    // Lean: ResidualArrow.tail, ResidualArrow.head; index 2i is `along i`, 2i + 1 is `back i`.
    // Arrow 0: 1 → 0, arrow 1: 0 → 1 (antiparallel), arrow 2: 0 → 1 (parallel), arrow 3: a loop
    // at 2, arrow 4: 2 → 0.
    let net = network(
        3,
        &[(1, 0, 1), (0, 1, 2), (0, 1, 3), (2, 2, 4), (2, 0, 5)],
        0,
        1,
    );
    let r = Residual::new(&net);
    assert_eq!(r.n(), 3);
    assert_eq!(r.arrow_count(), 10);
    assert_eq!(r.out(0), [1, 2, 4, 9]);
    assert_eq!(r.out(1), [0, 3, 5]);
    assert_eq!(r.out(2), [6, 7, 8]);
    for e in 0..10 {
        assert_eq!(r.tail(e), r.head(e ^ 1));
        assert!(r.out(r.tail(e)).contains(&e));
    }
    assert_eq!((r.head(4), r.tail(4)), (1, 0));
    assert_eq!((r.head(9), r.tail(9)), (2, 0));
    assert_eq!((r.source(), r.sink()), (0, 1));
    // The zero flow: every along arrow has its capacity, every back arrow nothing.
    assert_eq!(
        (0..10).map(|e| r.residual_capacity(e)).collect::<Vec<_>>(),
        [1, 0, 2, 0, 3, 0, 4, 0, 5, 0]
    );
    assert_eq!(r.flow(), [0; 5]);
}

#[test]
fn sending_moves_residual_capacity_to_the_partner_and_the_flow_is_the_residual_capacity_of_back() {
    // Lean: sendOne, ResidualArrow.residual capacity
    let net = network(3, &[(0, 1, 5), (1, 2, 3)], 0, 2);
    let mut r = Residual::new(&net);
    r.send(0, 3);
    r.send(2, 3);
    assert_eq!((r.residual_capacity(0), r.residual_capacity(1)), (2, 3));
    assert_eq!((r.residual_capacity(2), r.residual_capacity(3)), (0, 3));
    assert_eq!(r.flow(), [3, 3]);
    // Back against arrow 0 takes 1 off it.
    r.send(1, 1);
    assert_eq!(r.flow(), [2, 3]);
    assert_eq!(r.residual_capacity(0) + r.residual_capacity(1), 5);
}

#[test]
#[should_panic(expected = "sending 3 along arrow 1 with residual capacity 0")]
fn sending_more_than_the_residual_capacity_panics() {
    let net = network(2, &[(0, 1, 5)], 0, 1);
    Residual::new(&net).send(1, 3);
}

#[test]
fn the_reached_vertices_are_those_arrows_with_residual_capacity_lead_to() {
    // Lean: Flows.reached
    // 0 → 1 → 2 → 3, and 4 → 0 never reached; 1 → 2 full after sending 2 along 0 → 1 → 2.
    let net = network(5, &[(0, 1, 3), (1, 2, 2), (2, 3, 9), (4, 0, 1)], 0, 3);
    let mut r = Residual::new(&net);
    assert_eq!(r.reached(), [true, true, true, true, false]);
    r.send(0, 2);
    r.send(2, 2);
    assert_eq!(r.reached(), [true, true, false, false, false]);
    // Taking the 2 back, against 1 → 2 and then against 0 → 1, frees 1 → 2 again.
    r.send(3, 2);
    r.send(1, 2);
    assert_eq!(r.flow(), [0, 0, 0, 0]);
    assert_eq!(r.reached(), [true, true, true, true, false]);
}
