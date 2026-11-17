use super::*;

#[test]
fn a_network_takes_one_capacity_per_arrow_a_source_and_a_sink() {
    let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 1)]).unwrap();
    let net: Network = Network::new(g.clone(), vec![4, 2, 7], 0, 2).unwrap();
    assert_eq!(net.capacity(), [4, 2, 7]);
    assert_eq!(net.arrow_capacity(1), 2);
    assert_eq!((net.n(), net.arrow_count()), (3, 3));
    assert_eq!((net.source(), net.sink()), (0, 2));
    assert_eq!(net.graph(), &g);
    assert_eq!(net.clone().into_parts(), (g, vec![4, 2, 7], 0, 2));
}

#[test]
fn too_few_or_too_many_capacities_are_refused() {
    let g = Digraph::new(2, &[(0, 1), (1, 0)]).unwrap();
    for capacity in [vec![], vec![1u64], vec![1, 2, 3]] {
        let k = capacity.len();
        assert_eq!(
            Network::new(g.clone(), capacity, 0, 1),
            Err(FlowsError::CapacityCountMismatch {
                capacities: k,
                arrows: 2
            })
        );
    }
}

#[test]
fn a_source_or_a_sink_outside_the_graph_is_refused_and_so_is_one_vertex_for_both() {
    // Lean: Network.WellFormed (source < n, sink < n, source ≠ sink)
    let g = Digraph::new(2, &[(0, 1)]).unwrap();
    assert_eq!(
        Network::new(g.clone(), vec![1u64], 2, 1),
        Err(FlowsError::EndOutOfRange { vertex: 2, n: 2 })
    );
    assert_eq!(
        Network::new(g.clone(), vec![1u64], 0, 5),
        Err(FlowsError::EndOutOfRange { vertex: 5, n: 2 })
    );
    assert_eq!(
        Network::new(g, vec![1u64], 1, 1),
        Err(FlowsError::SourceIsSink { vertex: 1 })
    );
}

#[test]
fn the_capacities_leaving_the_source_must_add_up_within_a_u64() {
    let g = Digraph::new(3, &[(0, 1), (0, 2), (1, 2)]).unwrap();
    assert_eq!(
        Network::new(g.clone(), vec![u64::MAX, 1, 1], 0, 2),
        Err(FlowsError::SourceCapacityTooLarge)
    );
    assert!(Network::new(g, vec![u64::MAX - 1, 1, u64::MAX], 0, 2).is_ok());
    // A loop at the source carries nothing, so it does not count.
    let g = Digraph::new(2, &[(0, 0), (0, 1)]).unwrap();
    assert!(Network::new(g, vec![u64::MAX, u64::MAX], 0, 1).is_ok());
    // u32 capacities always fit.
    let g = Digraph::new(2, &[(0, 1), (0, 1)]).unwrap();
    assert!(Network::new(g, vec![u32::MAX, u32::MAX], 0, 1).is_ok());
}

#[test]
fn the_largest_power_of_two_below_and_the_half_of_each_capacity_type() {
    assert_eq!(0u32.power_of_two_below(), 0);
    assert_eq!(1u32.power_of_two_below(), 1);
    assert_eq!(12u32.power_of_two_below(), 8);
    assert_eq!(u32::MAX.power_of_two_below(), 1 << 31);
    assert_eq!(0u64.power_of_two_below(), 0);
    assert_eq!(16u64.power_of_two_below(), 16);
    assert_eq!(u64::MAX.power_of_two_below(), 1 << 63);
    assert_eq!((7u32.half(), 1u64.half()), (3, 0));
    assert_eq!((u32::MAX.to_u64(), 5u64.to_u64()), (4_294_967_295, 5));
}

#[test]
fn each_refusal_says_what_was_wrong() {
    let cases = [
        (
            FlowsError::CapacityCountMismatch {
                capacities: 1,
                arrows: 2,
            },
            "1 capacities for 2 arrows: one capacity per arrow",
        ),
        (
            FlowsError::TooManyArrows { count: 1 << 31 },
            "2147483648 arrows: at most 2^31 - 1 allowed",
        ),
        (
            FlowsError::EndOutOfRange { vertex: 4, n: 3 },
            "source or sink 4 out of range 0..3",
        ),
        (
            FlowsError::SourceIsSink { vertex: 0 },
            "vertex 0 is both the source and the sink",
        ),
        (
            FlowsError::SourceCapacityTooLarge,
            "the capacities leaving the source add up to more than u64::MAX",
        ),
    ];
    for (err, text) in cases {
        assert_eq!(err.to_string(), text);
    }
}
