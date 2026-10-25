use super::*;
use proptest::prelude::*;

fn pairs(r: Row<'_>) -> Vec<(u32, u32)> {
    r.iter().collect()
}

/// Lean's `Digraph.out`: for each neighbour `w` upward, the ids of the arrows `v → w` upward.
fn lean_out(n: usize, arrows: &[(u32, u32)], v: u32) -> Vec<(u32, u32)> {
    (0..n as u32)
        .flat_map(|w| {
            (0..arrows.len() as u32)
                .filter(move |&i| arrows[i as usize] == (v, w))
                .map(move |i| (w, i))
        })
        .collect()
}

/// Lean's `Graph.adj`: for each neighbour `w` upward, one entry per end of a link at `v` whose
/// other end is `w`, ids upward; a loop gives two.
fn lean_adj(n: usize, links: &[(u32, u32)], v: u32) -> Vec<(u32, u32)> {
    let mut row = Vec::new();
    for w in 0..n as u32 {
        for (i, &(a, b)) in (0u32..).zip(links) {
            if (a, b) == (v, w) {
                row.push((w, i));
            }
            if (b, a) == (v, w) {
                row.push((w, i));
            }
        }
    }
    row
}

#[test]
fn rows_are_sorted_by_neighbour_then_id_whatever_the_input_order() {
    // Lean: the `Digraph.out` and `Digraph.into` examples in Digraph.lean
    let g = &Digraph::new(3, &[(0, 2), (0, 1), (0, 2), (1, 0)]).unwrap();
    assert_eq!(pairs(g.out(0)), vec![(1, 1), (2, 0), (2, 2)]);
    assert_eq!(pairs(g.incoming(2)), vec![(0, 0), (0, 2)]);
    assert_eq!(pairs(g.incoming(0)), vec![(1, 3)]);
    assert!(g.out(2).is_empty());
    assert_eq!(g.out(0).len(), 3);
    assert_eq!(g.out(0).neighbours, &[1, 2, 2]);
    assert_eq!(g.out(0).ids, &[1, 0, 2]);
    assert_eq!((g.n(), g.arrow_count(), g.arrow(1)), (3, 4, (0, 1)));
}

#[test]
fn doubled_arrows_and_loops_are_kept_with_their_own_ids() {
    let g = &Digraph::new(2, &[(1, 1), (0, 1), (0, 1), (1, 1)]).unwrap();
    assert_eq!(pairs(g.out(0)), vec![(1, 1), (1, 2)]);
    assert_eq!(pairs(g.out(1)), vec![(1, 0), (1, 3)]);
    assert_eq!(pairs(g.incoming(1)), vec![(0, 1), (0, 2), (1, 0), (1, 3)]);
    assert!(g.incoming(0).is_empty());
}

#[test]
fn a_link_is_in_both_rows_and_a_loop_twice_in_its_own() {
    // Lean: the `Graph.adj` examples in Digraph.lean
    let g = Graph::new(2, &[(0, 1), (1, 1)]).unwrap();
    assert_eq!(pairs(g.adj(1)), vec![(0, 0), (1, 1), (1, 1)]);
    assert_eq!(pairs(g.adj(0)), vec![(1, 0)]);
    assert_eq!((g.n(), g.link_count(), g.link(1)), (2, 2, (1, 1)));
}

#[test]
fn doubled_links_keep_their_own_ids() {
    let g = Graph::new(3, &[(2, 0), (0, 2), (1, 0)]).unwrap();
    assert_eq!(pairs(g.adj(0)), vec![(1, 2), (2, 0), (2, 1)]);
    assert_eq!(pairs(g.adj(2)), vec![(0, 0), (0, 1)]);
    assert_eq!(pairs(g.adj(1)), vec![(0, 2)]);
}

#[test]
fn no_vertices_and_no_arrows() {
    let g = Digraph::new(0, &[]).unwrap();
    assert_eq!((g.n(), g.arrow_count()), (0, 0));
    let g = &Digraph::new(2, &[]).unwrap();
    assert!(g.out(1).is_empty() && g.incoming(1).is_empty());
    assert_eq!(Graph::new(0, &[]).unwrap().n(), 0);
}

#[test]
fn an_end_out_of_range_is_refused_naming_the_first() {
    let e = Digraph::new(3, &[(0, 1), (1, 3), (5, 0)]).unwrap_err();
    assert_eq!(
        e,
        GraphError::EndpointOutOfRange {
            id: 1,
            vertex: 3,
            n: 3
        }
    );
    assert_eq!(e.to_string(), "entry 1 names vertex 3, out of range 0..3");
    let e = Graph::new(2, &[(2, 0)]).unwrap_err();
    assert_eq!(
        e,
        GraphError::EndpointOutOfRange {
            id: 0,
            vertex: 2,
            n: 2
        }
    );
    assert!(Digraph::new(0, &[(0, 0)]).is_err());
}

#[test]
fn two_to_the_31_vertices_are_refused_before_anything_is_allocated() {
    let n = 1usize << 31;
    assert_eq!(
        Digraph::new(n, &[]).unwrap_err(),
        GraphError::TooManyVertices { n }
    );
    assert_eq!(
        Graph::new(n, &[]).unwrap_err(),
        GraphError::TooManyVertices { n }
    );
    assert_eq!(
        GraphError::TooManyVertices { n }.to_string(),
        "2147483648 vertices: at most 2^31 - 1 allowed"
    );
}

#[test]
fn more_ids_than_a_u32_holds_are_refused() {
    // The size check on its own: building u32::MAX + 1 arrows is out of reach for a test.
    let count = u32::MAX as usize + 1;
    let too_many = GraphError::TooManyArrows { count };
    assert_eq!(check(3, count, too_many.clone(), &[]), Err(too_many));
    let fits = GraphError::TooManyLinks { count: 0 };
    assert_eq!(check(3, u32::MAX as usize, fits, &[]), Ok(()));
    assert_eq!(
        GraphError::TooManyLinks { count }.to_string(),
        "4294967296 links: at most u32::MAX allowed"
    );
    let as_error: &dyn std::error::Error = &GraphError::TooManyArrows { count };
    assert!(as_error.source().is_none());
}

#[test]
#[should_panic(expected = "out of range")]
fn out_of_a_vertex_out_of_range_panics() {
    let _ = Digraph::new(2, &[]).unwrap().out(2);
}

#[test]
#[should_panic(expected = "out of range")]
fn incoming_of_a_vertex_out_of_range_panics() {
    let _ = Digraph::new(2, &[]).unwrap().incoming(2);
}

#[test]
#[should_panic(expected = "out of range")]
fn adj_of_a_vertex_out_of_range_panics() {
    let _ = Graph::new(2, &[]).unwrap().adj(2);
}

#[test]
#[should_panic(expected = "out of range")]
fn an_arrow_id_out_of_range_panics() {
    let _ = Digraph::new(2, &[(0, 1)]).unwrap().arrow(1);
}

/// A number of vertices and some arrows (or links) between them.
fn graphs() -> impl Strategy<Value = (usize, Vec<(u32, u32)>)> {
    (1usize..=8).prop_flat_map(|n| {
        let m = n as u32;
        (Just(n), prop::collection::vec((0..m, 0..m), 0..24))
    })
}

proptest! {
    #[test]
    fn every_row_is_the_lean_row((n, arrows) in graphs()) {
        // Lean: Digraph.out, Digraph.into, Graph.adj
        let g = &Digraph::new(n, &arrows).unwrap();
        let turned: Vec<(u32, u32)> = arrows.iter().map(|&(a, b)| (b, a)).collect();
        let u = Graph::new(n, &arrows).unwrap();
        for v in 0..n {
            prop_assert_eq!(pairs(g.out(v)), lean_out(n, &arrows, v as u32));
            prop_assert_eq!(pairs(g.incoming(v)), lean_out(n, &turned, v as u32));
            prop_assert_eq!(pairs(u.adj(v)), lean_adj(n, &arrows, v as u32));
        }
        prop_assert_eq!(g.arrow_count(), arrows.len());
        prop_assert_eq!(u.link_count(), arrows.len());
        for (i, &a) in arrows.iter().enumerate() {
            prop_assert_eq!(g.arrow(i), a);
            prop_assert_eq!(u.link(i), a);
        }
    }
}

#[test]
#[should_panic(expected = "out of range")]
fn a_link_id_out_of_range_panics() {
    let _ = Graph::new(2, &[(0, 1)]).unwrap().link(1);
}
