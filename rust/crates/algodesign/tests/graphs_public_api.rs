// SPDX-License-Identifier: Apache-2.0
//! The Graphs module driven from outside the crate, through its public API only, as a reader's
//! program would use it.

use std::error::Error;

use algodesign::graphs::{
    blocks, check_components, condensation, dfs_order, kosaraju_sharir, strong_components,
    topological_order, two_sat, BlockCutForest, Digraph, Graph, GraphError, TwoSatError,
    UndoUnionFind, UnionFind,
};

/// The chapter's chat, Omar 0, Amara 1, Priya 2, Mateo 3, Kenji 4, Sofia 5; an arrow
/// from the person waited on to the person waiting.
fn chat() -> Digraph {
    Digraph::new(6, &[(4, 5), (3, 1), (1, 3), (1, 0), (1, 2), (2, 3)]).unwrap()
}

#[test]
fn the_chat_has_no_order_and_its_knot_is_one_group() {
    let g = chat();
    let stuck = topological_order(&g).unwrap_err();
    assert_eq!(stuck.vertices, [0, 1, 2, 3]);
    let cycle = dfs_order(&g).unwrap_err();
    assert_eq!(cycle.vertices.first(), cycle.vertices.last());

    let t = strong_components(&g);
    let ks = kosaraju_sharir(&g);
    assert_eq!(t.group_of_each(), ks.group_of_each());
    assert_eq!(t.group_of_each(), [3, 2, 2, 2, 0, 1]);
    assert_eq!(t.group(2), [3, 2, 1]);
    assert_eq!(check_components(&g, t.group_of_each()), Ok(()));

    // The graph of groups has an order: Kenji and the knot first, then Sofia and Omar.
    let q = condensation(&g, &t);
    assert_eq!(topological_order(&q).unwrap(), [0, 2, 1, 3]);
}

#[test]
fn the_errors_travel_through_question_marks() {
    fn order(g: &Digraph) -> Result<Vec<u32>, Box<dyn Error>> {
        Ok(topological_order(g)?)
    }
    fn cycle(g: &Digraph) -> Result<Vec<u32>, Box<dyn Error>> {
        Ok(dfs_order(g)?)
    }
    fn build(n: usize, arrows: &[(u32, u32)]) -> Result<Digraph, Box<dyn Error>> {
        Ok(Digraph::new(n, arrows)?)
    }
    let g = chat();
    assert!(order(&g).unwrap_err().to_string().contains("wait forever"));
    assert!(cycle(&g).unwrap_err().to_string().contains("cycle"));
    assert!(build(2, &[(0, 2)]).is_err());
    assert!(matches!(
        Digraph::new(2, &[(0, 2)]),
        Err(GraphError::EndpointOutOfRange { .. })
    ));
}

#[test]
fn two_triangles_and_a_tail_have_two_cut_vertices_and_one_bridge() {
    // Two triangles meeting at 2, and a tail 4 – 5.
    let links = [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 2), (4, 5)];
    let g = Graph::new(6, &links).unwrap();
    let b = blocks(&g);
    assert_eq!(b.bridges(), [6]);
    assert_eq!(b.cut_vertices(), [2, 4]);
    assert_eq!(b.count(), 3);
    let f = BlockCutForest::new(&g, &b);
    assert_eq!(f.separators(0, 5), Some(vec![2, 4]));
    assert_eq!(f.separators(0, 1), Some(vec![]));
}

#[test]
fn union_find_and_its_undo_agree_on_a_run() {
    let mut u = UnionFind::new(5);
    let mut w = UndoUnionFind::new(5);
    for (x, y) in [(0, 1), (2, 3), (1, 3), (4, 4)] {
        assert_eq!(u.union(x, y), w.union(x, y));
    }
    for x in 0..5 {
        for y in 0..5 {
            assert_eq!(u.joined(x, y), w.joined(x, y));
        }
    }
    assert_eq!((u.count(), w.count()), (2, 2));
    // Back over the self-merge (nothing) and the merge of the two pairs.
    assert!(w.undo());
    assert!(w.undo());
    assert!(!w.joined(0, 3));
    assert_eq!(w.count(), 3);
}

#[test]
fn two_sat_reads_literals_two_per_variable() {
    // x0 → x1 and x1 → not x0, with (x0 or x0): x0 is forced, then x1, then not x0.
    let clauses = [(1, 2), (3, 1), (0, 0)];
    assert_eq!(two_sat(2, &clauses), Err(TwoSatError::Unsat { var: 0 }));
    let a = two_sat(2, &[(1, 2), (0, 0)]).unwrap();
    assert_eq!(a, [true, true]);
}
