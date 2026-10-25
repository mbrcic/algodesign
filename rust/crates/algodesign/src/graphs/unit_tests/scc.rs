use super::*;
use crate::graphs::naive;
use proptest::prelude::*;

fn graph(n: usize, arrows: &[(u32, u32)]) -> Digraph {
    Digraph::new(n, arrows).unwrap()
}

fn groups(c: &Components) -> Vec<Vec<u32>> {
    (0..c.count()).map(|i| c.group(i).to_vec()).collect()
}

fn arrows_of(g: &Digraph) -> Vec<(u32, u32)> {
    (0..g.arrow_count()).map(|i| g.arrow(i)).collect()
}

/// Seven vertices: the cycle 0 → 1 → 2 → 0, the pair 3 ⇄ 4 (4 → 3 doubled), 1 → 5 with a loop at
/// 5, 5 → 3, 5 → 6 → 1.
const SEVEN: [(u32, u32); 12] = [
    (0, 1),
    (1, 2),
    (2, 0),
    (2, 3),
    (3, 4),
    (4, 3),
    (4, 3),
    (1, 5),
    (5, 5),
    (5, 3),
    (5, 6),
    (6, 1),
];

#[test]
fn algorithm_t_stops_when_done_and_emits_members_in_postorder() {
    // Lean: the `algorithmT seven` example in the Lean tests (Graphs.lean)
    // The walk enters 0, 1, 2; 2 → 0 drops 2's low; 2 → 3 enters 3, 4, whose group comes out
    // first; 2 finishes onto F; back at 1, 1 → 5 → 6 enters the last vertices, and 6 → 1 drops
    // 6's low to the root's: F holds 2, the path is 0, 1, 5, 6. Running on would finish 6, 5, 1
    // onto F and pop them under 0, so the group is 2, 6, 5, 1, 0.
    let g = graph(7, &SEVEN);
    let (c, time) = algorithm_t(&g, &mut ());
    assert_eq!(c.group_of_each(), &[0, 0, 0, 1, 1, 0, 0]);
    assert_eq!(groups(&c), vec![vec![2, 6, 5, 1, 0], vec![4, 3]]);
    assert_eq!(time, 14);
}

#[test]
fn kosaraju_sharir_numbers_in_the_order_found_members_as_entered() {
    // Lean: the `kosarajuSharir seven` example in the Lean tests (Graphs.lean)
    let c = kosaraju_sharir(&graph(7, &SEVEN));
    assert_eq!(c.group_of_each(), &[0, 0, 0, 1, 1, 0, 0]);
    assert_eq!(groups(&c), vec![vec![0, 2, 1, 6, 5], vec![3, 4]]);
}

#[test]
fn condensation_keeps_one_arrow_per_pair_and_no_loops() {
    // Lean: the `condensation seven` example in the Lean tests (Graphs.lean)
    let g = graph(7, &SEVEN);
    for c in [strong_components(&g), kosaraju_sharir(&g)] {
        let q = condensation(&g, &c);
        assert_eq!(q.n(), 2);
        assert_eq!(arrows_of(&q), vec![(0, 1)]);
    }
}

#[test]
fn a_pair_with_a_follower() {
    // Lean: the `algorithmT abc` and `kosarajuSharir abc` examples in the Lean tests (Graphs.lean)
    // A ↔ B → C: {A, B} first, then C.
    let g = graph(3, &[(0, 1), (1, 0), (1, 2)]);
    let c = strong_components(&g);
    assert_eq!(c.group_of_each(), &[0, 0, 1]);
    assert_eq!(groups(&c), vec![vec![1, 0], vec![2]]);
    assert_eq!(c.group_of(2), 1);
    let k = kosaraju_sharir(&g);
    assert_eq!(k.group_of_each(), &[0, 0, 1]);
    assert_eq!(groups(&k), vec![vec![0, 1], vec![2]]);
    assert_eq!(arrows_of(&condensation(&g, &c)), vec![(0, 1)]);
    assert_eq!(check_components(&g, c.group_of_each()), Ok(()));
}

#[test]
fn a_group_of_one_is_cyclic_exactly_when_it_has_a_loop() {
    // 0 → 1 with a loop at 1: two groups of one each; only 1's is a cycle.
    let arrows = [(0, 1), (1, 1)];
    let g = graph(2, &arrows);
    let c = strong_components(&g);
    assert_eq!(groups(&c), vec![vec![0], vec![1]]);
    assert!(!naive::has_cycle_within(&[true, false], &arrows));
    assert!(naive::has_cycle_within(&[false, true], &arrows));
    // The loop is dropped from the graph of groups.
    assert_eq!(arrows_of(&condensation(&g, &c)), vec![(0, 1)]);
    assert_eq!(check_components(&g, &[0, 1]), Ok(()));
}

#[test]
fn no_vertices_and_vertices_with_no_arrows() {
    let c = strong_components(&graph(0, &[]));
    assert_eq!(c.count(), 0);
    assert_eq!(kosaraju_sharir(&graph(0, &[])), c);
    assert_eq!(check_components(&graph(0, &[]), &[]), Ok(()));
    // Three lone vertices come out 0, 1, 2, so their ids run 2, 1, 0.
    let c = strong_components(&graph(3, &[]));
    assert_eq!(c.group_of_each(), &[2, 1, 0]);
    assert_eq!(kosaraju_sharir(&graph(3, &[])), c);
}

#[test]
fn the_checker_rejects_the_two_planted_wrong_groupings() {
    // Lean: the `check` examples (`quotientCycle`, `notStronglyConnected`) in the Lean tests
    // (Graphs.lean)
    // A → B → A split into two singletons: each is strongly connected on its own, but the graph
    // of groups has the cycle 0 → 1 → 0.
    let g = graph(2, &[(0, 1), (1, 0)]);
    assert_eq!(check_components(&g, &[0, 1]), Err(ComponentsError::Cyclic));
    assert_eq!(check_components(&g, &[0, 0]), Ok(()));
    // Joining two vertices that do not reach each other: 0 → 1 as one group.
    let g = graph(2, &[(0, 1)]);
    assert_eq!(
        check_components(&g, &[0, 0]),
        Err(ComponentsError::NotStronglyConnected { group: 0 })
    );
    assert_eq!(check_components(&g, &[0, 1]), Ok(()));
}

#[test]
fn the_checker_does_not_ask_for_topological_ids() {
    let g = graph(2, &[(0, 1)]);
    assert_eq!(check_components(&g, &[1, 0]), Ok(()));
}

#[test]
fn the_checker_refuses_what_is_not_a_partition() {
    let g = graph(3, &[(0, 1), (1, 0)]);
    let partition = Err(ComponentsError::Partition);
    assert_eq!(check_components(&g, &[0, 0]), partition);
    assert_eq!(check_components(&g, &[0, 0, 0, 0]), partition);
    // Id 2 used, id 1 not.
    assert_eq!(check_components(&g, &[0, 0, 2]), partition);
    // An id past n is refused before anything is sized by it.
    assert_eq!(check_components(&g, &[0, 0, u32::MAX]), partition);
    assert_eq!(check_components(&g, &[0, 0, 3]), partition);
    // The partition check comes before the others.
    assert_eq!(check_components(&g, &[0, 1, 3]), partition);
}

#[test]
fn the_backward_search_catches_what_the_forward_one_misses() {
    // 0 → 1, 0 → 2, 2 → 0 as one group: from 0 forward reaches 1 and 2, backward misses 1.
    let g = graph(3, &[(0, 1), (0, 2), (2, 0)]);
    assert_eq!(
        check_components(&g, &[0, 0, 0]),
        Err(ComponentsError::NotStronglyConnected { group: 0 })
    );
    // 1 → 0 instead: forward from 0 misses 1.
    let g = graph(3, &[(1, 0), (0, 2), (2, 0)]);
    assert_eq!(
        check_components(&g, &[0, 0, 0]),
        Err(ComponentsError::NotStronglyConnected { group: 0 })
    );
    // The first failing group in id order is reported.
    let g = graph(4, &[(0, 1), (2, 3)]);
    assert_eq!(
        check_components(&g, &[1, 1, 0, 0]),
        Err(ComponentsError::NotStronglyConnected { group: 0 })
    );
}

#[test]
fn the_packed_lows_stay_below_the_done_value() {
    // The largest live low is the clock at the end, 2n; the graph refuses n >= 2³¹, so at the
    // largest n it accepts, 2n is still below the done value.
    for n in [1usize, 2, 7, 100] {
        let arrows: Vec<(u32, u32)> = (0..n as u32).map(|v| (v, (v + 1) % n as u32)).collect();
        assert_eq!(algorithm_t(&graph(n, &arrows), &mut ()).1, 2 * n as u32);
        assert_eq!(algorithm_t(&graph(n, &[]), &mut ()).1, 2 * n as u32);
    }
    assert_eq!(algorithm_t(&graph(7, &SEVEN), &mut ()).1, 14);
    assert!(matches!(
        Digraph::new(1 << 31, &[]),
        Err(crate::graphs::GraphError::TooManyVertices { .. })
    ));
    let largest_n = (1u64 << 31) - 1;
    assert_eq!(2 * largest_n, u64::from(u32::MAX) - 1);
    assert!(2 * largest_n < u64::from(DONE));
}

/// A path through `n` vertices, `0 → 1 → … → n - 1`, closed back to 0 when `closed`.
fn long(n: u32, closed: bool) -> Vec<(u32, u32)> {
    let mut arrows: Vec<(u32, u32)> = (1..n).map(|v| (v - 1, v)).collect();
    if closed {
        arrows.push((n - 1, 0));
    }
    arrows
}

#[test]
fn a_path_and_a_cycle_of_a_million_vertices_run_on_a_small_stack() {
    // 256 KiB: any frame per vertex on the call stack would overflow it.
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let n = 1_000_000u32;
            let g = graph(n as usize, &long(n, false));
            let along: Vec<u32> = (0..n).collect();
            for c in [strong_components(&g), kosaraju_sharir(&g)] {
                assert_eq!(c.count(), n as usize);
                assert_eq!(c.group_of_each(), &along[..]);
            }
            assert_eq!(check_components(&g, &along), Ok(()));
            let g = graph(n as usize, &long(n, true));
            let c = strong_components(&g);
            assert_eq!(c.count(), 1);
            // Postorder: the walk stops at n - 1 → 0 with the whole path open, top down.
            let down: Vec<u32> = (0..n).rev().collect();
            assert_eq!(c.group(0), &down[..]);
            let k = kosaraju_sharir(&g);
            assert_eq!(k.group_of_each(), c.group_of_each());
            assert_eq!(check_components(&g, c.group_of_each()), Ok(()));
        })
        .expect("spawning a thread")
        .join()
        .expect("the body panicked");
}

/// A number of vertices and some arrows between them, loops and doubled arrows included.
fn graphs() -> impl Strategy<Value = (usize, Vec<(u32, u32)>)> {
    (1usize..=9).prop_flat_map(|n| {
        let m = n as u32;
        (Just(n), prop::collection::vec((0..m, 0..m), 0..24))
    })
}

/// Both methods give the strong components, ids topological; T's members are in postorder,
/// Kosaraju–Sharir's in the order entered; both ids agree vertex by vertex.
fn both_are_the_components(n: usize, arrows: &[(u32, u32)]) -> Result<(), TestCaseError> {
    let g = graph(n, arrows);
    let truth = naive::mutual_groups(n, arrows);
    let t = strong_components(&g);
    let k = kosaraju_sharir(&g);
    for c in [&t, &k] {
        prop_assert!(naive::same_partition(c.group_of_each(), &truth));
        prop_assert_eq!(check_components(&g, c.group_of_each()), Ok(()));
        // Ids topological: every arrow between groups goes from a smaller id to a larger.
        for &(a, b) in arrows {
            let (x, y) = (c.group_of(a as usize), c.group_of(b as usize));
            prop_assert!(x <= y);
        }
        // Members listed once each, in their own group.
        let mut seen = vec![false; n];
        for i in 0..c.count() {
            prop_assert!(!c.group(i).is_empty());
            for &v in c.group(i) {
                prop_assert_eq!(c.group_of(v as usize) as usize, i);
                prop_assert!(!std::mem::replace(&mut seen[v as usize], true));
            }
        }
        prop_assert!(seen.iter().all(|&s| s));
        // The condensation: no loops, no doubled arrows, exactly the pairs some arrow joins.
        let q = condensation(&g, c);
        let mut got = arrows_of(&q);
        prop_assert!(got.iter().all(|&(x, y)| x < y));
        got.sort_unstable();
        let mut want: Vec<(u32, u32)> = arrows
            .iter()
            .map(|&(a, b)| (c.group_of(a as usize), c.group_of(b as usize)))
            .filter(|&(x, y)| x != y)
            .collect();
        want.sort_unstable();
        want.dedup();
        prop_assert_eq!(got, want);
    }
    prop_assert_eq!(t.group_of_each(), k.group_of_each());
    // T's members in the order a plain walk finishes them.
    let mut finish = vec![0usize; n];
    for (i, &v) in naive::postorder(n, arrows).iter().enumerate() {
        finish[v as usize] = i;
    }
    for i in 0..t.count() {
        prop_assert!(t
            .group(i)
            .windows(2)
            .all(|p| finish[p[0] as usize] < finish[p[1] as usize]));
    }
    Ok(())
}

proptest! {
    #[test]
    fn on_any_graph_both_methods_give_the_components((n, arrows) in graphs()) {
        both_are_the_components(n, &arrows)?;
    }

    #[test]
    fn on_a_denser_graph_both_methods_give_the_components(
        (n, arrows) in (1usize..=6).prop_flat_map(|n| {
            let m = n as u32;
            (Just(n), prop::collection::vec((0..m, 0..m), 6..30))
        })
    ) {
        both_are_the_components(n, &arrows)?;
    }

    #[test]
    fn the_checker_rejects_every_wrong_grouping(
        (n, arrows) in graphs(),
        moves in prop::collection::vec((0u32..9, 0u32..9), 1..4),
    ) {
        let g = graph(n, &arrows);
        let truth = strong_components(&g);
        let mut group_of = truth.group_of_each().to_vec();
        for (v, c) in moves {
            group_of[v as usize % n] = c % (n as u32 + 1);
        }
        let ok = check_components(&g, &group_of).is_ok();
        // Any numbering of the true partition passes; anything else fails.
        let valid_ids = {
            let k = group_of.iter().max().map_or(0, |&c| c as usize + 1);
            let mut used = vec![false; k];
            group_of.iter().for_each(|&c| used[c as usize] = true);
            used.iter().all(|&u| u)
        };
        prop_assert_eq!(ok, valid_ids && naive::same_partition(&group_of, truth.group_of_each()));
    }
}

/// The chapter's chat, Omar 0, Amara 1, Priya 2, Mateo 3, Kenji 4, Sofia 5; an arrow
/// from the person waited on to the person waiting.
const CHAT: [(u32, u32); 6] = [(4, 5), (3, 1), (1, 3), (1, 0), (1, 2), (2, 3)];

#[test]
fn algorithm_t_stops_where_a_low_drops_to_the_root_with_everyone_entered() {
    // The stop is checked where a low drops, as the Python checks it, so both stop at the same
    // step, and that step's state is the walk's end. Without the stop the walk runs on and
    // records more states.
    // SEVEN: everyone is entered when 6 → 1 drops 6 to the root's number, and that step stops
    // with 2 on F and the path 0, 1, 5, 6 still open: 15 states, then the stop's.
    let g = graph(7, &SEVEN);
    let states = Walk::trace(&g);
    assert_eq!(states.len(), 16);
    let before = &states[14];
    assert_eq!(before.groups(), vec![&[4u32, 3][..]]);
    assert_eq!(before.stack[before.ftop..], [2, 7]);
    let last = states.last().unwrap();
    assert_eq!(last.groups(), vec![&[4u32, 3][..], &[2, 6, 5, 1, 0][..]]);
    assert_eq!(last.stack[last.ftop..], [7]);
    assert_eq!(last.finished, [4, 3, 2, 6, 5, 1, 0]);
    assert_eq!(last.retreats.last(), Some(&(6, 1)));
    // The chat: Omar alone, then Amara's walk enters Mateo and Priya; back at Amara with everyone
    // but Kenji and Sofia entered, so Amara finishes and leads; Kenji's walk enters Sofia, the
    // last, and comes back to Kenji, the root, which lowers nothing, so the walk does not stop:
    // Kenji finishes and comes out alone, the walk's end: 14 states, then Kenji's finish.
    let chat = graph(6, &CHAT);
    let states = Walk::trace(&chat);
    assert_eq!(states.len(), 15);
    let groups: Vec<Vec<u32>> = states[13].groups().iter().map(|m| m.to_vec()).collect();
    assert_eq!(groups, vec![vec![0], vec![3, 2, 1], vec![5]]);
    let c = strong_components(&chat);
    assert_eq!(c.group_of_each(), &[3, 2, 2, 2, 0, 1]);
}

#[test]
fn every_state_of_algorithm_t_is_valid() {
    // Lean: AlgorithmT.validAlong, AlgorithmT.traceValid
    let g = graph(7, &SEVEN);
    let states = Walk::trace(&g);
    assert!(!states.is_empty());
    for w in &states {
        assert_eq!(w.check_valid(&g), Ok(()));
    }
    // A ↔ B → C: enter 0, enter 1, back over 1 → 0 (1 drops to 0 before 2 is entered), enter 2,
    // 2 finishes and comes out and the walk comes back over 1 → 2, which lowers nothing, so the
    // walk does not stop: 1 finishes onto F, the walk comes back to 0, and 0 finishes.
    let pair = graph(3, &[(0, 1), (1, 0), (1, 2)]);
    let states = Walk::trace(&pair);
    assert_eq!(states.len(), 7);
    assert!(states.iter().all(|w| w.is_valid(&pair)));
}

/// A ↔ B → C and a fourth vertex D with no arrows, entered last, so the walk from A runs to its
/// end.
fn pair_and_one() -> Digraph {
    graph(4, &[(0, 1), (1, 0), (1, 2)])
}

/// A state of the walk on [`pair_and_one`], one part changed.
fn changed(at: usize, f: impl FnOnce(&mut WalkParts)) -> Walk {
    let mut parts = Walk::trace(&pair_and_one())[at].parts();
    f(&mut parts);
    Walk::from_parts(parts)
}

#[test]
fn each_broken_walk_state_names_its_piece() {
    let g = pair_and_one();
    // Enter 0, enter 1, back over 1 → 0, enter 2, 2 comes out, back over 1 → 2, then 1 finishes
    // onto F and the walk comes back to 0: F holds 1.
    assert_eq!(Walk::trace(&g).len(), 9);
    assert_eq!(changed(5, |_| {}).check_valid(&g), Ok(()));
    let off_f = changed(5, |p| p.ftop += 1);
    assert_eq!(
        off_f.check_valid(&g),
        Err("invariant 1 (followers_in_finish_order)")
    );
    // 1's low back up to its own entry clock, though it came back over 1 → 0.
    let high = changed(5, |p| p.low[1] = p.pre[1]);
    assert_eq!(
        high.check_valid(&g),
        Err("invariant 2 (climb_back_is_earliest)")
    );
    // The retreat over 1 → 0 forgotten: 1 could climb back to nothing earlier.
    let forgot = changed(5, |p| {
        p.retreats.remove(0);
    });
    assert_eq!(
        forgot.check_valid(&g),
        Err("invariant 2 (climb_back_is_earliest)")
    );
    // 2's group is out, but 2 is not marked out.
    let done = changed(5, |p| p.low[2] = p.pre[2]);
    assert_eq!(
        done.check_valid(&g),
        Err("invariant 3 (done_iff_group_out)")
    );
}

proptest! {
    #[test]
    fn on_any_graph_every_state_of_algorithm_t_is_valid((n, arrows) in graphs()) {
        let g = graph(n, &arrows);
        for w in Walk::trace(&g) {
            prop_assert_eq!(w.check_valid(&g), Ok(()));
        }
    }
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "another graph's")]
fn the_condensation_refuses_another_graphs_groups() {
    // 0 → 1 and 1 → 0 alone have the same vertices; the second's ids put 1 before 0, so the
    // first's arrow runs from a larger id to a smaller.
    let g = graph(2, &[(0, 1)]);
    let other = strong_components(&graph(2, &[(1, 0)]));
    let _ = condensation(&g, &other);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "the groups cover 2 vertices, the graph has 3")]
fn the_condensation_refuses_groups_of_another_size() {
    let other = strong_components(&graph(2, &[(0, 1)]));
    let _ = condensation(&graph(3, &[]), &other);
}

#[test]
fn a_vertex_or_group_out_of_range_panics_with_the_range() {
    let c = strong_components(&graph(7, &SEVEN));
    let v = std::panic::catch_unwind(|| c.group_of(7)).unwrap_err();
    assert_eq!(
        v.downcast_ref::<String>().unwrap(),
        "vertex 7 out of range 0..7"
    );
    let i = std::panic::catch_unwind(|| c.group(2).len()).unwrap_err();
    assert_eq!(
        i.downcast_ref::<String>().unwrap(),
        "group 2 out of range 0..2"
    );
}

/// The member lists and the ids say the same grouping: group `i` lists exactly the vertices whose
/// id is `i`, each once.
fn groups_agree_with_ids(c: &Components) -> bool {
    let mut seen = vec![false; c.group_of_each().len()];
    (0..c.count()).all(|i| {
        c.group(i).iter().all(|&v| {
            c.group_of(v as usize) as usize == i && !std::mem::replace(&mut seen[v as usize], true)
        })
    }) && seen.iter().all(|&s| s)
}

#[test]
fn the_groups_agree_with_the_ids_on_the_named_graphs() {
    for g in [graph(7, &SEVEN), graph(6, &CHAT), graph(0, &[])] {
        assert!(groups_agree_with_ids(&strong_components(&g)));
        assert!(groups_agree_with_ids(&kosaraju_sharir(&g)));
    }
}

proptest! {
    #[test]
    fn on_any_graph_the_groups_agree_with_the_ids((n, arrows) in graphs()) {
        let g = graph(n, &arrows);
        prop_assert!(groups_agree_with_ids(&strong_components(&g)));
        prop_assert!(groups_agree_with_ids(&kosaraju_sharir(&g)));
    }
}
