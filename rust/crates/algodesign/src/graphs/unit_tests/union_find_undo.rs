use super::*;
use crate::graphs::naive;
use proptest::prelude::*;

/// The most links any item is from its root.
fn depth(u: &UndoUnionFind) -> usize {
    (0..u.parent.len())
        .map(|mut i| {
            let mut d = 0;
            while u.parent[i] as usize != i {
                i = u.parent[i] as usize;
                d += 1;
            }
            d
        })
        .max()
        .unwrap_or(0)
}

/// The stored state a rollback must restore exactly.
fn state(u: &UndoUnionFind) -> (Vec<u32>, Vec<u8>, usize) {
    (u.parent.clone(), u.rank.clone(), u.count())
}

#[test]
fn every_item_starts_alone_with_an_empty_log() {
    let mut u = UndoUnionFind::new(4);
    assert_eq!(state(&u), (vec![0, 1, 2, 3], vec![0; 4], 4));
    assert!(!u.undo());
    assert_eq!(state(&u), (vec![0, 1, 2, 3], vec![0; 4], 4));
}

#[test]
fn on_equal_ranks_the_second_root_goes_under_the_first() {
    let mut u = UndoUnionFind::new(4);
    assert!(u.union(0, 1));
    assert_eq!(state(&u), (vec![0, 0, 2, 3], vec![1, 0, 0, 0], 3));
    assert!(u.union(3, 2));
    assert_eq!(state(&u), (vec![0, 0, 3, 3], vec![1, 0, 0, 1], 2));
    // Roots 0 and 3, both of rank 1: 3 goes under 0, whose rank rises.
    assert!(u.union(1, 2));
    assert_eq!(state(&u), (vec![0, 0, 3, 0], vec![2, 0, 0, 1], 1));
    assert_eq!(
        u.log,
        vec![Some((1, true)), Some((2, true)), Some((3, true))]
    );
}

#[test]
fn the_lower_rank_goes_under_the_higher_whichever_comes_first() {
    let mut u = UndoUnionFind::new(3);
    u.union(1, 2);
    assert!(u.union(0, 2));
    assert_eq!(state(&u), (vec![1, 1, 1], vec![0, 1, 0], 1));
    assert_eq!(u.log[1], Some((0, false)));
    assert!(u.undo());
    assert_eq!(state(&u), (vec![0, 1, 1], vec![0, 1, 0], 2));
}

#[test]
fn a_union_that_merges_nothing_takes_one_undo_step() {
    let mut u = UndoUnionFind::new(3);
    u.union(0, 1);
    let merged = state(&u);
    assert!(!u.union(1, 0));
    assert!(!u.union(2, 2));
    assert_eq!(state(&u), merged);
    assert_eq!(u.log, vec![Some((1, true)), None, None]);
    // The two empty entries go first, changing nothing; then the merge.
    assert!(u.undo());
    assert_eq!(state(&u), merged);
    assert!(u.undo());
    assert_eq!(state(&u), merged);
    assert!(u.joined(0, 1));
    assert!(u.undo());
    assert_eq!(state(&u), (vec![0, 1, 2], vec![0; 3], 3));
    assert!(!u.joined(0, 1));
    assert!(!u.undo());
}

#[test]
fn find_changes_nothing_and_stays_within_log2_n() {
    // Pairing items at distances 1, 2, 4, … builds a tree of 1024 items of depth exactly
    // 10 = log₂ 1024.
    let n = 1024;
    let mut u = UndoUnionFind::new(n);
    let mut step = 1;
    while step < n {
        for i in (0..n).step_by(2 * step) {
            assert!(u.union(i, i + step));
        }
        step *= 2;
    }
    assert_eq!(u.count(), 1);
    assert_eq!(depth(&u), 10);
    let before = state(&u);
    assert!((0..n).all(|x| u.find(x) == 0));
    assert_eq!(state(&u), before);
}

#[test]
#[should_panic(expected = "out of range")]
fn an_item_out_of_range_panics() {
    let u = UndoUnionFind::new(2);
    let _ = u.find(2);
}

/// One operation: a union of two items, or an undo.
#[derive(Debug, Clone)]
enum Op {
    Union(usize, usize),
    Undo,
}

fn ops() -> impl Strategy<Value = (usize, Vec<Op>)> {
    (1usize..=12).prop_flat_map(|n| {
        let op = prop_oneof![
            3 => (0..n, 0..n).prop_map(|(x, y)| Op::Union(x, y)),
            1 => Just(Op::Undo),
        ];
        (Just(n), prop::collection::vec(op, 0..40))
    })
}

proptest! {
    #[test]
    fn a_full_rollback_restores_every_earlier_state_exactly(
        n in 1usize..=12,
        pairs in prop::collection::vec((0usize..12, 0usize..12), 0..30),
    ) {
        let mut u = UndoUnionFind::new(n);
        let mut states = vec![state(&u)];
        for &(x, y) in &pairs {
            u.union(x % n, y % n);
            states.push(state(&u));
            prop_assert!(1usize << depth(&u) <= n);
        }
        while let Some(want) = states.pop() {
            prop_assert_eq!(state(&u), want);
            prop_assert_eq!(u.undo(), !states.is_empty());
        }
        prop_assert!(u.log.is_empty());
    }

    #[test]
    fn after_any_unions_and_undos_the_state_is_the_live_unions_replayed(
        (n, ops) in ops()
    ) {
        let mut u = UndoUnionFind::new(n);
        let mut live: Vec<(usize, usize)> = Vec::new();
        for op in ops {
            match op {
                Op::Union(x, y) => {
                    let before = naive::groups(n, &live);
                    prop_assert_eq!(u.union(x, y), before[x] != before[y]);
                    live.push((x, y));
                }
                Op::Undo => prop_assert_eq!(u.undo(), live.pop().is_some()),
            }
            let mut replay = UndoUnionFind::new(n);
            for &(x, y) in &live {
                replay.union(x, y);
            }
            prop_assert_eq!(&u, &replay);
            let groups = naive::groups(n, &live);
            prop_assert_eq!(u.count(), (0..n).filter(|&i| groups[i] == i).count());
            for x in 0..n {
                for y in 0..n {
                    prop_assert_eq!(u.joined(x, y), groups[x] == groups[y]);
                }
            }
            prop_assert!(1usize << depth(&u) <= n);
        }
    }
}
