use super::*;
use crate::graphs::naive;
use proptest::prelude::*;

/// The most links any item is from its root, counted without compressing anything.
fn depth(u: &UnionFind) -> usize {
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

fn unions(n: usize, pairs: &[(usize, usize)]) -> UnionFind {
    let mut u = UnionFind::new(n);
    for &(x, y) in pairs {
        u.union(x, y);
    }
    u
}

#[test]
fn every_item_starts_alone() {
    // Lean: valid_init
    let u = UnionFind::new(5);
    assert_eq!(u.parent, vec![0, 1, 2, 3, 4]);
    assert_eq!(u.rank, vec![0; 5]);
    assert_eq!(u.count(), 5);
    assert!(u.is_valid());
    assert!(UnionFind::new(0).is_valid());
}

#[test]
fn union_of_two_singles_keeps_the_first_as_root() {
    // Lean: the `(init 2).union 0 1` example in Union.lean
    let mut u = UnionFind::new(2);
    assert!(u.union(0, 1));
    assert_eq!(u.parent[1], 0);
    assert_eq!(u.rank[0], 1);
    assert_eq!(u.count(), 1);
    assert!(u.is_valid());
}

#[test]
fn union_inside_one_group_keeps_ranks_and_count() {
    // Lean: the "merging two items already together" example in Union.lean
    let mut u = unions(2, &[(0, 1)]);
    assert!(!u.union(1, 0));
    assert_eq!(u.rank, vec![1, 0]);
    assert_eq!(u.count(), 1);
    assert!(u.is_valid());
}

/// The 21-item run behind the same-root check: before each item joins the chain, it is merged
/// with itself once more than the last.
fn self_unions_then_chain(n: usize) -> Vec<(usize, usize)> {
    let mut ops = Vec::new();
    for i in 0..n - 1 {
        ops.extend(std::iter::repeat_n((i + 1, i + 1), i + 1));
        ops.push((i, i + 1));
    }
    ops
}

#[test]
fn repeated_unions_inside_one_group_keep_ranks_and_depth_bounded() {
    let n = 21;
    // CLRS's FIND-SET and LINK, with the tie as here but no check for one root: a self-union
    // raises the root's rank with no new item, so each new item outranks the chain and goes on top.
    let mut parent: Vec<usize> = (0..n).collect();
    let mut rank = vec![0usize; n];
    fn find_set(p: &mut [usize], x: usize) -> usize {
        if p[x] != x {
            p[x] = find_set(p, p[x]);
        }
        p[x]
    }
    for &(x, y) in &self_unions_then_chain(n) {
        let (rx, ry) = (find_set(&mut parent, x), find_set(&mut parent, y));
        if rank[rx] < rank[ry] {
            parent[rx] = ry;
        } else {
            parent[ry] = rx;
            if rank[rx] == rank[ry] {
                rank[rx] += 1;
            }
        }
    }
    let unguarded = UnionFind {
        parent: parent.iter().map(|&p| p as u32).collect(),
        rank: vec![0; n],
        count: 1,
    };
    assert_eq!(depth(&unguarded), 20);

    // With the check, every self-union answers no and changes nothing.
    let mut u = UnionFind::new(n);
    for &(x, y) in &self_unions_then_chain(n) {
        let ranks = u.rank.clone();
        let merged = u.union(x, y);
        assert_eq!(merged, x != y);
        if x == y {
            assert_eq!(u.rank, ranks);
        }
    }
    assert_eq!(u.count(), 1);
    assert!(u.is_valid());
    assert!(u.rank.iter().all(|&r| r <= 4)); // log₂ 21 < 5
    assert!(depth(&u) <= 4);

    // Repeating unions of pairs already joined keeps ranks and the count.
    let ranks = u.rank.clone();
    for _ in 0..3 {
        for i in 0..n - 1 {
            assert!(!u.union(i, i + 1));
            assert!(!u.union(i + 1, i));
        }
    }
    assert_eq!(u.rank, ranks);
    assert_eq!(u.count(), 1);
    assert!(u.is_valid());
    assert!(depth(&u) <= 4);
}

#[test]
fn equal_ranks_raise_the_first_root() {
    // Lean: the `(init 4).unions [(0, 1), (2, 3), (1, 3)]` example in Union.lean
    let mut u = unions(4, &[(0, 1), (2, 3), (1, 3)]);
    assert!(u.is_valid());
    assert_eq!(u.parent, vec![0, 0, 0, 2]);
    assert_eq!(u.rank, vec![2, 0, 1, 0]);
    assert_eq!(u.count(), 1);
    assert!(u.joined(1, 2));
}

#[test]
fn five_item_run_ends_flat() {
    // Lean: the `(init 5).unions [(0, 1), (2, 3), (1, 3), (4, 4), (3, 4), (0, 4)]` example in
    // Union.lean
    let u = unions(5, &[(0, 1), (2, 3), (1, 3), (4, 4), (3, 4), (0, 4)]);
    assert!(u.is_valid());
    assert_eq!(u.parent, vec![0, 0, 0, 0, 0]);
    assert_eq!(u.rank, vec![2, 0, 1, 0, 0]);
    assert_eq!(u.count(), 1);
}

#[test]
fn a_long_chain_stays_within_log_n_only_with_the_rank_rule() {
    let n = 1024;
    // Without ranks or compression, hanging x's root under y's along (0, 1), (1, 2), ... makes
    // one path through every item.
    let mut parent: Vec<usize> = (0..n).collect();
    let top = |p: &[usize], mut i: usize| {
        while p[i] != i {
            i = p[i];
        }
        i
    };
    for i in 0..n - 1 {
        let (rx, ry) = (top(&parent, i), top(&parent, i + 1));
        parent[rx] = ry;
    }
    let plain_depth = (0..n)
        .map(|mut i| {
            let mut d = 0;
            while parent[i] != i {
                i = parent[i];
                d += 1;
            }
            d
        })
        .max()
        .unwrap();
    assert_eq!(plain_depth, n - 1);

    // With ranks, the same chain stays shallow ...
    let chain: Vec<(usize, usize)> = (0..n - 1).map(|i| (i, i + 1)).collect();
    let u = unions(n, &chain);
    assert!(u.is_valid());
    assert!(depth(&u) <= 10); // log₂ 1024

    // ... and merging equal halves, stride by stride, reaches the largest rank the bound allows.
    let mut halves = Vec::new();
    let mut step = 1;
    while step < n {
        halves.extend((0..n).step_by(2 * step).map(|i| (i, i + step)));
        step *= 2;
    }
    let u = unions(n, &halves);
    assert!(u.is_valid());
    assert_eq!(u.rank[0], 10);
    assert!(depth(&u) <= 10);
}

#[test]
#[should_panic(expected = "out of range")]
fn find_out_of_range_panics() {
    UnionFind::new(3).find(3);
}

#[test]
#[should_panic(expected = "out of range")]
fn union_out_of_range_panics() {
    UnionFind::new(3).union(0, 3);
}

/// One operation: 0 a union, 1 a joined question, 2 a lookup, on two items.
fn ops() -> impl Strategy<Value = (usize, Vec<(u8, usize, usize)>)> {
    (1usize..=64).prop_flat_map(|n| (Just(n), prop::collection::vec((0u8..3, 0..n, 0..n), 0..120)))
}

proptest! {
    #[test]
    fn every_operation_keeps_valid_and_answers_as_the_plain_search((n, ops) in ops()) {
        // Lean: valid_union, valid_find, valid_joined, union_spec, find_spec
        let mut u = UnionFind::new(n);
        let mut pairs = Vec::new();
        for (kind, x, y) in ops {
            let before = naive::groups(n, &pairs);
            let old = u.clone();
            match kind {
                0 => {
                    let merged = u.union(x, y);
                    prop_assert_eq!(merged, before[x] != before[y]);
                    if merged {
                        prop_assert_eq!(u.count + 1, old.count);
                    } else {
                        prop_assert_eq!(&u.rank, &old.rank);
                        prop_assert_eq!(u.count, old.count);
                    }
                    pairs.push((x, y));
                }
                1 => prop_assert_eq!(u.joined(x, y), before[x] == before[y]),
                _ => {
                    prop_assert_eq!(u.find(x), old.root_of(x));
                    prop_assert_eq!(&u.rank, &old.rank);
                    prop_assert_eq!(u.count, old.count);
                }
            }
            prop_assert!(u.is_valid());
            // The groups are the plain search's: one root per label, one label per root.
            let after = naive::groups(n, &pairs);
            let mut root_for_label = vec![usize::MAX; n];
            let mut label_for_root = vec![usize::MAX; n];
            for i in 0..n {
                let r = u.root_of(i);
                prop_assert!(root_for_label[after[i]] == usize::MAX || root_for_label[after[i]] == r);
                prop_assert!(label_for_root[r] == usize::MAX || label_for_root[r] == after[i]);
                root_for_label[after[i]] = r;
                label_for_root[r] = after[i];
            }
            prop_assert_eq!(u.count, (0..n).filter(|&i| after[i] == i).count());
        }
    }
}

/// Eight items, one group with root 3 and the path `0 → 1 → 2 → 3`: ranks 0 to 3 up the path,
/// items 4 to 7 straight under the root. Lean: `deep8` in `AlgoDesignTests/Graphs.lean`.
fn deep8() -> UnionFind {
    UnionFind {
        parent: vec![1, 2, 3, 3, 3, 3, 3, 3],
        rank: vec![0, 1, 2, 3, 0, 0, 0, 0],
        count: 1,
    }
}

/// `deep8` with one stored part replaced.
fn broken(edit: impl FnOnce(&mut UnionFind)) -> UnionFind {
    let mut u = deep8();
    edit(&mut u);
    u
}

#[test]
fn each_check_accepts_a_deep_valid_tree() {
    assert_eq!(deep8().check_valid(), Ok(()));
    assert!(deep8().one_rank_per_item());
}

#[test]
fn each_check_rejects_its_own_breakage_and_names_it() {
    // A link past the items, and a loop of two that never reaches a root.
    for u in [broken(|u| u.parent[4] = 8), broken(|u| u.parent[3] = 2)] {
        assert!(!u.is_upward_ends_at_root());
        assert_eq!(u.check_valid(), Err("invariant 1 (upward_ends_at_root)"));
    }
    // A rank equal to its parent's.
    let u = broken(|u| u.rank[1] = 2);
    assert!(u.is_upward_ends_at_root() && !u.is_ranks_rise_upward());
    assert_eq!(u.check_valid(), Err("invariant 2 (ranks_rise_upward)"));
    // A root of rank 4 over eight items, and one of rank 255, which no shift may overflow on.
    for r in [4, 255] {
        let u = broken(|u| u.rank[3] = r);
        assert!(u.is_ranks_rise_upward() && !u.is_root_rank_bounds_size());
        assert_eq!(u.check_valid(), Err("invariant 2 (root_rank_bounds_size)"));
    }
    // A count that is not the number of roots.
    let u = broken(|u| u.count = 2);
    assert!(u.is_root_rank_bounds_size() && !u.is_count_is_roots());
    assert_eq!(u.check_valid(), Err("not in the box (count_is_roots)"));
}

#[test]
fn each_check_answers_on_any_stored_state() {
    // Arrays of different lengths and links far out of range: every check answers, none panics.
    let u = UnionFind {
        parent: vec![9, 0, 2],
        rank: vec![200],
        count: 7,
    };
    assert!(!u.one_rank_per_item());
    assert!(!u.is_upward_ends_at_root());
    assert!(!u.is_ranks_rise_upward());
    assert!(u.is_root_rank_bounds_size());
    assert!(!u.is_count_is_roots());
    assert!(!u.is_valid());
}
