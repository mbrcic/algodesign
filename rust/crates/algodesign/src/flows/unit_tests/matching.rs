use super::*;
use crate::rng::SplitMix64;
use proptest::prelude::*;

/// A variant of the chapter's rooms in which Anita (0) also accepts room 2: Daniel (1) accepts
/// room 1, Tomás (2) rooms 1 and 2, Juan (3) rooms 3 and 4; room `r` is object `r - 1`.
const ROOMS: [(u32, u32); 7] = [(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 2), (3, 3)];

#[test]
fn the_rooms_match_three_and_name_the_cover_and_the_blocked_group() {
    let m = max_matching(4, 4, &ROOMS).unwrap();
    assert_eq!(m.pairs, [(0, 0), (2, 1), (3, 2)]);
    // the cover: Juan, room 1, room 2
    assert_eq!(m.cover_people, [3]);
    assert_eq!(m.cover_objects, [0, 1]);
    // Anita, Daniel and Tomás accept only rooms 1 and 2
    assert_eq!(
        m.blocked,
        Some(BlockedGroup {
            people: vec![0, 1, 2],
            objects: vec![0, 1],
        })
    );
    assert_eq!(check(4, 4, &ROOMS, &m), None);
}

#[test]
fn everyone_matched_means_no_blocked_group() {
    let m = max_matching(2, 3, &[(0, 0), (0, 1), (1, 1), (1, 2)]).unwrap();
    assert_eq!(m.pairs, [(0, 0), (1, 1)]);
    assert_eq!(m.blocked, None);
    assert_eq!(m.cover_people, [0, 1]);
    assert!(m.cover_objects.is_empty());
}

#[test]
fn no_people_or_no_pairs() {
    let m = max_matching(0, 0, &[]).unwrap();
    assert!(m.pairs.is_empty() && m.blocked.is_none());
    let m = max_matching(2, 1, &[]).unwrap();
    assert!(m.pairs.is_empty());
    assert_eq!(m.cover_people, Vec::<u32>::new());
    // nobody accepts anything: every person alone is blocked, together they accept nothing
    assert_eq!(
        m.blocked,
        Some(BlockedGroup {
            people: vec![0, 1],
            objects: vec![],
        })
    );
}

#[test]
fn a_doubled_pair_still_matches_once() {
    let m = max_matching(1, 1, &[(0, 0), (0, 0)]).unwrap();
    assert_eq!(m.pairs, [(0, 0)]);
    assert_eq!(check(1, 1, &[(0, 0), (0, 0)], &m), None);
}

#[test]
fn a_pair_outside_the_problem_is_refused() {
    assert_eq!(
        max_matching(2, 2, &[(0, 1), (2, 0)]),
        Err(MatchingError::PairOutOfRange {
            index: 1,
            person: 2,
            object: 0,
        })
    );
    assert!(max_matching(2, 2, &[(0, 2)]).is_err());
    assert_eq!(
        MatchingError::TooLarge.to_string(),
        "the matching network would be too large"
    );
}

#[test]
fn the_network_has_three_blocks_of_unit_arrows() {
    let net = network(2, 2, &[(1, 0), (0, 1)]).unwrap();
    let ends: Vec<(u32, u32)> = (0..net.arrow_count())
        .map(|i| net.graph().arrow(i))
        .collect();
    assert_eq!(ends, [(0, 1), (0, 2), (2, 3), (1, 4), (3, 5), (4, 5)]);
    assert!(net.capacity().iter().all(|&c| c == 1));
    assert_eq!((net.source(), net.sink()), (0, 5));
}

/// What breaks in `m` as an answer to the problem; `None` if nothing: the label
/// `Matching::check_valid` gives, then the library's own choices, no group beside a matching of
/// everyone and the lists in increasing order.
fn check(people: usize, objects: usize, pairs: &[(u32, u32)], m: &Matching) -> Option<String> {
    // Lean: Ops.MaximumMatching, Ops.CoverAsLarge, Ops.BlockedGroupWhenShort
    if let Err(label) = m.check_valid(people, objects, pairs) {
        return Some(label.into());
    }
    if m.blocked.is_some() && m.pairs.len() == people {
        return Some("a blocked group beside a matching of everyone".into());
    }
    let mut lists = vec![&m.cover_people, &m.cover_objects];
    if let Some(g) = &m.blocked {
        lists.extend([&g.people, &g.objects]);
    }
    if lists.iter().any(|xs| !xs.windows(2).all(|w| w[0] < w[1])) {
        return Some("a list out of order".into());
    }
    None
}

fn distinct(xs: impl Iterator<Item = u32>) -> bool {
    let mut v: Vec<u32> = xs.collect();
    let n = v.len();
    v.sort_unstable();
    v.dedup();
    v.len() == n
}

/// The size of a largest matching, by trying every set of pairs.
fn brute_force(pairs: &[(u32, u32)]) -> usize {
    (0u32..1 << pairs.len())
        .filter_map(|set| {
            let chosen: Vec<(u32, u32)> = (0..pairs.len())
                .filter(|&j| set >> j & 1 == 1)
                .map(|j| pairs[j])
                .collect();
            (distinct(chosen.iter().map(|e| e.0)) && distinct(chosen.iter().map(|e| e.1)))
                .then_some(chosen.len())
        })
        .max()
        .unwrap_or(0)
}

/// How many paths the matching's own max flow added; beside them it answers as `max_matching`.
fn paths_added(people: usize, objects: usize, pairs: &[(u32, u32)]) -> usize {
    let (m, rounds) = max_matching_with_rounds(people, objects, pairs).unwrap();
    assert_eq!(Ok(m), max_matching(people, objects, pairs));
    rounds.iter().map(Vec::len).sum()
}

fn problems() -> impl Strategy<Value = (usize, usize, Vec<(u32, u32)>)> {
    (0usize..6, 1usize..6).prop_flat_map(|(people, objects)| {
        let pair = (0..people.max(1) as u32, 0..objects as u32);
        let pairs = if people == 0 {
            Just(Vec::new()).boxed()
        } else {
            proptest::collection::vec(pair, 0..11).boxed()
        };
        (Just(people), Just(objects), pairs)
    })
}

proptest! {
    #[test]
    fn on_small_problems_the_answer_is_largest_with_its_cover_and_group(
        (people, objects, pairs) in problems()
    ) {
        let m = max_matching(people, objects, &pairs).unwrap();
        prop_assert_eq!(check(people, objects, &pairs, &m), None);
        prop_assert_eq!(m.pairs.len(), brute_force(&pairs));
        // Lean: Ops.StepsAtMostPeople
        prop_assert!(paths_added(people, objects, &pairs) <= people);
    }
}

/// A draw below `k`.
fn below(r: &mut SplitMix64, k: u64) -> u64 {
    r.next_u64() % k
}

#[test]
fn on_larger_problems_the_cover_proves_the_matching_largest() {
    let mut r = SplitMix64::new(11);
    for _ in 0..300 {
        let people = 1 + below(&mut r, 40) as usize;
        let objects = 1 + below(&mut r, 40) as usize;
        let m = below(&mut r, 200) as usize;
        let pairs: Vec<(u32, u32)> = (0..m)
            .map(|_| {
                (
                    below(&mut r, people as u64) as u32,
                    below(&mut r, objects as u64) as u32,
                )
            })
            .collect();
        let answer = max_matching(people, objects, &pairs).unwrap();
        assert_eq!(check(people, objects, &pairs, &answer), None);
        assert!(paths_added(people, objects, &pairs) <= people);
    }
}

#[test]
fn check_valid_names_each_broken_part_alone() {
    let good = max_matching(4, 4, &ROOMS).unwrap();
    assert_eq!(good.check_valid(4, 4, &ROOMS), Ok(()));
    assert!(good.is_valid(4, 4, &ROOMS));
    let group = |people: &[u32], objects: &[u32]| {
        Some(BlockedGroup {
            people: people.to_vec(),
            objects: objects.to_vec(),
        })
    };
    let answer = |pairs: &[(u32, u32)], cp: &[u32], co: &[u32], g: Option<BlockedGroup>| Matching {
        pairs: pairs.to_vec(),
        cover_people: cp.to_vec(),
        cover_objects: co.to_vec(),
        blocked: g,
    };
    let (pairs, g) = (&good.pairs[..], good.blocked.clone());
    let cases = [
        // Lean: IsMatching; a pair nobody accepts, a person twice, an object twice. Each keeps the
        // cover's size equal to the number of pairs, the cover touching every acceptable pair.
        (
            answer(&[(0, 0), (2, 1), (3, 0)], &[3], &[0, 1], g.clone()),
            "promise (maximum_matching)",
        ),
        (
            answer(&[(0, 0), (0, 1), (3, 2)], &[3], &[0, 1], g.clone()),
            "promise (maximum_matching)",
        ),
        (
            answer(&[(0, 0), (2, 0), (3, 2)], &[3], &[0, 1], g.clone()),
            "promise (maximum_matching)",
        ),
        // Lean: Ops.CoverAsLarge; a pair it misses (Juan's (3, 2)), someone twice, someone outside
        // the problem, and a cover one larger than the matching.
        (
            answer(pairs, &[0], &[0, 1], g.clone()),
            "promise (cover_as_large)",
        ),
        (
            answer(pairs, &[3], &[0, 0], g.clone()),
            "promise (cover_as_large)",
        ),
        (
            answer(pairs, &[4], &[0, 1], g.clone()),
            "promise (cover_as_large)",
        ),
        (
            answer(pairs, &[3, 0], &[0, 1], g.clone()),
            "promise (cover_as_large)",
        ),
        // Lean: Ops.BlockedGroupWhenShort; no group, a person twice, a person outside the problem,
        // an object nobody of them accepts, one they accept missing, and as many objects as people.
        (
            answer(pairs, &[3], &[0, 1], None),
            "promise (blocked_group_when_short)",
        ),
        (
            answer(pairs, &[3], &[0, 1], group(&[0, 0, 1], &[0, 1])),
            "promise (blocked_group_when_short)",
        ),
        (
            answer(pairs, &[3], &[0, 1], group(&[0, 1, 4], &[0, 1])),
            "promise (blocked_group_when_short)",
        ),
        (
            answer(pairs, &[3], &[0, 1], group(&[0, 1, 2], &[0, 1, 2])),
            "promise (blocked_group_when_short)",
        ),
        (
            answer(pairs, &[3], &[0, 1], group(&[0, 1, 2], &[0])),
            "promise (blocked_group_when_short)",
        ),
        (
            answer(pairs, &[3], &[0, 1], group(&[0, 2], &[0, 1])),
            "promise (blocked_group_when_short)",
        ),
    ];
    for (m, label) in &cases {
        assert_eq!(m.check_valid(4, 4, &ROOMS), Err(*label), "{m:?}");
        assert!(!m.is_valid(4, 4, &ROOMS));
    }
    // When everyone is matched no group is asked for, and any group passes.
    let full = answer(&[(0, 0)], &[0], &[], group(&[], &[]));
    assert_eq!(full.check_valid(1, 1, &[(0, 0)]), Ok(()));
}

/// The zero flow on the matching network, then the flow after every round of its max flow.
fn flows_of_rounds(people: usize, objects: usize, pairs: &[(u32, u32)]) -> Vec<Vec<u64>> {
    let (_, rounds) = max_matching_with_rounds(people, objects, pairs).unwrap();
    let mut flow = vec![0u64; people + pairs.len() + objects];
    let mut out = vec![flow.clone()];
    for sent in rounds {
        for x in sent {
            for &e in &x.path {
                let i = e as usize / 2;
                if e % 2 == 0 {
                    flow[i] += x.amount;
                } else {
                    flow[i] -= x.amount;
                }
            }
        }
        out.push(flow.clone());
    }
    out
}

#[test]
fn every_flow_of_the_rounds_keeps_the_invariant() {
    // Lean: Matching.Ops.startValid, Matching.Ops.roundsKeep
    let mut r = SplitMix64::new(26);
    for _ in 0..200 {
        let (people, objects) = (below(&mut r, 6) as usize, 1 + below(&mut r, 5) as usize);
        let pairs: Vec<(u32, u32)> = if people == 0 {
            Vec::new()
        } else {
            (0..below(&mut r, 11))
                .map(|_| {
                    (
                        below(&mut r, people as u64) as u32,
                        below(&mut r, objects as u64) as u32,
                    )
                })
                .collect()
        };
        for flow in flows_of_rounds(people, objects, &pairs) {
            let st = State::new(people, objects, &pairs, flow).unwrap();
            assert_eq!(st.check_valid(), Ok(()), "{st:?}");
            assert!(st.is_valid());
        }
    }
}

#[test]
fn state_names_a_flow_that_breaks_max_flows_invariants() {
    // Lean: Matching.FlowRespected, on the network 0 → person → object → sink
    let st = |flow: Vec<u64>| State::new(1, 1, &[(0, 0)], flow).unwrap();
    assert!(st(vec![1, 1, 1]).is_flow_respected());
    // An amount past the arrows is read by no piece: the Lean state has no `WellFormed`.
    assert!(st(vec![1, 1, 1, 5]).is_valid());
    for flow in [vec![2, 2, 2], vec![1, 1, 0], vec![0, 1, 1]] {
        let s = st(flow);
        assert_eq!(
            s.check_valid(),
            Err("invariant 1 (flow_respected)"),
            "{s:?}"
        );
        assert!(!s.is_flow_respected() && !s.is_valid());
    }
    assert_eq!(st(vec![1, 1, 1]).flow(), [1, 1, 1]);
    assert!(matches!(
        State::new(1, 1, &[(0, 1)], vec![0; 3]),
        Err(MatchingError::PairOutOfRange { index: 0, .. })
    ));
}
