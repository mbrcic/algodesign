// SPDX-License-Identifier: Apache-2.0
//! Matching people with objects: a reduction to max flow, with König's cover and Hall's blocked
//! group read from its last search.
//!
//! The matching network has the source at vertex 0, person `p` at `1 + p`, object `o` at
//! `1 + people + o`, and the sink last. Its arrows come in three blocks, each in order: the source
//! to every person, one arrow per acceptable pair in input order, and every object to the sink;
//! every arrow carries 1. The library's max flow (Dinic's rule) runs on it; with an integer flow
//! every arrow carries 0 or 1, and the pairs whose arrows carry 1 are a matching, listed in input
//! order. The vertices the last search reached give the rest: the people it did not reach and the
//! objects it reached are a cover, as many as there are pairs, with every acceptable pair incident
//! to one of them, so no matching is larger (König, 1931); when someone stays unmatched, the people
//! it reached accept between them fewer objects than there are of them (Hall, 1935). The network is
//! that of Korte and Vygen, *Combinatorial Optimization*.
//!
//! Cost: as max flow on `n + k + 2` vertices and `n + m + k` arrows, for `n` people, `k` objects
//! and `m` acceptable pairs; every added path carries one unit out of one person, so at most `n`
//! of them.
//!
//! [`State`] is a flow on a problem's matching network, the state those rounds change; its
//! [`State::check_valid`] judges it by the box's one invariant, max flow's invariants on that
//! network.
//!
//! **Against the Python, and how fast.** Both build the same network and run Dinic's rule on it;
//! here a problem whose network would be too large is refused. Its speed is Dinic's rule on unit
//! arrows, plus one pass to read the pairs, the cover and the group.
//!
//! Lean counterpart: `AlgoDesign.Flows.Matching` (`Flows/Matching.lean`), the contract in
//! `Flows/Matching/Spec.lean`.

use std::collections::BTreeSet;
use std::fmt;

use super::dinic::Dinic;
#[cfg(any(test, feature = "unchecked"))]
use super::max_flow::max_flow_with_rounds;
use super::max_flow::{max_flow_with, MaxFlow};
use super::network::Network;
#[cfg(any(test, feature = "unchecked"))]
use super::residual::Augmentation;
use crate::graphs::Digraph;

/// Why a matching problem was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchingError {
    /// An acceptable pair names a person or an object outside the problem.
    PairOutOfRange {
        /// The pair's position in the input.
        index: usize,
        /// The person it names.
        person: u32,
        /// The object it names.
        object: u32,
    },
    /// The matching network would have more vertices or arrows than a network may have.
    TooLarge,
}

impl fmt::Display for MatchingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PairOutOfRange {
                index,
                person,
                object,
            } => write!(
                f,
                "pair {index} = ({person}, {object}) names a person or an object outside the \
                 problem"
            ),
            Self::TooLarge => write!(f, "the matching network would be too large"),
        }
    }
}

impl std::error::Error for MatchingError {}

/// A blocked group: some people, and the objects they accept between them, fewer than the people.
///
/// Lean: `Matching.Group`, `IsBlocked`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockedGroup {
    /// The people of the group, in increasing order.
    pub people: Vec<u32>,
    /// Every object some person of the group accepts, in increasing order.
    pub objects: Vec<u32>,
}

/// The answer: the matched pairs, a cover as large, and a blocked group when someone stays
/// unmatched.
///
/// Lean: `Matching.Answer`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Matching {
    /// The matched pairs `(person, object)`, in input order.
    pub pairs: Vec<(u32, u32)>,
    /// The cover's people, in increasing order: those the last search did not reach.
    pub cover_people: Vec<u32>,
    /// The cover's objects, in increasing order: those the last search reached.
    pub cover_objects: Vec<u32>,
    /// When some person stays unmatched, the people the last search reached and the objects they
    /// accept; `None` when everyone is matched.
    pub blocked: Option<BlockedGroup>,
}

/// Whether no entry of `xs` appears twice.
fn distinct(xs: impl IntoIterator<Item = u32>) -> bool {
    let mut seen = BTreeSet::new();
    xs.into_iter().all(|x| seen.insert(x))
}

/// Judging an answer on its problem, anyone's, by the promise's three parts. That no matching is
/// larger needs no check of its own: no matching is larger than a cover (Lean
/// `matching_le_cover`), so a cover as large as the matching makes it a maximum one. The box's
/// invariant, max flow's on the matching network, is about the flow, which the answer does not
/// carry, so it is no piece here: [`State`] checks it on a flow, and the Lean proves that every
/// round keeps it (`Ops.roundsKeep`).
/// Each piece never panics, and takes `O(e log e)` time for `e` entries in the answer and the
/// acceptable pairs together.
impl Matching {
    /// The promise's matching: acceptable pairs, each person in at most one and each object in at
    /// most one.
    ///
    /// Lean: `Ops.MaximumMatching`, its `IsMatching`.
    #[must_use]
    pub fn is_maximum_matching(&self, pairs: &[(u32, u32)]) -> bool {
        let acceptable: BTreeSet<(u32, u32)> = pairs.iter().copied().collect();
        self.pairs.iter().all(|e| acceptable.contains(e))
            && distinct(self.pairs.iter().map(|&(p, _)| p))
            && distinct(self.pairs.iter().map(|&(_, o)| o))
    }

    /// The promise's cover: as many people and objects as there are pairs, none listed twice, with
    /// every acceptable pair incident to one of them.
    ///
    /// Lean: `Ops.CoverAsLarge`, its `IsCover`.
    #[must_use]
    pub fn is_cover_as_large(&self, people: usize, objects: usize, pairs: &[(u32, u32)]) -> bool {
        let (cp, co) = (&self.cover_people, &self.cover_objects);
        let in_cp: BTreeSet<u32> = cp.iter().copied().collect();
        let in_co: BTreeSet<u32> = co.iter().copied().collect();
        in_cp.len() == cp.len()
            && in_co.len() == co.len()
            && cp.iter().all(|&p| (p as usize) < people)
            && co.iter().all(|&o| (o as usize) < objects)
            && pairs
                .iter()
                .all(|(p, o)| in_cp.contains(p) || in_co.contains(o))
            && cp.len() + co.len() == self.pairs.len()
    }

    /// The promise's blocked group: if some person stays unmatched, some people, none listed
    /// twice, beside exactly the objects they accept between them, fewer of those than there are
    /// people.
    ///
    /// Lean: `Ops.BlockedGroupWhenShort`, its `IsBlocked`.
    #[must_use]
    pub fn is_blocked_group_when_short(&self, people: usize, pairs: &[(u32, u32)]) -> bool {
        if self.pairs.len() >= people {
            return true;
        }
        let Some(g) = &self.blocked else {
            return false;
        };
        let group: BTreeSet<u32> = g.people.iter().copied().collect();
        let accepted: BTreeSet<u32> = pairs
            .iter()
            .filter(|(p, _)| group.contains(p))
            .map(|&(_, o)| o)
            .collect();
        let objects: BTreeSet<u32> = g.objects.iter().copied().collect();
        group.len() == g.people.len()
            && g.people.iter().all(|&p| (p as usize) < people)
            && objects.len() == g.objects.len()
            && objects == accepted
            && g.objects.len() < g.people.len()
    }

    /// The promise's three parts, `Ops.MaximumMatching`, `Ops.CoverAsLarge` and
    /// `Ops.BlockedGroupWhenShort`: [`Matching::is_maximum_matching`],
    /// [`Matching::is_cover_as_large`] and [`Matching::is_blocked_group_when_short`].
    #[must_use]
    pub fn is_valid(&self, people: usize, objects: usize, pairs: &[(u32, u32)]) -> bool {
        self.check_valid(people, objects, pairs).is_ok()
    }

    /// [`Matching::is_valid`], naming the first part that fails.
    ///
    /// # Errors
    ///
    /// `"promise (maximum_matching)"`, `"promise (cover_as_large)"` or
    /// `"promise (blocked_group_when_short)"`.
    pub fn check_valid(
        &self,
        people: usize,
        objects: usize,
        pairs: &[(u32, u32)],
    ) -> Result<(), &'static str> {
        if !self.is_maximum_matching(pairs) {
            return Err("promise (maximum_matching)");
        }
        if !self.is_cover_as_large(people, objects, pairs) {
            return Err("promise (cover_as_large)");
        }
        if !self.is_blocked_group_when_short(people, pairs) {
            return Err("promise (blocked_group_when_short)");
        }
        Ok(())
    }
}

/// A flow on a problem's matching network, the state the rounds of max flow change: the problem's
/// matching network, and the amount on each of its arrows by id.
///
/// Lean: `Matching.State`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    net: Network,
    flow: Vec<u64>,
}

impl State {
    /// The state of `flow` on the matching network of `people` people, `objects` objects and the
    /// acceptable `pairs`; the flow lists one amount per arrow, by id, in the network's three
    /// blocks.
    ///
    /// # Errors
    ///
    /// As [`max_matching`], for the problem.
    pub fn new(
        people: usize,
        objects: usize,
        pairs: &[(u32, u32)],
        flow: Vec<u64>,
    ) -> Result<Self, MatchingError> {
        Ok(Self {
            net: network(people, objects, pairs)?,
            flow,
        })
    }

    /// The amount on each arrow of the matching network, by id.
    #[must_use]
    pub fn flow(&self) -> &[u64] {
        &self.flow
    }

    /// Box invariant 1: those of max flow, on this network; no arrow carries more than its
    /// capacity, and at every vertex but the source and the sink what comes in goes out. Linear in
    /// vertices plus arrows; an amount past the arrows is read by no piece.
    ///
    /// Lean: `FlowRespected`.
    #[must_use]
    pub fn is_flow_respected(&self) -> bool {
        let f = MaxFlow {
            value: 0,
            flow: self.flow.clone(),
            side: Vec::new(),
        };
        f.is_within_capacity(&self.net) && f.is_conserved(&self.net)
    }

    /// Lean `Valid`: [`State::is_flow_respected`].
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.check_valid().is_ok()
    }

    /// [`State::is_valid`], naming the piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (flow_respected)"`.
    pub fn check_valid(&self) -> Result<(), &'static str> {
        if !self.is_flow_respected() {
            return Err("invariant 1 (flow_respected)");
        }
        Ok(())
    }
}

/// A maximum matching of `people` people with `objects` objects, person `p` accepting object `o`
/// for every `(p, o)` in `pairs`; beside it a cover as large, and a blocked group when someone
/// stays unmatched. `O((n + k)² (n + m + k))` for `n` people, `k` objects and `m` pairs, as max
/// flow by Dinic's rule.
///
/// Lean: `Matching.contract`.
///
/// # Errors
///
/// [`MatchingError::PairOutOfRange`] for the first pair that names a person or an object outside
/// the problem, and [`MatchingError::TooLarge`] when the matching network would have too many
/// vertices or arrows.
///
/// # Examples
///
/// ```
/// use algodesign::flows::max_matching;
///
/// // The chapter's quiet rooms, the people in the order of its hand run: Tomás (0) accepts
/// // rooms 1 and 2, Daniel (1) and Anita (2) room 1, Juan (3) rooms 3 and 4; room r is object
/// // r - 1.
/// let pairs = [(0, 0), (0, 1), (1, 0), (2, 0), (3, 2), (3, 3)];
/// let m = max_matching(4, 4, &pairs).unwrap();
/// // Tomás moves to room 2, Daniel takes room 1, Juan room 3; Anita stays out.
/// assert_eq!(m.pairs, [(0, 1), (1, 0), (3, 2)]);
/// // the cover: Tomás, Juan, room 1
/// assert_eq!((m.cover_people, m.cover_objects), (vec![0, 3], vec![0]));
/// // Daniel and Anita accept only room 1
/// let group = m.blocked.unwrap();
/// assert_eq!((group.people, group.objects), (vec![1, 2], vec![0]));
/// ```
pub fn max_matching(
    people: usize,
    objects: usize,
    pairs: &[(u32, u32)],
) -> Result<Matching, MatchingError> {
    matching_by(people, objects, pairs, max_flow_with)
}

/// [`max_matching`], with the paths each round of its max flow added on the matching network, in
/// order: residual arrow ids from the source and the amount. Rounds that added nothing are not
/// listed. Only in test builds and under the `unchecked` feature.
///
/// Lean: `Matching.Ops.rounds`, `Matching.Ops.walks`.
///
/// # Errors
///
/// As [`max_matching`].
#[cfg(any(test, feature = "unchecked"))]
pub fn max_matching_with_rounds(
    people: usize,
    objects: usize,
    pairs: &[(u32, u32)],
) -> Result<(Matching, Vec<Vec<Augmentation>>), MatchingError> {
    let mut rounds = Vec::new();
    let m = matching_by(people, objects, pairs, |net, rule| {
        let (answer, added) = max_flow_with_rounds(net, rule);
        rounds = added;
        answer
    })?;
    Ok((m, rounds))
}

/// The matching read from `flow`, max flow by Dinic's rule on the matching network: the pairs that
/// carry the unit, and the cover and the blocked group read from its last search.
fn matching_by(
    people: usize,
    objects: usize,
    pairs: &[(u32, u32)],
    flow: impl FnOnce(&Network, Dinic) -> MaxFlow,
) -> Result<Matching, MatchingError> {
    let net = network(people, objects, pairs)?;
    let answer = flow(&net, Dinic::new());
    let side = &answer.side;
    let reached_person = |p: usize| side[1 + p];
    let matched: Vec<(u32, u32)> = pairs
        .iter()
        .zip(&answer.flow[people..people + pairs.len()])
        .filter(|&(_, &x)| x > 0)
        .map(|(&e, _)| e)
        .collect();
    let cover_people = ids(people, |p| !reached_person(p));
    let cover_objects = ids(objects, |o| side[1 + people + o]);
    let blocked = (matched.len() < people).then(|| {
        let mut accepted = vec![false; objects];
        for &(p, o) in pairs {
            if reached_person(p as usize) {
                accepted[o as usize] = true;
            }
        }
        BlockedGroup {
            people: ids(people, reached_person),
            objects: ids(objects, |o| accepted[o]),
        }
    });
    Ok(Matching {
        pairs: matched,
        cover_people,
        cover_objects,
        blocked,
    })
}

/// The ids below `n` that `keep` keeps, in increasing order; `n` is below the network's vertex
/// count, which fits a `u32`.
fn ids(n: usize, keep: impl Fn(usize) -> bool) -> Vec<u32> {
    (0..n).filter(|&i| keep(i)).map(|i| i as u32).collect()
}

/// The matching network: the source 0, the people, the objects, the sink; one unit from the source
/// to every person, on every pair, and from every object to the sink, in that order.
///
/// Lean: `Matching.Problem.network`.
fn network(people: usize, objects: usize, pairs: &[(u32, u32)]) -> Result<Network, MatchingError> {
    for (index, &(person, object)) in pairs.iter().enumerate() {
        if person as usize >= people || object as usize >= objects {
            return Err(MatchingError::PairOutOfRange {
                index,
                person,
                object,
            });
        }
    }
    let n = people
        .checked_add(objects)
        .and_then(|v| v.checked_add(2))
        .filter(|&n| u32::try_from(n).is_ok())
        .ok_or(MatchingError::TooLarge)?;
    // n fits a u32, so do the people and objects and the vertex ids below n.
    let first_object = 1 + people as u32;
    let sink = (n - 1) as u32;
    let mut arrows = Vec::with_capacity(people + pairs.len() + objects);
    arrows.extend((1..first_object).map(|v| (0, v)));
    arrows.extend(pairs.iter().map(|&(p, o)| (1 + p, first_object + o)));
    arrows.extend((first_object..sink).map(|v| (v, sink)));
    let ones = vec![1u64; arrows.len()];
    let g = Digraph::new(n, &arrows).map_err(|_| MatchingError::TooLarge)?;
    Network::new(g, ones, 0, sink).map_err(|_| MatchingError::TooLarge)
}

#[cfg(test)]
#[path = "unit_tests/matching.rs"]
mod tests;
