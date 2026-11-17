// SPDX-License-Identifier: Apache-2.0
//! Max flow: one loop around an open choice, the path rule.
//!
//! The loop starts from the zero flow and asks the rule for one round at a time; a round sends more
//! along augmenting paths of the residual graph, changing it in place, and says whether it sent
//! anything. The first round that sends nothing ends the loop. The answer is the flow and the
//! source's side of a cut: the vertices the residual graph still reaches from the source, found by
//! one last search the loop runs itself, so the cut does not depend on the rule. Its capacity
//! equals the flow amount, and no flow exceeds any cut, so the flow is the largest (Ford and
//! Fulkerson, "Maximal flow through a network", 1956).
//!
//! The library's rule is Dinic's ([`Dinic`]); Edmonds–Karp's
//! ([`EdmondsKarp`](super::EdmondsKarp)) and capacity scaling
//! ([`CapacityScaling`](super::CapacityScaling)) are the others it ships, and a caller may bring
//! its own through [`PathRule`].
//!
//! The paths each round added are recorded only in test builds and under the `unchecked` feature
//! (`max_flow_with_rounds`); the library's loop builds no list of paths.
//!
//! **Against the Python, and how fast.** The same loop, the same rules and the same ties. The
//! Python's rules also return the paths of their round; here no list of paths is built outside the
//! trace, and the rules send by changing the residual capacities of the packed arrays in place.
//!
//! Lean counterpart: `AlgoDesign.Flows.PathRule` and `PathRule.maxFlow`
//! (`Flows/MaxFlow/Loop.lean`), the contract in `Flows/MaxFlow/Spec.lean`.

use super::dinic::Dinic;
use super::network::{Capacity, Network};
use super::residual::{Augmentation, Residual};

/// A path rule: how one round of the loop chooses the paths it sends along.
///
/// A rule keeps the promise of the Lean `PathRule.Promise`: it sends only along augmenting paths,
/// each amount fitting the residual capacity of every arrow on its path when its turn comes; every
/// path it adds carries at least one unit; and a round sends nothing only when no augmenting path
/// is left. With such a rule the loop answers with a largest flow and a cut of the same amount. A
/// rule that says it sent something and did not keeps the loop running for ever.
///
/// Lean: `Flows.PathRule`, with `start` and `round`; the rule's memory is the value itself.
pub trait PathRule<C: Capacity> {
    /// Ready the rule for the zero flow of a new network, before its first round. The loop calls
    /// it; the library's rules also call it themselves when a round meets a network of another
    /// size, so a caller who drives the rounds by hand may leave it out. Does nothing unless the
    /// rule overrides it.
    fn start(&mut self, r: &Residual<C>) {
        let _ = r;
    }

    /// One round on the current flow: send along the paths the rule chooses, through
    /// [`Residual::send`], and say whether anything was sent.
    fn round(&mut self, r: &mut Residual<C>) -> bool;
}

impl<C: Capacity, R: PathRule<C> + ?Sized> PathRule<C> for &mut R {
    fn start(&mut self, r: &Residual<C>) {
        (**self).start(r);
    }

    fn round(&mut self, r: &mut Residual<C>) -> bool {
        (**self).round(r)
    }
}

/// The answer: the flow amount, the flow, and the source's side of a cut of the same amount.
///
/// Lean: `Flows.Answer`, with the amount beside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaxFlow<C = u64> {
    /// The flow amount: what leaves the source, less what comes back into it.
    pub value: u64,
    /// The amount on each arrow, by id.
    pub flow: Vec<C>,
    /// For each vertex, whether it is on the source's side of the cut: whether the residual graph
    /// reaches it from the source.
    pub side: Vec<bool>,
}

/// The labels [`MaxFlow::check_valid`] gives, in the order it checks the pieces.
const LABELS: [&str; 4] = [
    "invariant 1 (within_capacity)",
    "invariant 2 (conserved)",
    "not in the box (well_formed)",
    "promise (cut_matches_flow)",
];

/// Judging an answer on its network, anyone's, piece by piece: the box's invariants on the flow,
/// one amount per arrow, and the cut beside it. The promise's third part, that the flow is the
/// largest, needs no check of its own: no flow exceeds any cut (Lean `value_le_cutCapacity`), so a
/// cut of the flow's amount makes it the largest. The reported `value` has no piece of its own;
/// the cut is measured against what the flow itself sends. Each piece is linear in vertices plus
/// arrows, never panics, and answers `false` on a flow or side of the wrong length.
impl<C: Capacity> MaxFlow<C> {
    /// The amount on arrow `i`, read as 0 past the end of the list, as the Lean `Flow.on`.
    fn on(&self, i: usize) -> u64 {
        self.flow.get(i).map_or(0, |x| x.to_u64())
    }

    /// Box invariant 1: no arrow carries more than its capacity, or a negative amount; no amount
    /// is negative, by its unsigned type.
    ///
    /// Lean: `WithinCapacity`.
    #[must_use]
    pub fn is_within_capacity(&self, net: &Network<C>) -> bool {
        (0..net.arrow_count()).all(|i| self.on(i) <= net.arrow_capacity(i).to_u64())
    }

    /// Box invariant 2: at every vertex except the source and the sink, what comes in goes out.
    ///
    /// Lean: `Conserved`.
    #[must_use]
    pub fn is_conserved(&self, net: &Network<C>) -> bool {
        let net_out = net_out(net, |i| self.on(i));
        let (s, t) = (net.source() as usize, net.sink() as usize);
        (0..net.n()).all(|v| v == s || v == t || net_out[v] == 0)
    }

    /// Not in the box: the flow lists one amount per arrow.
    ///
    /// Lean: `WellFormed`.
    #[must_use]
    pub fn is_well_formed(&self, net: &Network<C>) -> bool {
        self.flow.len() == net.arrow_count()
    }

    /// The promise's cut: the source on one side, the sink on the other, and the capacities of
    /// arrows leaving the source's side add up to the flow amount; `side` marks every vertex.
    ///
    /// Lean: `Ops.CutMatchesFlow`.
    #[must_use]
    pub fn is_cut_matches_flow(&self, net: &Network<C>) -> bool {
        let side = &self.side;
        let (s, t) = (net.source() as usize, net.sink() as usize);
        side.len() == net.n()
            && side[s]
            && !side[t]
            && i128::try_from(cut_capacity(net, side))
                .is_ok_and(|cut| cut == net_out(net, |i| self.on(i))[s])
    }

    /// Lean `Valid` and `WellFormed` on the flow, and `Ops.CutMatchesFlow` on the cut:
    /// [`MaxFlow::is_within_capacity`], [`MaxFlow::is_conserved`], [`MaxFlow::is_well_formed`]
    /// and [`MaxFlow::is_cut_matches_flow`].
    #[must_use]
    pub fn is_valid(&self, net: &Network<C>) -> bool {
        self.check_valid(net).is_ok()
    }

    /// [`MaxFlow::is_valid`], naming the first piece that fails. Invariant 3, an integer on every
    /// arrow, holds by the type.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (within_capacity)"`, `"invariant 2 (conserved)"`,
    /// `"not in the box (well_formed)"` or `"promise (cut_matches_flow)"`.
    pub fn check_valid(&self, net: &Network<C>) -> Result<(), &'static str> {
        let pieces = [
            self.is_within_capacity(net),
            self.is_conserved(net),
            self.is_well_formed(net),
            self.is_cut_matches_flow(net),
        ];
        match pieces.iter().position(|&ok| !ok) {
            Some(i) => Err(LABELS[i]),
            None => Ok(()),
        }
    }
}

/// What leaves each vertex less what enters it, arrow `i` carrying `on(i)`; a loop adds and takes
/// away the same. At the source, the flow amount (Lean `value`). Fewer than 2^31 arrows of at most
/// `u64::MAX` each sum below 2^95, inside an `i128`.
pub(crate) fn net_out(net: &Network<impl Capacity>, on: impl Fn(usize) -> u64) -> Vec<i128> {
    let g = net.graph();
    let mut out = vec![0i128; net.n()];
    for i in 0..g.arrow_count() {
        let (tail, head) = g.arrow(i);
        out[tail as usize] += i128::from(on(i));
        out[head as usize] -= i128::from(on(i));
    }
    out
}

/// The capacities of the arrows leaving the vertices marked in `side`, which has one mark per
/// vertex (Lean `cutCapacity`). Fewer than 2^31 arrows of at most `u64::MAX` each sum below 2^95.
pub(crate) fn cut_capacity<C: Capacity>(net: &Network<C>, side: &[bool]) -> u128 {
    let g = net.graph();
    (0..g.arrow_count())
        .filter(|&i| {
            let (tail, head) = g.arrow(i);
            side[tail as usize] && !side[head as usize]
        })
        .map(|i| u128::from(net.arrow_capacity(i).to_u64()))
        .sum()
}

/// A largest flow from the source to the sink of `net`, and the source's side of a cut of the same
/// amount, by Dinic's rule. `O(n² m)` for `n` vertices and `m` arrows: at most `n` rounds, each
/// sending at most `m` paths found in `O(n m)` together.
///
/// Lean: `MaxFlow.contract` (`ops := Dinic.rule.ops`).
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow, Network};
/// use algodesign::graphs::Digraph;
///
/// // 0 → 1 → 3 and 0 → 2 → 3, and 1 → 2 between them.
/// let g = Digraph::new(4, &[(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]).unwrap();
/// let net = Network::new(g, vec![3u64, 2, 2, 1, 3], 0, 3).unwrap();
/// let answer = max_flow(&net);
/// assert_eq!(answer.value, 4);
/// assert_eq!(answer.side, [true, true, true, false]);
/// ```
#[must_use]
pub fn max_flow<C: Capacity>(net: &Network<C>) -> MaxFlow<C> {
    max_flow_with(net, Dinic::new())
}

/// A largest flow and a cut of the same amount, by the loop around `rule`: rounds until one sends
/// nothing, then one search for the cut. The cost is the rule's, plus one search linear in
/// vertices plus arrows.
///
/// The answer is a largest flow only if `rule` keeps the promise [`PathRule`] states.
///
/// Lean: `PathRule.maxFlow`, `PathRule.contract`.
///
/// # Panics
///
/// If `rule` broke the promise so that more flow enters the source than leaves it, in debug and
/// release builds alike.
///
/// # Examples
///
/// ```
/// use algodesign::flows::{max_flow, max_flow_with, CapacityScaling, EdmondsKarp, Network};
/// use algodesign::graphs::Digraph;
///
/// let g = Digraph::new(3, &[(0, 1), (1, 2), (0, 2)]).unwrap();
/// let net = Network::new(g, vec![5u32, 3, 4], 0, 2).unwrap();
/// assert_eq!(max_flow_with(&net, EdmondsKarp::new()), max_flow(&net));
/// assert_eq!(max_flow_with(&net, CapacityScaling::new()).value, 7);
/// ```
pub fn max_flow_with<C: Capacity, R: PathRule<C>>(net: &Network<C>, rule: R) -> MaxFlow<C> {
    run(net, rule, None)
}

/// [`max_flow_with`], with the paths each round added, in order: residual arrow ids from the
/// source and the amount. Rounds that added nothing are not listed. Only in test builds and under
/// the `unchecked` feature.
///
/// Lean: `Ops.rounds`, `Ops.walks`.
///
/// # Panics
///
/// As [`max_flow_with`].
#[cfg(any(test, feature = "unchecked"))]
pub fn max_flow_with_rounds<C: Capacity, R: PathRule<C>>(
    net: &Network<C>,
    rule: R,
) -> (MaxFlow<C>, Vec<Vec<Augmentation<C>>>) {
    let mut rounds = Vec::new();
    let answer = run(net, rule, Some(&mut rounds));
    (answer, rounds)
}

/// The loop, recording each round's paths into `rounds` when it is given (test builds and the
/// `unchecked` feature only).
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn run<C: Capacity, R: PathRule<C>>(
    net: &Network<C>,
    mut rule: R,
    mut rounds: Option<&mut Vec<Vec<Augmentation<C>>>>,
) -> MaxFlow<C> {
    let mut r = Residual::new(net);
    rule.start(&r);
    loop {
        watched!(r.added.clear());
        if !rule.round(&mut r) {
            break;
        }
        watched!(if let Some(rounds) = rounds.as_deref_mut() {
            if !r.added.is_empty() {
                rounds.push(std::mem::take(&mut r.added));
            }
        });
    }
    answer(net, &r)
}

/// The answer read off the final residual graph: the flow, its amount, and the vertices the last
/// search reaches.
fn answer<C: Capacity>(net: &Network<C>, r: &Residual<C>) -> MaxFlow<C> {
    let flow = r.flow();
    let g = net.graph();
    let s = net.source();
    // A loop at the source leaves it and comes back: it counts on neither side.
    // Summed in `u128`, where fewer than 2^31 arrows of at most `u64::MAX` each always fit.
    let leaving: u128 = g
        .out(s as usize)
        .iter()
        .filter(|&(to, _)| to != s)
        .map(|(_, id)| u128::from(flow[id as usize].to_u64()))
        .sum();
    let entering: u128 = g
        .incoming(s as usize)
        .iter()
        .filter(|&(from, _)| from != s)
        .map(|(_, id)| u128::from(flow[id as usize].to_u64()))
        .sum();
    // A rule that keeps the promise sends nothing into the source; leaving fits a `u64` because
    // `Network::new` refused capacities leaving the source past `u64::MAX`.
    let value = leaving
        .checked_sub(entering)
        .and_then(|v| u64::try_from(v).ok())
        .expect("the path rule broke its promise: more flow enters the source than leaves it");
    MaxFlow {
        value,
        flow,
        side: r.reached(),
    }
}

#[cfg(test)]
#[path = "unit_tests/max_flow.rs"]
mod tests;
