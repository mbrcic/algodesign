// SPDX-License-Identifier: Apache-2.0
//! Strong components: the groups of vertices that all reach each other, numbered so that every
//! arrow between two groups goes from a smaller number to a larger one.
//!
//! [`strong_components`] is Tarjan and Zwick's Algorithm T (2024, arXiv 2201.07197v3, Fig. 2,
//! p. 12) in their Implementation A with the two-ended shared array (§6.4, p. 23): one array of
//! `n + 1` slots holds the walk stack P (the row positions of the arrows on the current path) from
//! the bottom up and the followers stack F (vertices finished while their group is open) from the
//! top down; the path and F never share a vertex, so the two ends never meet. The slot past them
//! holds Fig. 2's guard, a vertex whose `low` stays 0, so popping F needs no emptiness test.
//!
//! `low` is packed as in Fig. 4: entering a vertex adds 2 to the clock and stores it, so a vertex
//! that still leads its group holds an even value and one whose `low` dropped holds the smaller
//! value with its lowest bit set. 0 means not entered. Live values never pass `2n`, which the
//! graph's limit `n < 2³¹` keeps below `u32::MAX`, the value a vertex gets when its group comes out
//! (Fig. 2's ∞): above every live value, so it never lowers anyone. A group's id cannot ride in
//! `low` too (at `n` near 2³¹ the live values already fill the word), so each group is written to
//! the members array as it comes out, and at the end the `low` array is overwritten with the group
//! of every vertex. The walk stops when done (p. 12), checked where a `low` drops: once every
//! vertex is entered and the current vertex's `low` drops to the root's, F and the path are one
//! group; its members are written in the order running to the end would give.
//!
//! Groups come out sinks first; group id = count − 1 − the order it came out, so the ids are a
//! topological order of the graph of groups (AtCoder `internal_scc.hpp`, l. 56–58). A group's
//! members are in postorder, as T emits them: its followers in the order they finished, then its
//! leader.
//!
//! [`kosaraju_sharir`] is the second method (CLRS 4th ed., §20.5, p. 577): a depth-first walk on
//! the forward rows records the finishing order, and a walk on the reversed rows, started from
//! vertices in decreasing finishing order, finds one group per start, in topological order. Members
//! in the order the second walk enters them.
//!
//! [`condensation`] is the graph of groups (TZ §3.3, p. 10) and [`check_components`] checks a
//! grouping it did not compute. Loops and doubled arrows are accepted everywhere; a group of one is
//! cyclic exactly when its vertex has a loop. Nothing recurses on the call stack.
//!
//! [`Walk`] is a state of Algorithm T's walk, with one check per piece of the Lean `Valid` on it.
//!
//! Lean counterpart: `AlgoDesign.Graphs.Scc`.

use std::fmt;

use super::digraph::Digraph;
use super::topo::topological_order;

/// The `low` of a vertex whose group is out: larger than every live value (at most `2n`).
const DONE: u32 = u32::MAX;

/// The strong components of a directed graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Components {
    /// The group of each vertex.
    group_of: Vec<u32>,
    /// Where each group's members start in `members`; `count + 1` values.
    offsets: Vec<usize>,
    /// The members of every group, group 0 first.
    members: Vec<u32>,
}

impl Components {
    /// The number of groups.
    #[must_use]
    pub fn count(&self) -> usize {
        self.offsets.len() - 1
    }

    /// The group of vertex `v`.
    ///
    /// # Panics
    ///
    /// If `v` is not a vertex.
    #[must_use]
    pub fn group_of(&self, v: usize) -> u32 {
        let n = self.group_of.len();
        assert!(v < n, "vertex {v} out of range 0..{n}");
        self.group_of[v]
    }

    /// The group of every vertex, indexed by vertex.
    #[must_use]
    pub fn group_of_each(&self) -> &[u32] {
        &self.group_of
    }

    /// The members of group `i`, in the order the method found them.
    ///
    /// # Panics
    ///
    /// If `i` is not below [`Components::count`].
    #[must_use]
    pub fn group(&self, i: usize) -> &[u32] {
        let k = self.count();
        assert!(i < k, "group {i} out of range 0..{k}");
        &self.members[self.offsets[i]..self.offsets[i + 1]]
    }

    /// The grouping `group_of` with ids `0..count`, each used, members in increasing vertex order.
    fn from_group_of(group_of: Vec<u32>, count: usize) -> Self {
        let mut offsets = vec![0usize; count + 1];
        for &c in &group_of {
            offsets[c as usize + 1] += 1;
        }
        for i in 0..count {
            offsets[i + 1] += offsets[i];
        }
        let mut next = offsets.clone();
        let mut members = vec![0u32; group_of.len()];
        for (v, &c) in (0u32..).zip(&group_of) {
            members[next[c as usize]] = v;
            next[c as usize] += 1;
        }
        Self {
            group_of,
            offsets,
            members,
        }
    }
}

/// Algorithm T: the strong components, ids in topological order, members in postorder. Linear in
/// vertices plus arrows; `2n` words of work space besides the answer.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{strong_components, Digraph};
///
/// // 0 ⇄ 1 → 2: two groups; the ids run along the arrows between them.
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// let c = strong_components(&g);
/// assert_eq!(c.count(), 2);
/// assert_eq!(c.group_of_each(), [0, 0, 1]);
/// // Members in postorder: the follower 1, then the leader 0.
/// assert_eq!(c.group(0), [1, 0]);
/// ```
#[must_use]
pub fn strong_components(g: &Digraph) -> Components {
    algorithm_t(g, &mut ()).0
}

/// What Algorithm T shows as it goes: each vertex as it is entered, with the clock, as it finishes,
/// each arrow it comes back over, and its state after every step. Only test builds and the
/// `unchecked` feature make the calls; `Walk::trace` records the states.
#[cfg_attr(not(any(test, feature = "unchecked")), allow(dead_code))]
trait Watch {
    /// `v` is entered; its `low` is the clock.
    fn enter(&mut self, _v: usize, _clock: u32) {}
    /// `v` finishes.
    fn finish(&mut self, _v: usize) {}
    /// The walk comes back over the arrow `v` → `w`.
    fn retreat(&mut self, _v: usize, _w: usize) {}
    /// The state after a step.
    fn step(&mut self, _state: &Parts<'_>) {}
}

impl Watch for () {}

/// Algorithm T's own arrays, as a step leaves them.
// Read only by the recorder the tests use.
#[cfg_attr(not(any(test, feature = "unchecked")), allow(dead_code))]
struct Parts<'a> {
    low: &'a [u32],
    stack: &'a [u32],
    ftop: usize,
    members: &'a [u32],
    offsets: &'a [usize],
    k: usize,
}

/// Algorithm T and the clock at its end, twice the number of vertices entered: the largest live
/// `low` it ever stored. Shows `watch` each step.
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn algorithm_t(g: &Digraph, watch: &mut impl Watch) -> (Components, u32) {
    let n = g.n();
    let (off, nb) = (&g.out.offsets, &g.out.neighbours);
    // low[n] is the guard's, always 0; vertex n is the guard.
    let mut low = vec![0u32; n + 1];
    // P in stack[0..psize] (row positions), F in stack[ftop..n] (vertices, top at ftop).
    let mut stack = vec![0u32; n + 1];
    stack[n] = n as u32;
    let mut ftop = n;
    // Groups are written from the back, so they end in id order; each block in postorder.
    let mut members = vec![0u32; n];
    let mut back = n;
    // Each group's start, also written from the back; offsets[k] is the newest.
    let mut offsets = vec![0usize; n + 1];
    offsets[n] = n;
    let mut k = n;
    // Twice the number of vertices entered; 2n once all are (n < 2³¹, so it fits).
    let mut time = 0u32;
    let all_entered = 2 * n as u32;
    // Show `watch` the state a step leaves.
    macro_rules! show {
        () => {
            watched!(watch.step(&Parts {
                low: &low,
                stack: &stack,
                ftop,
                members: &members,
                offsets: &offsets,
                k,
            }))
        };
    }

    'roots: for s in 0..n {
        if low[s] != 0 {
            continue;
        }
        time += 2;
        low[s] = time;
        watched!(watch.enter(s, time));
        show!();
        let mut psize = 0usize;
        let mut v = s;
        let mut a = off[s];
        let mut end = off[s + 1];
        loop {
            let w;
            if a < end {
                w = nb[a] as usize;
                if low[w] == 0 {
                    // Tree arrow: push it on P and enter w.
                    debug_assert!(psize < ftop);
                    stack[psize] = a as u32;
                    psize += 1;
                    time += 2;
                    debug_assert!(time < DONE);
                    low[w] = time;
                    watched!(watch.enter(w, time));
                    show!();
                    v = w;
                    a = off[w];
                    end = off[w + 1];
                    continue;
                }
            } else {
                // v finishes.
                watched!(watch.finish(v));
                let vl = low[v];
                if vl & 1 == 0 {
                    // v leads: its group is v and every vertex on F with a low at least v's.
                    back -= 1;
                    members[back] = v as u32;
                    low[v] = DONE;
                    loop {
                        let x = stack[ftop] as usize;
                        if low[x] < vl {
                            break;
                        }
                        low[x] = DONE;
                        back -= 1;
                        members[back] = x as u32;
                        ftop += 1;
                    }
                    k -= 1;
                    offsets[k] = back;
                } else {
                    ftop -= 1;
                    debug_assert!(psize <= ftop);
                    stack[ftop] = v as u32;
                }
                if psize == 0 {
                    show!();
                    break;
                }
                // Back over the tree arrow that entered v.
                psize -= 1;
                a = stack[psize] as usize;
                w = v;
                v = if psize == 0 {
                    s
                } else {
                    nb[stack[psize - 1] as usize] as usize
                };
                end = off[v + 1];
            }
            // Retreat over v -> w: climb to w's low if it is smaller.
            watched!(watch.retreat(v, w));
            let wl = low[w];
            if wl < low[v] {
                let dropped = wl | 1;
                debug_assert!(dropped < DONE);
                low[v] = dropped;
                if time == all_entered && dropped == low[s] | 1 {
                    // Stop when done: every vertex is entered and v's low has just dropped to the
                    // root's. F (in the order it finished), the path top down, then s come out as
                    // one group.
                    for &x in &stack[..psize] {
                        low[nb[x as usize] as usize] = DONE;
                    }
                    low[s] = DONE;
                    back -= 1;
                    members[back] = s as u32;
                    for &x in &stack[..psize] {
                        back -= 1;
                        members[back] = nb[x as usize];
                    }
                    for &x in &stack[ftop..n] {
                        low[x as usize] = DONE;
                        back -= 1;
                        members[back] = x;
                    }
                    k -= 1;
                    offsets[k] = back;
                    // The walk's end as running on would reach it: the path finished top down,
                    // F holding the guard alone.
                    for &x in stack[..psize].iter().rev() {
                        watched!(watch.finish(nb[x as usize] as usize));
                    }
                    watched!(watch.finish(s));
                    watched!(ftop = n);
                    show!();
                    break 'roots;
                }
            }
            show!();
            a += 1;
        }
    }
    debug_assert_eq!(back, 0);
    debug_assert_eq!(time, all_entered);
    // The group that came out last has id 0 and starts at offsets[k].
    offsets.drain(..k);
    low.truncate(n);
    let mut group_of = low;
    for (c, w) in (0u32..).zip(offsets.windows(2)) {
        for &x in &members[w[0]..w[1]] {
            group_of[x as usize] = c;
        }
    }
    let comps = Components {
        group_of,
        offsets,
        members,
    };
    (comps, time)
}

/// A state of Algorithm T's walk, as the walk holds it, with what the invariants read and the walk
/// never does: each vertex's entry clock, the vertices in the order they finished, and the arrows
/// the walk has come back over, in order. `low` is packed as the walk packs it (an even clock while
/// the vertex may lead, the smaller clock with its lowest bit set once it dropped, `u32::MAX` once
/// its group is out); F is `stack[ftop..]`, top first, the guard last; the groups out so far are
/// the runs of `members` that `offsets[k..]` marks out, the first out last. The states run up to
/// the step at which the walk stops when done. They come only from the walk itself, under the
/// `unchecked` feature, for tests that watch it: `cargo test --features unchecked`.
///
/// Lean: `Scc.Walk`; the checks below are the pieces of `AlgorithmT.Valid`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Walk {
    /// Each vertex's packed `low`, then the guard's, 0.
    low: Vec<u32>,
    /// The shared stack: P from the bottom, F from `ftop` up to the guard in the last slot.
    stack: Vec<u32>,
    /// Where F's top is in `stack`.
    ftop: usize,
    /// The groups' members, written from the back.
    members: Vec<u32>,
    /// Where each group starts in `members`; the groups out are those from `k` on.
    offsets: Vec<usize>,
    /// The first entry of `offsets` in use.
    k: usize,
    /// Each vertex's clock when it was entered; 0 if not entered.
    pre: Vec<u32>,
    /// The vertices in the order they finished.
    finished: Vec<u32>,
    /// The arrows the walk has come back over, in order, as (from, to).
    retreats: Vec<(u32, u32)>,
}

/// Each vertex's vertices reachable along arrows, itself included: `reach[u][v]` when `u` reaches
/// `v`. One search per vertex.
fn reachability(g: &Digraph) -> Vec<Vec<bool>> {
    let n = g.n();
    (0..n)
        .map(|u| {
            let mut seen = vec![false; n];
            seen[u] = true;
            let mut stack = vec![u];
            while let Some(v) = stack.pop() {
                for (w, _) in g.out(v).iter() {
                    if !seen[w as usize] {
                        seen[w as usize] = true;
                        stack.push(w as usize);
                    }
                }
            }
            seen
        })
        .collect()
}

/// What the invariants read off the graph: who reaches whom both ways.
struct Mutual {
    reach: Vec<Vec<bool>>,
}

impl Mutual {
    /// Whether `u` and `v` reach each other; any number reaches itself, and nothing past the
    /// vertices reaches another.
    fn holds(&self, u: usize, v: usize) -> bool {
        u == v
            || (u < self.reach.len()
                && v < self.reach.len()
                && self.reach[u][v]
                && self.reach[v][u])
    }
}

impl Walk {
    fn pre_of(&self, v: usize) -> u32 {
        self.pre.get(v).copied().unwrap_or(0)
    }

    fn low_of(&self, v: usize) -> u32 {
        self.low.get(v).copied().unwrap_or(0)
    }

    /// The groups out so far, in the order they came out, each in postorder.
    fn groups(&self) -> Vec<&[u32]> {
        let ends = self.offsets.get(self.k..).unwrap_or(&[]);
        ends.windows(2)
            .rev()
            .map(|w| self.members.get(w[0]..w[1]).unwrap_or(&[]))
            .collect()
    }

    fn out(&self, v: usize) -> bool {
        self.groups().iter().any(|m| m.contains(&(v as u32)))
    }

    /// The leader of `v`'s strong component, its first-entered member, has finished.
    fn leader_out(&self, g: &Digraph, mutual: &Mutual, v: usize) -> bool {
        (0..g.n()).any(|u| {
            mutual.holds(u, v)
                && self.finished.contains(&(u as u32))
                && (0..g.n()).all(|x| {
                    !mutual.holds(x, v) || self.pre_of(x) == 0 || self.pre_of(u) <= self.pre_of(x)
                })
        })
    }

    /// The least entry clock `v` reaches along a retreating path inside its component, every
    /// arrow of which the walk has come back over, taking the retreats in order: the arrow
    /// retreated `b`-th extends a path only if the rest uses arrows retreated before it.
    fn climb_back(&self, g: &Digraph, mutual: &Mutual, v: usize) -> u32 {
        let n = g.n();
        let mut reach: Vec<Vec<bool>> = (0..n).map(|x| (0..n).map(|y| x == y).collect()).collect();
        for &(x, y) in &self.retreats {
            let (x, y) = (x as usize, y as usize);
            if x < n && y < n && mutual.holds(x, y) {
                let from_y = reach[y].clone();
                for (r, &f) in reach[x].iter_mut().zip(&from_y) {
                    *r |= f;
                }
            }
        }
        (0..n)
            .filter(|&x| reach[v][x])
            .map(|x| self.pre_of(x))
            .fold(self.pre_of(v), u32::min)
    }

    /// Box invariant 1: the open list holds the finished vertices whose group has not come out
    /// yet; formally, exactly those, in the order they finished. F, above the guard, holds exactly
    /// the finished vertices whose group is not out, most recently finished on top.
    ///
    /// Lean: `FollowersInFinishOrder`.
    #[must_use]
    pub fn is_followers_in_finish_order(&self, g: &Digraph) -> bool {
        let mut want: Vec<u32> = self
            .finished
            .iter()
            .rev()
            .copied()
            .filter(|&v| !self.out(v as usize))
            .collect();
        want.push(g.n() as u32);
        self.stack.get(self.ftop..) == Some(&want[..])
    }

    /// Box invariant 2: each vertex's climb-back number is the earliest entry number it can get
    /// back to within its group; formally, along arrows the walk has already come back over. From
    /// its entry until its leader finishes, a vertex's `low`, its lead bit aside, is the least
    /// entry clock it reaches along a retreating path inside its component.
    ///
    /// Lean: `ClimbBackIsEarliest`.
    #[must_use]
    pub fn is_climb_back_is_earliest(&self, g: &Digraph) -> bool {
        let mutual = Mutual {
            reach: reachability(g),
        };
        (0..g.n()).all(|v| {
            self.pre_of(v) == 0
                || self.leader_out(g, &mutual, v)
                || self.low_of(v) >> 1 == self.climb_back(g, &mutual, v) >> 1
        })
    }

    /// Box invariant 3: every group that has come out is whole; formally, the vertices marked out
    /// are exactly the vertices in those groups. A vertex's `low` is
    /// `u32::MAX` exactly when the leader of its component has finished, which is exactly when
    /// its group is out; and each group out is a whole strong component.
    ///
    /// Lean: `DoneIffGroupOut`.
    #[must_use]
    pub fn is_done_iff_group_out(&self, g: &Digraph) -> bool {
        let mutual = Mutual {
            reach: reachability(g),
        };
        let marks = (0..g.n()).all(|v| {
            let leader = self.leader_out(g, &mutual, v);
            (self.low_of(v) == DONE) == leader && self.out(v) == leader
        });
        marks
            && self.groups().iter().all(|m| {
                m.iter().all(|&u| {
                    (0..g.n()).all(|x| m.contains(&(x as u32)) == mutual.holds(x, u as usize))
                })
            })
    }

    /// Lean `AlgorithmT.Valid`: [`Walk::is_followers_in_finish_order`],
    /// [`Walk::is_climb_back_is_earliest`] and [`Walk::is_done_iff_group_out`].
    #[must_use]
    pub fn is_valid(&self, g: &Digraph) -> bool {
        self.check_valid(g).is_ok()
    }

    /// [`Walk::is_valid`], naming the first piece that fails.
    ///
    /// # Errors
    ///
    /// `"invariant 1 (followers_in_finish_order)"`, `"invariant 2 (climb_back_is_earliest)"` or
    /// `"invariant 3 (done_iff_group_out)"`.
    pub fn check_valid(&self, g: &Digraph) -> Result<(), &'static str> {
        if !self.is_followers_in_finish_order(g) {
            return Err("invariant 1 (followers_in_finish_order)");
        }
        if !self.is_climb_back_is_earliest(g) {
            return Err("invariant 2 (climb_back_is_earliest)");
        }
        if !self.is_done_iff_group_out(g) {
            return Err("invariant 3 (done_iff_group_out)");
        }
        Ok(())
    }

    /// Every state of the walk on `g`, one per step: after each vertex is entered, each arrow is
    /// come back over and each root finishes. When coming back over an arrow stops the walk when
    /// done, that step's state is the walk's end (the path finished top down, F holding the guard
    /// alone). For tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn trace(g: &Digraph) -> Vec<Self> {
        #[derive(Default)]
        struct Record {
            pre: Vec<u32>,
            finished: Vec<u32>,
            retreats: Vec<(u32, u32)>,
            states: Vec<Walk>,
        }
        impl Watch for Record {
            fn enter(&mut self, v: usize, clock: u32) {
                self.pre[v] = clock;
            }
            fn finish(&mut self, v: usize) {
                self.finished.push(v as u32);
            }
            fn retreat(&mut self, v: usize, w: usize) {
                self.retreats.push((v as u32, w as u32));
            }
            fn step(&mut self, s: &Parts<'_>) {
                self.states.push(Walk {
                    low: s.low.to_vec(),
                    stack: s.stack.to_vec(),
                    ftop: s.ftop,
                    members: s.members.to_vec(),
                    offsets: s.offsets.to_vec(),
                    k: s.k,
                    pre: self.pre.clone(),
                    finished: self.finished.clone(),
                    retreats: self.retreats.clone(),
                });
            }
        }
        let mut record = Record {
            pre: vec![0; g.n()],
            ..Record::default()
        };
        let _ = algorithm_t(g, &mut record);
        record.states
    }

    /// A state from its stored parts, unchecked, for tests to judge states no
    /// walk reaches. Not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn from_parts(parts: WalkParts) -> Self {
        let WalkParts {
            low,
            stack,
            ftop,
            members,
            offsets,
            k,
            pre,
            finished,
            retreats,
        } = parts;
        Self {
            low,
            stack,
            ftop,
            members,
            offsets,
            k,
            pre,
            finished,
            retreats,
        }
    }

    /// The stored parts. For tests; not part of the API.
    #[cfg(any(test, feature = "unchecked"))]
    #[doc(hidden)]
    #[must_use]
    pub fn parts(&self) -> WalkParts {
        WalkParts {
            low: self.low.clone(),
            stack: self.stack.clone(),
            ftop: self.ftop,
            members: self.members.clone(),
            offsets: self.offsets.clone(),
            k: self.k,
            pre: self.pre.clone(),
            finished: self.finished.clone(),
            retreats: self.retreats.clone(),
        }
    }
}

/// A [`Walk`]'s stored parts, each as the field of the same name holds it. For tests; not part of
/// the API.
#[cfg(any(test, feature = "unchecked"))]
#[doc(hidden)]
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WalkParts {
    pub low: Vec<u32>,
    pub stack: Vec<u32>,
    pub ftop: usize,
    pub members: Vec<u32>,
    pub offsets: Vec<usize>,
    pub k: usize,
    pub pre: Vec<u32>,
    pub finished: Vec<u32>,
    pub retreats: Vec<(u32, u32)>,
}

/// The vertices in the order a depth-first walk on the forward rows finishes them: roots from 0
/// upward, a vertex marked when its frame is pushed.
fn finishing_order(g: &Digraph) -> Vec<u32> {
    let n = g.n();
    let (off, nb) = (&g.out.offsets, &g.out.neighbours);
    let mut entered = vec![false; n];
    let mut finished = Vec::with_capacity(n);
    // Each frame: the vertex and its next row position; at most n at once.
    let mut frames: Vec<(u32, usize)> = Vec::with_capacity(n);
    for root in 0..n {
        if entered[root] {
            continue;
        }
        entered[root] = true;
        frames.push((root as u32, off[root]));
        while let Some(top) = frames.last_mut() {
            let (v, next) = *top;
            if next == off[v as usize + 1] {
                frames.pop();
                finished.push(v);
                continue;
            }
            top.1 += 1;
            let w = nb[next] as usize;
            if !entered[w] {
                entered[w] = true;
                frames.push((w as u32, off[w]));
            }
        }
    }
    finished
}

/// Not in a group yet.
const UNSET: u32 = u32::MAX;

/// Kosaraju–Sharir: the strong components, ids in the order found (topological), members in the
/// order the second walk enters them. Linear in vertices plus arrows.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{kosaraju_sharir, Digraph};
///
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// let c = kosaraju_sharir(&g);
/// assert_eq!(c.group_of_each(), [0, 0, 1]);
/// // Members in the order the second walk enters them.
/// assert_eq!(c.group(0), [0, 1]);
/// ```
#[must_use]
pub fn kosaraju_sharir(g: &Digraph) -> Components {
    let n = g.n();
    let (off, nb) = (&g.into.offsets, &g.into.neighbours);
    let mut group_of = vec![UNSET; n];
    let mut members: Vec<u32> = Vec::with_capacity(n);
    let mut offsets = vec![0usize];
    let mut frames: Vec<(u32, usize)> = Vec::with_capacity(n);
    let mut c = 0u32;
    for root in finishing_order(g).into_iter().rev() {
        if group_of[root as usize] != UNSET {
            continue;
        }
        group_of[root as usize] = c;
        members.push(root);
        frames.push((root, off[root as usize]));
        while let Some(top) = frames.last_mut() {
            let (v, next) = *top;
            if next == off[v as usize + 1] {
                frames.pop();
                continue;
            }
            top.1 += 1;
            let w = nb[next] as usize;
            if group_of[w] == UNSET {
                group_of[w] = c;
                members.push(w as u32);
                frames.push((w as u32, off[w]));
            }
        }
        offsets.push(members.len());
        c += 1;
    }
    Components {
        group_of,
        offsets,
        members,
    }
}

/// The graph of groups (TZ §3.3): vertex `c` is group `c`, and there is one arrow c → d for each
/// pair of different groups some arrow of `g` joins, no loops. Groups are walked in id order,
/// each member's row in row order; an arrow is emitted unless its target group is marked, and the
/// marks a group set are cleared by walking the arrows it emitted. Arrow ids in emission order.
/// Linear in vertices plus arrows.
///
/// `comps` must be [`strong_components`] or [`kosaraju_sharir`] of `g`. Debug builds check as much
/// of that as one pass can: `comps` groups `g`'s vertices, and every arrow between two groups runs
/// from a smaller id to a larger, as both methods number them.
///
/// # Panics
///
/// In debug builds, if `comps` groups another number of vertices, or an arrow of `g` runs from a
/// larger group id to a smaller: then `comps` was computed on another graph. Release builds do not
/// check. In any build, if `comps` does not group the vertices of `g` (a vertex out of range of
/// its `group_of`).
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{condensation, strong_components, Digraph};
///
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2), (0, 2)]).unwrap();
/// let q = condensation(&g, &strong_components(&g));
/// // Two groups, and one arrow between them for the two arrows of g.
/// assert_eq!((q.n(), q.arrow_count()), (2, 1));
/// assert_eq!(q.arrow(0), (0, 1));
/// ```
#[must_use]
pub fn condensation(g: &Digraph, comps: &Components) -> Digraph {
    debug_assert!(
        comps.group_of.len() == g.n(),
        "the groups cover {} vertices, the graph has {}: they are another graph's",
        comps.group_of.len(),
        g.n()
    );
    let q = condense(g, comps);
    #[cfg(debug_assertions)]
    if let Some((c, d)) = (0..q.arrow_count())
        .map(|i| q.arrow(i))
        .find(|&(c, d)| c > d)
    {
        panic!("an arrow from group {c} to group {d}: the groups are another graph's");
    }
    q
}

/// [`condensation`] with any numbering of the groups.
fn condense(g: &Digraph, comps: &Components) -> Digraph {
    let k = comps.count();
    let (off, nb) = (&g.out.offsets, &g.out.neighbours);
    let mut marked = vec![false; k];
    let mut arrows: Vec<(u32, u32)> = Vec::new();
    for c in 0..k {
        let first = arrows.len();
        for &v in comps.group(c) {
            let v = v as usize;
            for &w in &nb[off[v]..off[v + 1]] {
                let d = comps.group_of[w as usize];
                if d as usize != c && !marked[d as usize] {
                    marked[d as usize] = true;
                    arrows.push((c as u32, d));
                }
            }
        }
        for &(_, d) in &arrows[first..] {
            marked[d as usize] = false;
        }
    }
    Digraph::new(k, &arrows).expect("at most n groups and one arrow per arrow of g")
}

/// Why a grouping is not the strong components; the first check it fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentsError {
    /// Not a group for every vertex with ids `0..k`, each id used.
    Partition,
    /// Some member of this group (the first such group in id order) is not reached from its
    /// smallest vertex, or does not reach it, inside the group.
    NotStronglyConnected {
        /// The group's id.
        group: u32,
    },
    /// The graph of groups, derived from the arrows, has a cycle: some groups should be one.
    Cyclic,
}

impl fmt::Display for ComponentsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Partition => write!(f, "not a partition of the vertices with ids 0..k"),
            Self::NotStronglyConnected { group } => {
                write!(f, "group {group} is not strongly connected")
            }
            Self::Cyclic => write!(f, "the graph of groups has a cycle"),
        }
    }
}

impl std::error::Error for ComponentsError {}

/// Whether a search from the first of `members` along the rows `(off, nb)`, staying inside their
/// group, reaches every one of them. `seen` holds `stamp` for vertices already reached.
fn reaches_all(
    (off, nb): (&[usize], &[u32]),
    group_of: &[u32],
    members: &[u32],
    seen: &mut [u32],
    stamp: u32,
    stack: &mut Vec<u32>,
) -> bool {
    let start = members[0];
    let c = group_of[start as usize];
    seen[start as usize] = stamp;
    stack.push(start);
    let mut reached = 1;
    while let Some(v) = stack.pop() {
        let v = v as usize;
        for &w in &nb[off[v]..off[v + 1]] {
            let i = w as usize;
            if group_of[i] == c && seen[i] != stamp {
                seen[i] = stamp;
                reached += 1;
                stack.push(w);
            }
        }
    }
    reached == members.len()
}

/// Checks that `group_of` is the strong components of `g`, numbered in any order: (1) every vertex
/// has a group, ids `0..k` each used; (2) each group is strongly connected: from its smallest
/// vertex a forward search and a backward search, both staying inside the group, reach every
/// member; (3) the graph of groups derived from `g`'s arrows has no cycle. The ids need not be
/// topological. Linear in vertices plus arrows.
///
/// # Errors
///
/// The first check that fails, in the order above; for (2), the first group in id order.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{check_components, ComponentsError, Digraph};
///
/// let g = Digraph::new(3, &[(0, 1), (1, 0), (1, 2)]).unwrap();
/// // Any numbering of the true groups passes.
/// assert_eq!(check_components(&g, &[1, 1, 0]), Ok(()));
/// // 1 and 2 do not reach each other both ways.
/// assert_eq!(
///     check_components(&g, &[0, 1, 1]),
///     Err(ComponentsError::NotStronglyConnected { group: 1 })
/// );
/// ```
pub fn check_components(g: &Digraph, group_of: &[u32]) -> Result<(), ComponentsError> {
    let n = g.n();
    // An id at or past n leaves some id below it unused; refused before anything is sized by it.
    if group_of.len() != n || group_of.iter().any(|&c| c as usize >= n) {
        return Err(ComponentsError::Partition);
    }
    let k = group_of.iter().max().map_or(0, |&c| c as usize + 1);
    let mut used = vec![false; k];
    for &c in group_of {
        used[c as usize] = true;
    }
    if used.contains(&false) {
        return Err(ComponentsError::Partition);
    }
    let comps = Components::from_group_of(group_of.to_vec(), k);
    let out = (&g.out.offsets[..], &g.out.neighbours[..]);
    let into = (&g.into.offsets[..], &g.into.neighbours[..]);
    // Stamp 2c + 1 for group c's forward search, 2c + 2 for its backward one.
    let mut seen = vec![0u32; n];
    let mut stack = Vec::new();
    for c in 0..k {
        let group = comps.group(c);
        let stamp = 2 * c as u32 + 1;
        if !reaches_all(out, group_of, group, &mut seen, stamp, &mut stack)
            || !reaches_all(into, group_of, group, &mut seen, stamp + 1, &mut stack)
        {
            return Err(ComponentsError::NotStronglyConnected { group: c as u32 });
        }
    }
    if topological_order(&condense(g, &comps)).is_err() {
        return Err(ComponentsError::Cyclic);
    }
    Ok(())
}

#[cfg(test)]
#[path = "unit_tests/scc.rs"]
mod tests;
