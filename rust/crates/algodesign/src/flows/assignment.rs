// SPDX-License-Identifier: Apache-2.0
//! The assignment: every person one object, every object one person, at the least total cost, with
//! a label on every person and every object that proves no assignment costs less.
//!
//! The table is square, row `i` for person `i` and column `j` for object `j`. The people are placed
//! one at a time, in row order, with every label zero at the start. Placing person `i` is one
//! best-first search over the objects on changed costs, the cost of a pair minus the label of its
//! person minus the label of its object, with the labels as they stand when the search starts. An
//! array holds each object's distance from person `i`, the cheapest changed cost of a path to it
//! through the people reached so far, and the object it came through. Each pick takes the unsettled
//! object with the smallest distance: on a tie a free object first, then the lowest index. If the
//! picked object is free, the search stops; otherwise the person holding it is reached, and their
//! row may lower the distances (only a strict drop changes a distance and the object it came
//! through); that pass also finds the next pick. Then the labels move once, as the cheapest flow's
//! heights: with `top` the free object's distance, person `i` gains `top`, and every settled object
//! `k` loses `top - distance[k]` while its holder gains it. Then the people along the path move one
//! object on, and person `i` takes the path's first object.
//!
//! This is shortest augmenting paths with heights, one person at a time: Ahuja, Magnanti and Orlin,
//! *Network Flows* (1993), §12.4, p. 471; the cheapest flow on the matching network, its heights
//! read as labels on both sides (Kuhn, "The Hungarian method for the assignment problem", 1955, is
//! where the family starts). The labels fit every pair, `person_label[i] + object_label[j] <=
//! cost[i][j]`, and meet every chosen pair exactly, so the labels add up to the answer's cost and
//! every assignment costs at least that. Read as prices, `-object_label[j]`, every person's object
//! is their favorite after price.
//!
//! Cost: one search per person, each of at most `n` picks, each pick one `O(n)` pass; `O(n³)` on a
//! full table of `n` people.
//!
//! Costs may be below zero. [`assignment_f64`] runs the same procedure on decimals; its labels fit
//! and meet the chosen pairs to within the tolerance its documentation states. The steps (the
//! objects each search settled, the path, the labels after it) are recorded only in test builds
//! and under the `unchecked` feature (`assignment_with_steps`).
//!
//! This module has no `check_valid`. The Lean `Valid`, `CheapestForThesePeople` and
//! `LabelsFitAndExact`, is checked in its tests on the state after every person: the labels fit
//! every pair of the people placed so far and are exact on their chosen pairs, which makes those
//! people's objects the cheapest for them.
//!
//! **Against the Python, and how fast.** The same procedure and ties. The search's arrays are
//! allocated once and kept from person to person; one pass over a reached person's row both lowers
//! the distances and finds the next pick; and the path is walked back through the array without
//! building a list outside the trace. The Python picks with `min` and builds the path and moves the
//! people along it.
//!
//! Lean counterpart: `AlgoDesign.Flows.Assignment`, the contract in `Flows/Assignment/Spec.lean`.

use std::ops::{Add, AddAssign, Sub, SubAssign};

use super::network::FlowsError;

/// Marks an object with no holder, or a path's first object (reached from the new person).
const NONE: usize = usize::MAX;

/// The answer: every person's object, the labels, and the total cost.
///
/// Lean: `Assignment.Answer`, with the total cost beside it.
#[derive(Debug, Clone, PartialEq)]
pub struct Assignment<T = i64> {
    /// Person `i` gets object `obj[i]`; every object goes to one person.
    pub obj: Vec<usize>,
    /// The label of every person.
    pub person_label: Vec<T>,
    /// The label of every object; the negative of each is the object's price.
    pub object_label: Vec<T>,
    /// The total cost: each person's cost for their object, summed. It equals the labels' sum.
    pub cost: T,
}

/// One person's step: the objects their search settled, the path, and the labels after it. Only
/// test builds and the `unchecked` feature record steps (`assignment_with_steps`).
///
/// Lean: `Ops.after`, the state after each person.
#[derive(Debug, Clone, PartialEq)]
pub struct AssignmentStep<T = i64> {
    /// The objects the search picked, in order; the last is the free one.
    pub settled: Vec<usize>,
    /// The path's objects: the one the new person takes first, the free one last; the holder of
    /// each earlier object moves to the next.
    pub path: Vec<usize>,
    /// The label of every person after the step.
    pub person_label: Vec<T>,
    /// The label of every object after the step.
    pub object_label: Vec<T>,
}

/// A least-cost assignment of the square table `cost`, row `i` for person `i`, with a label on
/// every person and every object: on every pair the two labels add up to at most its cost,
/// and on every chosen pair exactly to it. `O(n³)` for `n` people.
///
/// The box's Assumes, as many objects as people, is checked here, on the caller's input. The sums
/// are not saturated: the input range is tables whose labels, distances and total cost fit an
/// `i64`. A person's label is zero until their search and then stays between the smallest and the
/// largest cost; an object's label stays between minus the spread of the costs and zero (argued:
/// an object's label only drops, and a free object keeps its label zero, which every placed
/// person's label fits). So with `m` the largest magnitude of a cost, every label is at most `2m`
/// in magnitude, every changed cost at most `4m`, and every distance the search holds at most `9m`
/// (a picked distance is at least the smallest changed cost and at most the free object's, which is
/// a person's label; an unpicked one is a picked one plus one changed cost); costs of magnitude at
/// most `i64::MAX / (16n)` are inside the range.
///
/// Lean: `Assignment.contract`.
///
/// # Errors
///
/// [`FlowsError::NotSquare`] for the first row whose length is not the number of rows.
///
/// # Examples
///
/// ```
/// use algodesign::flows::assignment;
///
/// let cost = vec![vec![1, 3, 6], vec![2, 8, 9], vec![5, 4, 9]];
/// let answer = assignment(&cost).unwrap();
/// assert_eq!(answer.obj, [2, 0, 1]);
/// assert_eq!(answer.cost, 12);
/// // The labels add up to the cost, so no assignment costs less.
/// let labels: i64 = answer.person_label.iter().chain(&answer.object_label).sum();
/// assert_eq!(labels, 12);
/// ```
pub fn assignment(cost: &[Vec<i64>]) -> Result<Assignment, FlowsError> {
    refuse_shape(cost)?;
    Ok(run(cost, None))
}

/// [`assignment`] on decimal costs: the same procedure, ties included, in `f64`.
///
/// The input range is costs of magnitude at most `f64::MAX / (16n)` for `n` people, the bound of
/// [`assignment`] with `f64::MAX` for `i64::MAX`; a larger cost is refused. Within it every label,
/// changed cost and distance stays below `9m` in magnitude, `m` the largest magnitude of a cost,
/// as [`assignment`] argues, so every sum the search forms, `9m + 4m` at most, stays below
/// `f64::MAX`; the total cost and the labels' sum, `n` costs and `2n` labels, stay below
/// `4 n m <= f64::MAX / 4`. So nothing overflows to infinity, and no difference of two infinities
/// makes a label not a number.
///
/// Rounding: each distance is a chain of at most `2n` additions, and each label moves once per
/// person by a difference of two distances, every number below `9m` in magnitude. So the labels
/// fit every pair, and meet every chosen pair, to within the tolerance
/// `36 · n² · f64::EPSILON · (1 + m)` (argued), and the total cost is the labels' sum to within `n`
/// times that.
///
/// # Errors
///
/// [`FlowsError::NotSquare`] for the first row whose length is not the number of rows; then, for
/// the first cost in row order that is refused, [`FlowsError::CostNotFinite`] when it is infinite
/// or not a number, and [`FlowsError::CostTooLarge`] when its magnitude is above
/// `f64::MAX / (16n)`.
///
/// # Examples
///
/// ```
/// use algodesign::flows::assignment_f64;
///
/// let cost = vec![vec![0.5, 2.0], vec![1.0, 4.25]];
/// let answer = assignment_f64(&cost).unwrap();
/// assert_eq!(answer.obj, [1, 0]);
/// assert_eq!(answer.cost, 3.0);
/// ```
pub fn assignment_f64(cost: &[Vec<f64>]) -> Result<Assignment<f64>, FlowsError> {
    refuse_shape(cost)?;
    let largest = f64::MAX / (16.0 * cost.len() as f64);
    for (person, row) in cost.iter().enumerate() {
        for (object, c) in row.iter().enumerate() {
            if !c.is_finite() {
                return Err(FlowsError::CostNotFinite { person, object });
            }
            if c.abs() > largest {
                return Err(FlowsError::CostTooLarge { person, object });
            }
        }
    }
    let answer = run(cost, None);
    debug_assert!(
        answer.cost.is_finite()
            && answer.person_label.iter().all(|x| x.is_finite())
            && answer.object_label.iter().all(|x| x.is_finite()),
        "a label or the total cost overflowed inside the stated range"
    );
    Ok(answer)
}

/// [`assignment`], with every person's step: the objects the search settled in order, the path,
/// and the labels after it. Only in test builds and under the `unchecked` feature.
///
/// Lean: `Ops.after`, `Ops.walks`.
///
/// # Errors
///
/// As [`assignment`].
#[cfg(any(test, feature = "unchecked"))]
pub fn assignment_with_steps(
    cost: &[Vec<i64>],
) -> Result<(Assignment, Vec<AssignmentStep>), FlowsError> {
    refuse_shape(cost)?;
    let mut steps = Vec::new();
    let answer = run(cost, Some(&mut steps));
    Ok((answer, steps))
}

/// The shape [`assignment`] refuses: a row whose length is not the number of rows.
fn refuse_shape<T>(cost: &[Vec<T>]) -> Result<(), FlowsError> {
    let people = cost.len();
    match cost.iter().position(|row| row.len() != people) {
        Some(row) => Err(FlowsError::NotSquare {
            row,
            length: cost[row].len(),
            people,
        }),
        None => Ok(()),
    }
}

/// The people placed one at a time on the square table `cost`, recording each step into `steps`
/// when it is given (test builds and the `unchecked` feature only).
#[cfg_attr(
    not(any(test, feature = "unchecked")),
    allow(unused_variables, unused_mut)
)]
fn run<T>(cost: &[Vec<T>], mut steps: Option<&mut Vec<AssignmentStep<T>>>) -> Assignment<T>
where
    T: Copy + Default + PartialOrd + Add<Output = T> + Sub<Output = T> + AddAssign + SubAssign,
{
    let n = cost.len();
    let mut u = vec![T::default(); n];
    let mut v = vec![T::default(); n];
    // Each person's object, and each object's holder (NONE while free).
    let mut obj = vec![NONE; n];
    let mut holder = vec![NONE; n];
    // The search's arrays: each object's distance from the new person on the labels as they stood
    // when the search began, the object before it on its path (NONE: reached from the new person),
    // whether it is settled; the objects settled, in order.
    let mut dist = vec![T::default(); n];
    let mut came_from = vec![NONE; n];
    let mut settled = vec![false; n];
    let mut order: Vec<usize> = Vec::with_capacity(n);
    for i in 0..n {
        order.clear();
        settled.fill(false);
        came_from.fill(NONE);
        let ui = u[i];
        for ((d, &c), &vj) in dist.iter_mut().zip(&cost[i]).zip(&v) {
            *d = c - ui - vj;
        }
        let mut pick = first_pick(&dist, &holder);
        let free = loop {
            settled[pick] = true;
            order.push(pick);
            let r = holder[pick];
            if r == NONE {
                break pick;
            }
            // One pass over the reached person's row: lower the distances, and find the next
            // pick, the unsettled object with the smallest distance, a free one first, then the
            // lowest index.
            let base = dist[pick] - u[r];
            let mut next = NONE;
            for (j, &c) in cost[r].iter().enumerate() {
                if settled[j] {
                    continue;
                }
                let through = base + c - v[j];
                if through < dist[j] {
                    dist[j] = through;
                    came_from[j] = pick;
                }
                if next == NONE || before(&dist, &holder, j, next) {
                    next = j;
                }
            }
            pick = next;
        };
        // The labels move once, as the cheapest flow's heights: by the free object's distance
        // less each settled object's.
        let top = dist[free];
        u[i] += top;
        for &k in &order {
            let shift = top - dist[k];
            v[k] -= shift;
            let r = holder[k];
            if r != NONE {
                u[r] += shift;
            }
        }
        // Walk back from the free object: each object goes to the holder of the one before it,
        // the first to person i.
        let mut j = free;
        loop {
            let before = came_from[j];
            let p = if before == NONE { i } else { holder[before] };
            holder[j] = p;
            obj[p] = j;
            if before == NONE {
                break;
            }
            j = before;
        }
        watched!(if let Some(steps) = steps.as_deref_mut() {
            steps.push(AssignmentStep {
                settled: order.clone(),
                path: path_back(&came_from, free),
                person_label: u.clone(),
                object_label: v.clone(),
            });
        });
    }
    let mut total = T::default();
    for (p, &j) in obj.iter().enumerate() {
        total += cost[p][j];
    }
    Assignment {
        obj,
        person_label: u,
        object_label: v,
        cost: total,
    }
}

/// Whether object `j` comes before object `k` in the search's order: the smaller distance, then a
/// free object, then the lower index (`k`'s index is the higher when the two only tie).
fn before<T: PartialOrd>(dist: &[T], holder: &[usize], j: usize, k: usize) -> bool {
    dist[j] < dist[k] || (dist[j] == dist[k] && holder[j] == NONE && holder[k] != NONE)
}

/// The search's first pick: the object with the smallest distance, a free one first, then the
/// lowest index.
fn first_pick<T: PartialOrd>(dist: &[T], holder: &[usize]) -> usize {
    let mut pick = 0;
    for j in 1..dist.len() {
        if before(dist, holder, j, pick) {
            pick = j;
        }
    }
    pick
}

/// The path's objects, from the one the new person takes to `free`.
#[cfg(any(test, feature = "unchecked"))]
fn path_back(came_from: &[usize], free: usize) -> Vec<usize> {
    let mut path = vec![free];
    let mut j = free;
    while came_from[j] != NONE {
        j = came_from[j];
        path.push(j);
    }
    path.reverse();
    path
}

#[cfg(test)]
#[path = "unit_tests/assignment.rs"]
mod tests;
