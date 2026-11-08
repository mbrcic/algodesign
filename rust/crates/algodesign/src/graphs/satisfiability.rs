// SPDX-License-Identifier: Apache-2.0
//! 2-SAT: give each variable true or false so that every clause (a ∨ b) holds, or show that no
//! choice can.
//!
//! The method is Aspvall, Plass and Tarjan's (1979, p. 122). Literal `2i` is xᵢ and `2i + 1` is
//! ¬xᵢ, so `a ^ 1` negates `a`. A clause (a ∨ b) gives two arrows, "if this is false, that must be
//! true": `a ^ 1 → b` and `b ^ 1 → a`. A clause (x ∨ x) gives two copies of one arrow, and (x ∨ ¬x)
//! two loops. The formula has no answer exactly when some xᵢ and ¬xᵢ are in one strong component;
//! otherwise xᵢ is true when its group comes after ¬xᵢ's in topological order (cp-algorithms'
//! parity), that is `group_of[2i] > group_of[2i + 1]` with the ids of [`strong_components`].
//!
//! Lean counterpart: `AlgoDesign.Graphs.TwoSat`.

use std::fmt;

use super::digraph::Digraph;
use super::scc::strong_components;

/// Why [`two_sat`] gave no assignment: no assignment exists, or the input was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TwoSatError {
    /// No assignment satisfies every clause: xᵢ and ¬xᵢ, for i = `var` (the smallest such), are in
    /// one group, so each implies the other.
    Unsat {
        /// The variable.
        var: u32,
    },
    /// A clause names a literal not below `2 · n_vars`; the first such one is reported.
    LiteralOutOfRange {
        /// The clause's position in the input.
        clause: usize,
        /// The literal.
        literal: u32,
        /// The number of variables.
        n_vars: usize,
    },
    /// `2 · n_vars` literals is 2³¹ or more, past the graph's limit on vertices.
    TooManyVariables {
        /// The number of variables asked for.
        n_vars: usize,
    },
    /// Two arrows per clause would pass `u32::MAX` arrows.
    TooManyClauses {
        /// The number of clauses given.
        count: usize,
    },
}

impl fmt::Display for TwoSatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsat { var } => {
                write!(f, "unsatisfiable: x{var} and its negation imply each other")
            }
            Self::LiteralOutOfRange {
                clause,
                literal,
                n_vars,
            } => write!(
                f,
                "clause {clause} names literal {literal}, out of range 0..{}",
                2 * n_vars
            ),
            Self::TooManyVariables { n_vars } => {
                write!(f, "{n_vars} variables: at most 2^30 - 1 allowed")
            }
            Self::TooManyClauses { count } => {
                write!(f, "{count} clauses: at most u32::MAX / 2 allowed")
            }
        }
    }
}

impl std::error::Error for TwoSatError {}

/// A value for each variable that makes every clause `(a, b)` true, literal `2i` being xᵢ and
/// `2i + 1` being ¬xᵢ. Linear in variables plus clauses.
///
/// # Errors
///
/// [`TwoSatError::Unsat`] when no assignment exists; [`TwoSatError::TooManyVariables`] if
/// `2 · n_vars >= 2³¹`, [`TwoSatError::TooManyClauses`] if `2 · clauses > u32::MAX`, and
/// [`TwoSatError::LiteralOutOfRange`] for the first clause with a literal not below `2 · n_vars`,
/// checked in that order before anything is built.
///
/// # Examples
///
/// ```
/// use algodesign::graphs::{two_sat, TwoSatError};
///
/// // Literal 2i is x_i, 2i + 1 its negation. (x0 or x1) and (not x0 or x1) and (not x1 or not x1):
/// let clauses = [(0, 2), (1, 2), (3, 3)];
/// assert_eq!(two_sat(2, &clauses), Err(TwoSatError::Unsat { var: 0 }));
/// // (x0 or x1) and (not x0 or not x1): exactly one is true.
/// let a = two_sat(2, &[(0, 2), (1, 3)]).unwrap();
/// assert!(a[0] != a[1]);
/// ```
pub fn two_sat(n_vars: usize, clauses: &[(u32, u32)]) -> Result<Vec<bool>, TwoSatError> {
    let n = match n_vars.checked_mul(2) {
        Some(n) if n < 1 << 31 => n,
        _ => return Err(TwoSatError::TooManyVariables { n_vars }),
    };
    if clauses.len() > u32::MAX as usize / 2 {
        return Err(TwoSatError::TooManyClauses {
            count: clauses.len(),
        });
    }
    for (clause, &(a, b)) in clauses.iter().enumerate() {
        for literal in [a, b] {
            if literal as usize >= n {
                return Err(TwoSatError::LiteralOutOfRange {
                    clause,
                    literal,
                    n_vars,
                });
            }
        }
    }
    let arrows: Vec<(u32, u32)> = clauses
        .iter()
        .flat_map(|&(a, b)| [(a ^ 1, b), (b ^ 1, a)])
        .collect();
    let g = Digraph::new(n, &arrows).expect("sizes and literals checked above");
    let comps = strong_components(&g);
    let pairs = comps.group_of_each().chunks_exact(2);
    if let Some(var) = pairs.clone().position(|p| p[0] == p[1]) {
        return Err(TwoSatError::Unsat { var: var as u32 });
    }
    Ok(pairs.map(|p| p[0] > p[1]).collect())
}

#[cfg(test)]
#[path = "unit_tests/satisfiability.rs"]
mod tests;
