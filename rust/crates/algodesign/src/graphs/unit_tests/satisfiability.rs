use super::*;
use crate::graphs::naive;
use proptest::prelude::*;

/// Literal xᵢ.
fn x(i: u32) -> u32 {
    2 * i
}

/// Literal ¬xᵢ.
fn not(i: u32) -> u32 {
    2 * i + 1
}

#[test]
fn a_clause_with_one_literal_twice_forces_it() {
    // (x₀ ∨ x₀): two copies of ¬x₀ → x₀.
    assert_eq!(two_sat(1, &[(x(0), x(0))]), Ok(vec![true]));
    assert_eq!(two_sat(1, &[(not(0), not(0))]), Ok(vec![false]));
}

#[test]
fn a_clause_with_a_literal_and_its_negation_is_two_loops() {
    // (x₀ ∨ ¬x₀) holds either way; x₀ and ¬x₀ are separate groups of one, ids 1 and 0.
    assert_eq!(two_sat(1, &[(x(0), not(0))]), Ok(vec![true]));
}

#[test]
fn an_unsatisfiable_formula_names_its_smallest_witness() {
    // x₀ free; x₁ forced both ways: (x₁ ∨ x₁), (¬x₁ ∨ ¬x₁); x₂ the same.
    let clauses = [
        (x(0), not(0)),
        (x(2), x(2)),
        (not(2), not(2)),
        (x(1), x(1)),
        (not(1), not(1)),
    ];
    assert_eq!(two_sat(3, &clauses), Err(TwoSatError::Unsat { var: 1 }));
    assert_eq!(naive::two_sat(3, &clauses), None);
}

#[test]
fn no_variables_and_no_clauses() {
    assert_eq!(two_sat(0, &[]), Ok(vec![]));
    // Every variable free: each literal is its own group, and xᵢ's comes out before ¬xᵢ's, so
    // its id is the larger and xᵢ is true.
    assert_eq!(two_sat(3, &[]), Ok(vec![true; 3]));
}

#[test]
fn the_input_is_checked_before_anything_is_built() {
    assert_eq!(
        two_sat(2, &[(x(0), x(1)), (not(1), 4)]),
        Err(TwoSatError::LiteralOutOfRange {
            clause: 1,
            literal: 4,
            n_vars: 2
        })
    );
    assert_eq!(
        two_sat(0, &[(0, 0)]),
        Err(TwoSatError::LiteralOutOfRange {
            clause: 0,
            literal: 0,
            n_vars: 0
        })
    );
    assert_eq!(
        two_sat(1 << 30, &[]),
        Err(TwoSatError::TooManyVariables { n_vars: 1 << 30 })
    );
    assert_eq!(
        two_sat(usize::MAX, &[]),
        Err(TwoSatError::TooManyVariables { n_vars: usize::MAX })
    );
}

/// The answer agrees with brute force: an assignment exactly when one exists, and it satisfies
/// every clause; when there is none, the named variable and its negation are in one group, and
/// no smaller one is.
fn as_brute_force(n_vars: usize, clauses: &[(u32, u32)]) -> Result<(), TestCaseError> {
    match two_sat(n_vars, clauses) {
        Ok(values) => {
            prop_assert_eq!(values.len(), n_vars);
            prop_assert!(naive::satisfies(&values, clauses));
        }
        Err(TwoSatError::Unsat { var }) => {
            prop_assert_eq!(naive::two_sat(n_vars, clauses), None);
            let arrows: Vec<(u32, u32)> = clauses
                .iter()
                .flat_map(|&(a, b)| [(a ^ 1, b), (b ^ 1, a)])
                .collect();
            let groups = naive::mutual_groups(2 * n_vars, &arrows);
            let first = (0..n_vars).position(|i| groups[2 * i] == groups[2 * i + 1]);
            prop_assert_eq!(first, Some(var as usize));
        }
        Err(e) => prop_assert!(false, "unexpected {e}"),
    }
    Ok(())
}

#[test]
fn every_formula_with_up_to_two_variables_and_three_clauses() {
    for n_vars in 1..=2usize {
        let literals = 2 * n_vars as u32;
        let clauses = literals * literals;
        for len in 0..=3u32 {
            // Formula number f, read in base `clauses`, picks each clause.
            for f in 0..clauses.pow(len) {
                let formula: Vec<(u32, u32)> = (0..len)
                    .map(|j| {
                        let c = f / clauses.pow(j) % clauses;
                        (c / literals, c % literals)
                    })
                    .collect();
                as_brute_force(n_vars, &formula).unwrap();
            }
        }
    }
}

proptest! {
    #[test]
    fn on_any_small_formula_the_answer_agrees_with_brute_force(
        (n_vars, clauses) in (1usize..=4).prop_flat_map(|n| {
            let l = 2 * n as u32;
            (Just(n), prop::collection::vec((0..l, 0..l), 0..10))
        })
    ) {
        as_brute_force(n_vars, &clauses)?;
    }
}
