use super::*;
use crate::flows::naive;
use crate::rng::SplitMix64;
use proptest::prelude::*;

/// Whether the labels fit every pair of the people `0..people` and meet every chosen pair of them
/// exactly; the first that fails, in words.
fn labels_fit_and_exact(
    cost: &[Vec<i64>],
    people: usize,
    obj: &[usize],
    u: &[i64],
    v: &[i64],
) -> Result<(), String> {
    for i in 0..people {
        for (j, &c) in cost[i].iter().enumerate() {
            if u[i] + v[j] > c {
                return Err(format!(
                    "LabelsFit: {} + {} > {c} at ({i}, {j})",
                    u[i], v[j]
                ));
            }
        }
        if u[i] + v[obj[i]] != cost[i][obj[i]] {
            return Err(format!("ExactOnChosen at ({i}, {})", obj[i]));
        }
    }
    Ok(())
}

/// Whether `answer` and `steps` meet the contract on `cost`; the first thing that fails, in words.
/// With `oracle`, the cost is also the smallest found by trying every order of the objects.
fn meets_the_contract(
    cost: &[Vec<i64>],
    answer: &Assignment,
    steps: &[AssignmentStep],
    oracle: bool,
) -> Result<(), String> {
    let n = cost.len();
    let (obj, u, v) = (&answer.obj, &answer.person_label, &answer.object_label);
    if obj.len() != n || u.len() != n || v.len() != n {
        return Err("WellFormed".into());
    }
    // Lean: IsAssignmentOf
    let mut taken = vec![false; n];
    for &j in obj {
        if j >= n || taken[j] {
            return Err(format!("{obj:?} is no assignment"));
        }
        taken[j] = true;
    }
    if answer.cost != (0..n).map(|i| cost[i][obj[i]]).sum::<i64>() {
        return Err(format!("cost {} is not the assignment's", answer.cost));
    }
    // Lean: Ops.LabelsFit, Ops.ExactOnChosen
    labels_fit_and_exact(cost, n, obj, u, v)?;
    // Adding the labels up proves that no assignment costs less.
    if u.iter().chain(v).sum::<i64>() != answer.cost {
        return Err("the labels do not add up to the cost".into());
    }
    // Lean: Ops.FavoriteAfterPrice
    for i in 0..n {
        for j in 0..n {
            if cost[i][obj[i]] - v[obj[i]] > cost[i][j] - v[j] {
                return Err(format!("person {i} prefers object {j} after price"));
            }
        }
    }
    // Lean: Ops.OneSearchPerPerson, Ops.stepsKeep, Ops.walks
    if steps.len() != n {
        return Err(format!("{} steps for {n} people", steps.len()));
    }
    let mut placed = vec![NONE; n];
    let mut holder = vec![NONE; n];
    for (k, step) in steps.iter().enumerate() {
        let path = &step.path;
        let free = *path.last().ok_or(format!("step {k}: an empty path"))?;
        if step.settled.last() != Some(&free) || holder[free] != NONE {
            return Err(format!(
                "step {k}: the search does not end at a free object"
            ));
        }
        if path.iter().any(|j| !step.settled.contains(j)) {
            return Err(format!("step {k}: the path leaves the settled objects"));
        }
        let movers: Vec<usize> = std::iter::once(k)
            .chain(path[..path.len() - 1].iter().map(|&j| holder[j]))
            .collect();
        for (&p, &j) in movers.iter().zip(path) {
            placed[p] = j;
            holder[j] = p;
        }
        labels_fit_and_exact(cost, k + 1, &placed, &step.person_label, &step.object_label)
            .map_err(|e| format!("step {k}: {e}"))?;
    }
    let last = steps.last();
    if n > 0 && (placed != *obj || last.map(|s| (&s.person_label, &s.object_label)) != Some((u, v)))
    {
        return Err("the steps do not lead to the answer".into());
    }
    // Lean: Ops.LeastCost
    if oracle && naive::cheapest_assignment(cost) != answer.cost {
        return Err("a cheaper assignment exists".into());
    }
    Ok(())
}

/// The answer and steps for `cost`, checked against the contract.
fn checked(cost: &[Vec<i64>], oracle: bool) -> (Assignment, Vec<AssignmentStep>) {
    let (answer, steps) = assignment_with_steps(cost).unwrap();
    assert_eq!(meets_the_contract(cost, &answer, &steps, oracle), Ok(()));
    assert_eq!(assignment(cost).unwrap(), answer);
    (answer, steps)
}

#[test]
fn the_three_by_three_table_costs_twelve_and_its_labels_prove_it() {
    // P1 (1, 3, 6), P2 (2, 8, 9), P3 (5, 4, 9).
    let cost = vec![vec![1, 3, 6], vec![2, 8, 9], vec![5, 4, 9]];
    let (answer, steps) = checked(&cost, true);
    assert_eq!(answer.obj, [2, 0, 1]);
    assert_eq!(answer.cost, 12);
    // By hand, u = (6, 7, 7), v = (-5, -3, 0). Row P1: 6 - 5 = 1 <= 1, 6 - 3 = 3 <= 3,
    // 6 + 0 = 6 <= 6, exact on its object 3. Row P2: 7 - 5 = 2 <= 2, exact on object 1;
    // 4 <= 8, 7 <= 9. Row P3: 2 <= 5, 7 - 3 = 4 <= 4, exact on object 2; 7 <= 9. The labels
    // add up to 6 + 7 + 7 - 5 - 3 + 0 = 12, the cost, so no assignment costs less.
    assert_eq!(answer.person_label, [6, 7, 7]);
    assert_eq!(answer.object_label, [-5, -3, 0]);
    // P1 takes object 1 (cost 1); P2 also wants it, and P1 moves to object 2; P3 wants object 2,
    // then 1, then reaches the free object 3 through P1's row, and P1 moves there.
    let settled: Vec<&[usize]> = steps.iter().map(|s| &s.settled[..]).collect();
    let paths: Vec<&[usize]> = steps.iter().map(|s| &s.path[..]).collect();
    assert_eq!(settled, [&[0][..], &[0, 1], &[1, 0, 2]]);
    assert_eq!(paths, [&[0][..], &[0, 1], &[1, 2]]);
    assert_eq!(
        (&steps[1].person_label, &steps[1].object_label),
        (&vec![3, 4, 0], &vec![-2, 0, 0])
    );
}

#[test]
fn the_rent_gives_every_tenant_their_favorite_room_after_price() {
    // Values, larger is better; costs are 900 - value. Rows: Juan, Anita, Daniel, Tomás.
    let values = [
        [550, 400, 700, 350],
        [700, 650, 400, 250],
        [900, 550, 300, 250],
        [650, 700, 400, 250],
    ];
    let cost: Vec<Vec<i64>> = values
        .iter()
        .map(|row| row.iter().map(|&x| 900 - x).collect())
        .collect();
    let (answer, steps) = checked(&cost, true);
    // Juan room 3, Anita room 4, Daniel room 1, Tomás room 2.
    assert_eq!(answer.obj, [2, 3, 0, 1]);
    let value: i64 = (0..4).map(|i| values[i][answer.obj[i]]).sum();
    assert_eq!(value, 2_550);
    assert_eq!(answer.cost, 4 * 900 - 2_550);
    assert_eq!(answer.person_label, [350, 650, 450, 600]);
    assert_eq!(answer.object_label, [-450, -400, -150, 0]);
    // Prices are minus the room labels, 450, 400, 150, 0 (sum 1,000), each raised by 250 to sum
    // to the rent of 2,000.
    let raw: Vec<i64> = answer.object_label.iter().map(|&l| -l).collect();
    let shift = (2_000 - raw.iter().sum::<i64>()) / 4;
    let prices: Vec<i64> = raw.iter().map(|&p| p + shift).collect();
    assert_eq!(prices, [700, 650, 400, 250]);
    assert_eq!(prices.iter().sum::<i64>(), 2_000);
    // Daniel wants room 1, Anita's, and Anita moves to the free room 2. Tomás wants room 2,
    // Anita's, then rooms 1 and 3, and reaches the free room 4 through Anita's row: Tomás takes
    // room 2 and Anita moves to room 4.
    assert_eq!(steps[2].path, [0, 1]);
    assert_eq!(steps[2].settled, [0, 1]);
    assert_eq!(steps[3].settled, [1, 0, 2, 3]);
    assert_eq!(steps[3].path, [1, 3]);
}

#[test]
fn on_a_tie_a_free_object_comes_before_a_held_one_of_lower_index() {
    // Person 1 finds objects 0 (held) and 1 (free) both at 0 and takes the free one at once; the
    // lowest index alone would visit 0 first and move person 0 to object 1.
    let (answer, steps) = checked(&[vec![0, 0], vec![0, 0]], true);
    assert_eq!(steps[1].settled, [1]);
    assert_eq!(answer.obj, [0, 1]);
    // Lean's tie table: person 0 takes object 0 at 1; person 1 then takes the free object 1.
    let (answer, steps) = checked(&[vec![1, 1], vec![0, 0]], true);
    let settled: Vec<&[usize]> = steps.iter().map(|s| &s.settled[..]).collect();
    assert_eq!(settled, [&[0][..], &[1]]);
    assert_eq!(answer.obj, [0, 1]);
}

#[test]
fn on_a_tie_of_free_objects_the_lowest_index_wins() {
    // Person 0 finds objects 1 and 2 free at 1 each: object 1.
    let cost = vec![vec![5, 1, 1], vec![0, 9, 9], vec![9, 9, 0]];
    let (answer, steps) = checked(&cost, true);
    assert_eq!(steps[0].settled, [1]);
    assert_eq!(answer.obj, [1, 0, 2]);
}

#[test]
fn on_a_tie_of_held_objects_the_lowest_index_wins() {
    // Persons 0 and 1 hold objects 0 and 1; person 2 finds both at 1, the free object 2 at 5:
    // object 0 first, then 1 (now at 0), then 2.
    let cost = vec![vec![0, 9, 9], vec![9, 0, 9], vec![1, 1, 5]];
    let (answer, steps) = checked(&cost, true);
    assert_eq!(steps[2].settled, [0, 1, 2]);
    assert_eq!(steps[2].path, [2]);
    assert_eq!(answer.obj, [0, 1, 2]);
}

#[test]
fn an_empty_table_one_person_and_costs_below_zero() {
    let (answer, steps) = checked(&[], true);
    assert!(answer.obj.is_empty() && steps.is_empty());
    assert_eq!(answer.cost, 0);
    let (answer, _) = checked(&[vec![-5]], true);
    assert_eq!(
        (
            answer.obj,
            answer.person_label,
            answer.object_label,
            answer.cost
        ),
        (vec![0], vec![-5], vec![0], -5)
    );
    let (answer, _) = checked(&[vec![-3, 4, -8], vec![0, -7, 2], vec![-1, -1, -9]], true);
    // -3 - 7 - 9.
    assert_eq!(answer.cost, -19);
}

#[test]
fn a_table_that_is_not_square_is_refused() {
    // Lean: Problem.Square
    let refused = FlowsError::NotSquare {
        row: 1,
        length: 1,
        people: 2,
    };
    assert_eq!(assignment(&[vec![1, 2], vec![3]]), Err(refused.clone()));
    assert_eq!(
        assignment_with_steps(&[vec![1, 2], vec![3]]).err(),
        Some(refused.clone())
    );
    assert_eq!(
        assignment(&[vec![1, 2]]),
        Err(FlowsError::NotSquare {
            row: 0,
            length: 2,
            people: 1
        })
    );
    assert_eq!(
        refused.to_string(),
        "row 1 has 1 costs for 2 people: one cost per object, as many objects as people"
    );
    assert_eq!(assignment_f64(&[vec![1.0, 2.0], vec![3.0]]), Err(refused));
    let nan = FlowsError::CostNotFinite {
        person: 1,
        object: 0,
    };
    assert_eq!(
        assignment_f64(&[vec![1.0, 2.0], vec![f64::NAN, f64::INFINITY]]),
        Err(nan.clone())
    );
    assert_eq!(
        nan.to_string(),
        "the cost of object 0 for person 1 is not finite"
    );
}

#[test]
fn a_decimal_cost_past_the_range_is_refused_and_one_at_its_edge_keeps_finite_labels() {
    // The label move 1e308 - (-1e308) would overflow to infinity.
    let large = vec![vec![1e308, -1e308], vec![1e308, -1e308]];
    let refused = FlowsError::CostTooLarge {
        person: 0,
        object: 0,
    };
    assert_eq!(assignment_f64(&large), Err(refused.clone()));
    assert_eq!(
        refused.to_string(),
        "the cost of object 0 for person 0 is above f64::MAX / (16 n) in magnitude"
    );
    // The first refused cost in row order is named, whichever the reason.
    assert_eq!(
        assignment_f64(&[vec![1e308, 0.0], vec![f64::NAN, 0.0]]),
        Err(FlowsError::CostTooLarge {
            person: 0,
            object: 0
        })
    );
    assert_eq!(
        assignment_f64(&[vec![0.0, f64::INFINITY], vec![1e308, 0.0]]),
        Err(FlowsError::CostNotFinite {
            person: 0,
            object: 1
        })
    );
    // The same shape at the edge of the range, m = f64::MAX / 32 for two people: every label is
    // finite, and they fit every pair and meet the chosen ones exactly.
    let m = f64::MAX / 32.0;
    let edge = vec![vec![m, -m], vec![m, -m]];
    let answer = assignment_f64(&edge).unwrap();
    assert_eq!(answer.obj, [1, 0]);
    assert_eq!(answer.person_label, [m, m]);
    assert_eq!(answer.object_label, [0.0, -2.0 * m]);
    assert_eq!(answer.cost, 0.0);
    for (i, row) in edge.iter().enumerate() {
        for (j, &c) in row.iter().enumerate() {
            let sum = answer.person_label[i] + answer.object_label[j];
            assert!(sum.is_finite() && sum <= c);
            if answer.obj[i] == j {
                assert_eq!(sum, c);
            }
        }
    }
}

/// A square table of `n` people with costs in `lo..hi`.
fn table(n: usize, lo: i64, hi: i64) -> impl Strategy<Value = Vec<Vec<i64>>> {
    prop::collection::vec(prop::collection::vec(lo..hi, n), n)
}

proptest! {
    #[test]
    fn on_any_small_table_the_answer_is_the_cheapest(
        cost in (0usize..=7).prop_flat_map(|n| table(n, -20, 20))
    ) {
        // Lean: Contract.promise, Ops.OneSearchPerPerson
        let (answer, steps) = assignment_with_steps(&cost).unwrap();
        prop_assert_eq!(meets_the_contract(&cost, &answer, &steps, true), Ok(()));
    }

    #[test]
    fn on_any_small_table_of_many_ties_the_answer_is_the_cheapest(
        cost in (0usize..=7).prop_flat_map(|n| table(n, 0, 3))
    ) {
        let (answer, steps) = assignment_with_steps(&cost).unwrap();
        prop_assert_eq!(meets_the_contract(&cost, &answer, &steps, true), Ok(()));
    }
}

/// A draw below `k`.
fn below(r: &mut SplitMix64, k: u64) -> u64 {
    r.next_u64() % k
}

/// A square table of 1 to 60 people with costs drawn from `lo..lo + span`.
fn drawn(r: &mut SplitMix64, lo: i64, span: u64) -> Vec<Vec<i64>> {
    let n = 1 + below(r, 60) as usize;
    (0..n)
        .map(|_| (0..n).map(|_| lo + below(r, span) as i64).collect())
        .collect()
}

#[test]
fn on_larger_tables_the_labels_certify_every_answer() {
    // Up to 60 people, costs from -1,000 to 1,000, then from 0 to 4 (many ties); the labels are
    // the certificate, no oracle.
    let mut r = SplitMix64::new(7);
    for k in 0..200 {
        let cost = if k % 2 == 0 {
            drawn(&mut r, -1_000, 2_001)
        } else {
            drawn(&mut r, 0, 5)
        };
        checked(&cost, false);
    }
}

/// Whether the labels after `placed` people stay in the range `assignment`'s documentation
/// states: a person's label zero until their search, then between the smallest and the largest
/// cost; an object's label between minus the spread of the costs and zero.
fn labels_in_range(cost: &[Vec<i64>], placed: usize, u: &[i64], v: &[i64]) -> bool {
    let low = cost.iter().flatten().copied().min().unwrap_or(0);
    let high = cost.iter().flatten().copied().max().unwrap_or(0);
    u.iter().enumerate().all(|(i, &l)| {
        if i < placed {
            low <= l && l <= high
        } else {
            l == 0
        }
    }) && v.iter().all(|&l| low - high <= l && l <= 0)
}

#[test]
fn the_labels_stay_in_the_stated_range() {
    // All costs 5: the spread is 0, every object keeps the label 0 and every person gets 5.
    let mut tables = vec![vec![vec![5, 5], vec![5, 5]]];
    // The rent shifted up by 1,000: the object labels do not move.
    tables.push(vec![
        vec![1_350, 1_500, 1_200, 1_550],
        vec![1_200, 1_250, 1_500, 1_650],
        vec![1_000, 1_350, 1_600, 1_650],
        vec![1_250, 1_200, 1_500, 1_650],
    ]);
    let mut r = SplitMix64::new(29);
    for k in 0..200 {
        tables.push(match k % 3 {
            0 => drawn(&mut r, -1_000, 2_001),
            1 => drawn(&mut r, 500, 1_001),
            _ => drawn(&mut r, -700, 3),
        });
    }
    for cost in &tables {
        let (answer, steps) = checked(cost, false);
        let n = cost.len();
        assert!(labels_in_range(
            cost,
            n,
            &answer.person_label,
            &answer.object_label
        ));
        for (k, step) in steps.iter().enumerate() {
            assert!(labels_in_range(
                cost,
                k + 1,
                &step.person_label,
                &step.object_label
            ));
        }
    }
    let (answer, _) = checked(&tables[0], true);
    assert_eq!(
        (answer.person_label, answer.object_label),
        (vec![5, 5], vec![0, 0])
    );
    let (answer, _) = checked(&tables[1], true);
    assert_eq!(answer.object_label, [-450, -400, -150, 0]);
}

#[test]
fn whole_costs_given_as_decimals_take_the_same_steps() {
    // Small integers are exact in f64, so the procedure, ties included, is the same.
    let mut r = SplitMix64::new(19);
    for k in 0..100 {
        let cost = drawn(&mut r, -50, if k % 2 == 0 { 101 } else { 3 });
        let whole = assignment(&cost).unwrap();
        let decimal: Vec<Vec<f64>> = cost
            .iter()
            .map(|row| row.iter().map(|&c| c as f64).collect())
            .collect();
        let answer = assignment_f64(&decimal).unwrap();
        assert_eq!(answer.obj, whole.obj);
        let as_f64 = |l: &[i64]| l.iter().map(|&x| x as f64).collect::<Vec<f64>>();
        assert_eq!(answer.person_label, as_f64(&whole.person_label));
        assert_eq!(answer.object_label, as_f64(&whole.object_label));
        assert_eq!(answer.cost, whole.cost as f64);
    }
}

#[test]
fn on_decimal_tables_the_labels_fit_within_the_stated_tolerance() {
    let mut r = SplitMix64::new(23);
    for _ in 0..100 {
        let n = 1 + below(&mut r, 60) as usize;
        let cost: Vec<Vec<f64>> = (0..n)
            .map(|_| {
                (0..n)
                    .map(|_| (below(&mut r, 1 << 40) as f64 / (1u64 << 30) as f64) - 512.0)
                    .collect()
            })
            .collect();
        let answer = assignment_f64(&cost).unwrap();
        let m = cost.iter().flatten().fold(0.0f64, |a, &c| a.max(c.abs()));
        let tolerance = 4.0 * (n * n) as f64 * f64::EPSILON * (1.0 + m);
        let (obj, u, v) = (&answer.obj, &answer.person_label, &answer.object_label);
        let mut taken = vec![false; n];
        for i in 0..n {
            assert!(!taken[obj[i]]);
            taken[obj[i]] = true;
            for j in 0..n {
                assert!(u[i] + v[j] <= cost[i][j] + tolerance);
            }
            assert!((u[i] + v[obj[i]] - cost[i][obj[i]]).abs() <= tolerance);
        }
        let labels: f64 = u.iter().chain(v).sum();
        assert!((labels - answer.cost).abs() <= n as f64 * tolerance);
    }
}
