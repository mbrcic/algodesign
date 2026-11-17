use super::*;
use crate::paths::naive;
use crate::rng::SplitMix64;
use proptest::prelude::*;

/// The cargo box: 10 kg, one order of 6 kg for 30 and two of 5 kg for 20 each. The Lean's `cargo`.
const WEIGHTS: [u64; 3] = [6, 5, 5];
const VALUES: [i64; 3] = [30, 20, 20];

fn packing(value: i64, items: &[usize]) -> Packing {
    Packing {
        value,
        items: items.to_vec(),
    }
}

/// The weight and the value of a set of items.
fn weight_and_value(weights: &[u64], values: &[i64], items: &[usize]) -> (u128, i64) {
    (
        items.iter().map(|&k| u128::from(weights[k])).sum(),
        items.iter().map(|&k| values[k]).sum(),
    )
}

#[test]
fn the_cargo_box_takes_the_two_lighter_orders_where_greedy_takes_one() {
    // Lean: Ops.BestValue, Ops.ChosenItemsGiveIt, the cargo box
    assert_eq!(knapsack(&WEIGHTS, &VALUES, 10), Ok(packing(40, &[1, 2])));
    assert_eq!(naive::best_value(&WEIGHTS, &VALUES, 10), 40);
    // Greedy by value per kilo: 30 / 6 = 5 before 20 / 5 = 4 takes item 0, and then nothing fits.
    let (weight, value) = weight_and_value(&WEIGHTS, &VALUES, &[0]);
    assert!(weight <= 10 && weight + 5 > 10);
    assert_eq!(value, 30);
}

#[test]
fn a_tie_between_taking_and_skipping_takes_the_item() {
    // Lean: knapsack [⟨2, 5⟩, ⟨2, 5⟩] 2 = ⟨5, [1]⟩
    assert_eq!(knapsack(&[2, 2], &[5, 5], 2), Ok(packing(5, &[1])));
}

#[test]
fn two_weights_tie_in_the_last_layer_the_lighter_one_wins() {
    // Lean: knapsack [⟨1, 3⟩, ⟨2, 3⟩] 2 = ⟨3, [0]⟩
    assert_eq!(knapsack(&[1, 2], &[3, 3], 2), Ok(packing(3, &[0])));
}

#[test]
fn an_item_weighing_nothing_is_taken_when_it_is_worth_something() {
    // Lean: knapsack [⟨0, 4⟩, ⟨3, 2⟩] 2 = ⟨4, [0]⟩; its two arrows join the same two states
    assert_eq!(knapsack(&[0, 3], &[4, 2], 2), Ok(packing(4, &[0])));
    // Worth nothing: a tie, so it is taken; worth less: left out.
    assert_eq!(knapsack(&[0], &[0], 0), Ok(packing(0, &[0])));
    assert_eq!(knapsack(&[0], &[-1], 0), Ok(packing(0, &[])));
}

#[test]
fn an_item_worth_less_than_nothing_is_left_out() {
    // Lean: knapsack [⟨1, -3⟩] 5 = ⟨0, []⟩
    assert_eq!(knapsack(&[1], &[-3], 5), Ok(packing(0, &[])));
}

#[test]
fn no_items_or_no_room() {
    // Lean: knapsack [] 5 = ⟨0, []⟩ and knapsack cargo 0 = ⟨0, []⟩
    assert_eq!(knapsack(&[], &[], 5), Ok(packing(0, &[])));
    assert_eq!(knapsack(&WEIGHTS, &VALUES, 0), Ok(packing(0, &[])));
}

#[test]
fn a_weight_past_the_capacity_never_wraps() {
    assert_eq!(knapsack(&[u64::MAX, 1], &[9, 2], 3), Ok(packing(2, &[1])));
}

#[test]
fn weights_and_values_of_different_lengths_are_refused() {
    assert_eq!(
        knapsack(&[1, 2], &[3], 5),
        Err(PathsError::ValueCountMismatch {
            values: 1,
            weights: 2,
        })
    );
    assert_eq!(
        PathsError::ValueCountMismatch {
            values: 1,
            weights: 2,
        }
        .to_string(),
        "2 weights for 1 values: one of each per item"
    );
}

/// The knapsack on the whole table, `(n + 1)(C + 1)` cells: the same arrows in the same order, the
/// items read back through every layer. The answer, the table, and whether the walk back met a
/// tie, taking an item gaining exactly what skipping it does.
fn whole_table(
    weights: &[u64],
    values: &[i64],
    capacity: u64,
) -> (Packing, Vec<Vec<Option<i64>>>, bool) {
    let n = weights.len();
    let width = capacity as usize + 1;
    let mut best = vec![vec![None; width]; n + 1];
    best[0][0] = Some(0);
    for i in 0..n {
        for w in 0..width {
            let Some(b) = best[i][w] else {
                continue;
            };
            relax(&mut best[i + 1], w, b);
            if weights[i] <= capacity - w as u64 {
                relax(&mut best[i + 1], w + weights[i] as usize, b + values[i]);
            }
        }
    }
    let mut end: Option<(i64, usize)> = None;
    for (w, &cell) in best[n].iter().enumerate() {
        if let Some(b) = cell {
            if end.is_none_or(|(b0, _)| b0 < b) {
                end = Some((b, w));
            }
        }
    }
    let Some((value, mut w)) = end else {
        return (packing(0, &[]), best, false);
    };
    let (mut items, mut tie) = (Vec::new(), false);
    for i in (0..n).rev() {
        if weights[i] <= w as u64 {
            let from = w - weights[i] as usize;
            let (take, skip) = (best[i][from], best[i][w]);
            tie |= take.zip(skip).is_some_and(|(b, c)| c == b + values[i]);
            if take_wins(take, values[i], skip) {
                items.push(i);
                w = from;
            }
        }
    }
    items.reverse();
    (Packing { value, items }, best, tie)
}

/// A draw below `k`.
fn below(r: &mut SplitMix64, k: u64) -> u64 {
    r.next_u64() % k
}

#[test]
fn the_two_layers_and_the_bits_answer_as_the_whole_table() {
    // Small instances: a weight of 0 one time in four, weights past the capacity, values from −4
    // to 5, so ties are common; one instance in three has only even weights and an odd capacity,
    // so no odd weight is ever reached.
    let mut r = SplitMix64::new(72);
    let (mut zero, mut negative, mut ties, mut unreached) = (0, 0, 0, 0);
    for k in 0..6000 {
        let even = k % 3 == 0;
        let n = below(&mut r, 11) as usize;
        let capacity = if even {
            2 * below(&mut r, 13) + 1
        } else {
            below(&mut r, 26)
        };
        let weights: Vec<u64> = (0..n)
            .map(|_| match (below(&mut r, 4), even) {
                (0, _) => 0,
                (_, true) => 2 * (1 + below(&mut r, 15)),
                (_, false) => 1 + below(&mut r, 30),
            })
            .collect();
        let values: Vec<i64> = (0..n).map(|_| below(&mut r, 10) as i64 - 4).collect();
        let (p, best, tie) = whole_table(&weights, &values, capacity);
        assert_eq!(
            knapsack(&weights, &values, capacity),
            Ok(p),
            "{weights:?} {values:?} {capacity}"
        );
        zero += weights.iter().filter(|&&x| x == 0).count();
        negative += values.iter().filter(|&&x| x < 0).count();
        ties += usize::from(tie);
        unreached += usize::from(best[n].contains(&None));
    }
    // Every awkward case was reached.
    assert!(zero > 0 && negative > 0 && ties > 0 && unreached > 0);
}

#[test]
fn a_large_capacity_needs_only_two_layers_and_the_bits() {
    // 123 items at capacity 10⁶: the whole table would be 124 × 1,000,001 cells of 16 bytes;
    // the two layers and the bits are a small fraction of that. Items 0 to 119 weigh 20,000 each
    // and are worth their index plus one, so 50 fit and the best are 70 to 119, worth 4775; item
    // 120 weighs nothing and is worth 5; item 121 weighs 1 and is worth −7; item 122 never fits.
    let mut weights = vec![20_000; 120];
    let mut values: Vec<i64> = (1..=120).collect();
    weights.extend([0, 1, 1_000_001]);
    values.extend([5, -7, 1000]);
    let items: Vec<usize> = (70..=120).collect();
    assert_eq!(
        knapsack(&weights, &values, 1_000_000),
        Ok(packing(4775 + 5, &items))
    );
}

/// A handful of items, weights 0 to 6 and values −3 to 9, and a box of 0 to 12.
fn items() -> impl Strategy<Value = (Vec<u64>, Vec<i64>, u64)> {
    prop::collection::vec((0u64..7, -3i64..10), 0..=12)
        .prop_flat_map(|items| (Just(items), 0u64..13))
        .prop_map(|(items, capacity)| {
            let (weights, values) = items.into_iter().unzip();
            (weights, values, capacity)
        })
}

proptest! {
    #[test]
    fn on_any_items_the_value_is_the_best_and_the_items_give_it(
        (weights, values, capacity) in items()
    ) {
        // Lean: Ops.BestValue, Ops.ChosenItemsGiveIt
        let p = knapsack(&weights, &values, capacity).unwrap();
        prop_assert_eq!(p.value, naive::best_value(&weights, &values, capacity));
        prop_assert!(p.items.windows(2).all(|k| k[0] < k[1]));
        prop_assert!(p.items.iter().all(|&k| k < weights.len()));
        let (weight, value) = weight_and_value(&weights, &values, &p.items);
        prop_assert!(weight <= u128::from(capacity));
        prop_assert_eq!(value, p.value);
        prop_assert_eq!(p, whole_table(&weights, &values, capacity).0);
    }
}
