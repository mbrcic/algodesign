/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Cost
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Binary search tree: analysis

The analytic results: the optimal weighted BST by dynamic programming (`optCost_correct`),
Sedgewick–Flajolet's exact internal-path-length formula (`internalPathLength_eq`) with its search
costs and `~2 ln N` asymptotic (`tendsto_internalPathLength_div_mul_log`), and the height-growth
constant's existence (`exists_heightConstant`). The recurrence is the definition of
`internalPathLength`; that it is the expectation over random insertion orders is not a theorem
here.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BST

variable {α : Type}
variable [LinearOrder α]

/-! ## Statement-only: the four analytic results beside the operational development above (optimal
weighted BST via DP, Sedgewick–Flajolet's exact internal-path-length formula, the resulting
~2 ln N average-case asymptotic, and the height-growth constant's *existence*). -/

omit [LinearOrder α] in
/-- The tree's keys, in sorted order (on a `Sorted` tree — but the definition itself needs no
order at all, it's just "left subtree, then this node's key, then right subtree", recursively).
Needed to state what "a BST whose key set is `keys`" even means for the optimal-BST DP below. -/
def inorder : BST α → List α
  | leaf => []
  | node l k r => inorder l ++ k :: inorder r

omit [LinearOrder α] in
@[simp] theorem inorder_leaf : inorder (leaf : BST α) = [] := rfl

omit [LinearOrder α] in
@[simp] theorem inorder_node (l : BST α) (k : α) (r : BST α) :
    inorder (node l k r) = inorder l ++ k :: inorder r := rfl

omit [LinearOrder α] in
/-- Total access frequency (weight) over every key in the tree — order-free, like `inorder`. -/
def weight (w : α → ℕ) : BST α → ℕ
  | leaf => 0
  | node l k r => weight w l + weight w r + w k

omit [LinearOrder α] in
@[simp] theorem weight_leaf (w : α → ℕ) : weight w (leaf : BST α) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem weight_node (w : α → ℕ) (l : BST α) (k : α) (r : BST α) :
    weight w (node l k r) = weight w l + weight w r + w k := rfl

omit [LinearOrder α] in
/-- `weight` is exactly "sum `w` over the in-order key list" — the bridge used to relate `cost`'s
recursive, per-node accounting to `optCost`'s "sum of `w` over the whole key range" toll term. -/
theorem weight_eq_sum (w : α → ℕ) (t : BST α) : weight w t = ((inorder t).map w).sum := by
  induction t with
  | leaf => simp
  | node l k r ihl ihr => simp [ihl, ihr, List.sum_append, Nat.add_comm, Nat.add_left_comm]

omit [LinearOrder α] in
/-- **Weighted search cost** of a tree, given per-key access frequencies `w`: the standard
recursive accounting for `Σ (depth v + 1) · w (key v)` over every node `v` (root at depth `0`,
i.e. costing `1`; a node one level down costs `2`; and so on — the usual "expected number of
comparisons, weighted by how often each key is looked up" reading). The direct recursive
definition here is the same quantity: descending from `node l k r` into `l` or `r` shifts every
node already in that subtree one level deeper, i.e. adds `1 * w (that node's key)` to its
contribution for *each* node in the subtree — exactly `weight w l` (resp. `weight w r`) extra, on
top of whatever `cost w l` (resp. `cost w r`) already counted relative to `l`'s (resp. `r`'s) own
root. So `cost w (node l k r) = cost w l + cost w r + weight w l + weight w r + w k`, which is
`cost w l + cost w r + weight w (node l k r)` after unfolding `weight`'s own recursive equation —
the definition below. -/
def cost (w : α → ℕ) : BST α → ℕ
  | leaf => 0
  | node l k r => cost w l + cost w r + weight w (node l k r)

omit [LinearOrder α] in
@[simp] theorem cost_leaf (w : α → ℕ) : cost w (leaf : BST α) = 0 := rfl

omit [LinearOrder α] in
theorem cost_node (w : α → ℕ) (l : BST α) (k : α) (r : BST α) :
    cost w (node l k r) = cost w l + cost w r + weight w l + weight w r + w k := by
  simp [cost, weight]; omega

omit [LinearOrder α] in
/-- **Optimal (minimum) weighted BST cost** achievable by any tree whose in-order key list is
`keys`, given frequencies `w`: the standard CLRS dynamic-programming recurrence. An empty key list
costs nothing; otherwise, try every split point `i` (the root sits at position `i` in `keys`,
`0`-indexed), recursively solve the left range `keys.take i` and right range `keys.drop (i+1)`
(dropping the root key itself), and add the toll every choice of root pays regardless — the total
weight of the whole range, since every one of these keys is looked up exactly once no matter which
key sits at the root. Indexed over `Fin keys.length` (not `Finset.range keys.length`/`List.range`)
so that the well-founded recursion's decreasing-call obligations (`↑i < keys.length`) come for
free from `i.isLt` — see `LLRB`'s and `BST`'s earlier definitions for the same convention. -/
def optCost (w : α → ℕ) (keys : List α) : ℕ :=
  if h : keys = [] then 0
  else
    (Finset.univ : Finset (Fin keys.length)).inf'
      ⟨⟨0, List.length_pos_iff.mpr h⟩, Finset.mem_univ _⟩
      (fun i => optCost w (keys.take i) + optCost w (keys.drop (i + 1)))
      + (keys.map w).sum
termination_by keys.length
decreasing_by
  · have hi := i.isLt
    have _hlen : 0 < keys.length := List.length_pos_iff.mpr h
    simp only [List.length_take]
    omega
  · have hi := i.isLt
    have _hlen : 0 < keys.length := List.length_pos_iff.mpr h
    simp only [List.length_drop]
    omega

omit [LinearOrder α] in
/-- A key is a member of the tree iff it occurs in the in-order key list — the bridge from the
structural `Mem`/`All` predicates to `List`-level reasoning about `inorder`, needed throughout the
`optCost` correctness proof below. -/
theorem mem_iff_mem_inorder (t : BST α) (a : α) : Mem a t ↔ a ∈ inorder t := by
  induction t with
  | leaf => simp
  | node l k r ihl ihr =>
    simp only [mem_node, inorder_node, List.mem_append, List.mem_cons, ihl, ihr]

omit [LinearOrder α] in
/-- `All p t` is equivalent to `p` holding of every element of the in-order list — the list-level
reading of `All` used to reconstruct the BST invariant from `List.Pairwise` facts about `inorder`
splits (this Mathlib has no order-parametrized `List.Sorted r l` predicate; its
`List.SortedLE`/`SortedLT`/etc. are each defeq to a specific `List.Pairwise` instance, so the
correctness proof below works with `List.Pairwise (· < ·)` directly throughout). -/
theorem all_iff_forall_mem_inorder (p : α → Prop) (t : BST α) :
    All p t ↔ ∀ a ∈ inorder t, p a :=
  ⟨fun h a ha => h.of_mem ((mem_iff_mem_inorder t a).mpr ha),
    fun h => all_of_forall_mem (fun a ha => h a ((mem_iff_mem_inorder t a).mp ha))⟩

/-- The in-order traversal of a `Sorted` tree is a (strictly) pairwise-sorted list — turns the BST
invariant into the list-level fact the `optCost` correctness proof works with. -/
theorem inorder_sorted {t : BST α} (ht : Sorted t) : (inorder t).Pairwise (· < ·) := by
  induction t with
  | leaf => simp
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    simp only [inorder_node]
    rw [List.pairwise_append]
    refine ⟨ihl hsl, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun b hb => hr.of_mem ((mem_iff_mem_inorder r b).mpr hb), ihr hsr⟩
    · intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hl.of_mem ((mem_iff_mem_inorder l a).mpr ha)
      · exact lt_trans (hl.of_mem ((mem_iff_mem_inorder l a).mpr ha))
          (hr.of_mem ((mem_iff_mem_inorder r b).mpr hb))

/-- **`optCost` is correct**: it computes the minimum, over every `Sorted` `BST` whose in-order key
list is `keys`, of that tree's weighted search `cost` — the whole point of stating the DP
recurrence at all. Proved by strong induction on `keys.length`, mirroring the well-founded
recursion `optCost` itself is defined by. Two halves, proved together (the induction hypothesis is
used in both):

1. *Achievability*: some `Sorted` tree with in-order list `keys` has `cost w t = optCost w keys`.
   Built by taking whichever split point `i` realizes the `Finset.inf'` minimum in `optCost`'s own
   recurrence (`Finset.exists_mem_eq_inf'`), recursively building optimal left/right subtrees from
   `keys.take i`/`keys.drop (i + 1)` via the induction hypothesis, and joining them under the key
   sitting right after `keys.take i`, i.e. `(keys.drop i).head`.
2. *Optimality*: every `Sorted` tree `t'` with in-order list `keys` has `cost w t' ≥ optCost w
   keys`. Any such `t'` is `node l' k' r'` for some `l' k' r'`, and its in-order equation
   `inorder l' ++ k' :: inorder r' = keys` pins down a split point `j := (inorder l').length` with
   `keys.take j = inorder l'` and `keys.drop (j + 1) = inorder r'`; `cost w t'` then splits as
   `cost w l' + cost w r' + (toll for the whole range)`, each summand bounded below by the
   induction hypothesis (for the subtrees) or `Finset.inf'_le` (for the recurrence evaluated at
   `j`), and these bounds sum to exactly `optCost w keys`.

(This Mathlib snapshot has no order-parametrized `List.Sorted r l` predicate — see
`all_iff_forall_mem_inorder`'s docstring — so the sortedness hypothesis is stated as
`keys.Pairwise (· < ·)` directly, the same underlying fact.) -/
theorem optCost_correct (w : α → ℕ) (keys : List α) (hsorted : keys.Pairwise (· < ·)) :
    (∃ t : BST α, Sorted t ∧ inorder t = keys ∧ cost w t = optCost w keys) ∧
      ∀ t' : BST α, Sorted t' → inorder t' = keys → optCost w keys ≤ cost w t' := by
  have main : ∀ n : ℕ, ∀ ks : List α, ks.length = n → ks.Pairwise (· < ·) →
      (∃ t : BST α, Sorted t ∧ inorder t = ks ∧ cost w t = optCost w ks) ∧
        ∀ t' : BST α, Sorted t' → inorder t' = ks → optCost w ks ≤ cost w t' := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ks hlen hks
      rcases eq_or_ne ks [] with hks0 | hks0
      · subst hks0
        refine ⟨⟨leaf, trivial, rfl, by simp [optCost]⟩, fun t' ht' hinorder => ?_⟩
        have hleaf : t' = leaf := by
          cases t' with
          | leaf => rfl
          | node l k r => simp [inorder_node] at hinorder
        simp [hleaf, optCost]
      · have hlenpos : 0 < ks.length := List.length_pos_iff.mpr hks0
        have hne : (Finset.univ : Finset (Fin ks.length)).Nonempty :=
          ⟨⟨0, hlenpos⟩, Finset.mem_univ _⟩
        have hopt : optCost w ks = (Finset.univ : Finset (Fin ks.length)).inf' hne
            (fun i => optCost w (ks.take i) + optCost w (ks.drop (i + 1))) + (ks.map w).sum := by
          conv_lhs => unfold optCost
          rw [dite_eq_right hks0]
        constructor
        · -- Achievability: reconstruct an optimal tree from the minimizing split point.
          obtain ⟨i, -, hieq⟩ := Finset.exists_mem_eq_inf' hne
            (fun i : Fin ks.length => optCost w (ks.take i) + optCost w (ks.drop (i + 1)))
          have hdroplen : 0 < (ks.drop (i : ℕ)).length := by
            rw [List.length_drop]
            have := i.isLt
            omega
          rcases hdeq : ks.drop (i : ℕ) with _ | ⟨hd, tl0⟩
          · rw [hdeq] at hdroplen; simp at hdroplen
          · have htl0 : tl0 = ks.drop ((i : ℕ) + 1) := by
              have hdd := List.drop_drop (i := 1) (j := (i : ℕ)) (l := ks)
              rw [hdeq] at hdd
              simpa using hdd
            have hsplit : ks.take (i : ℕ) ++ hd :: tl0 = ks := by
              have htad := List.take_append_drop (i : ℕ) ks
              rwa [hdeq] at htad
            have hdmem : hd ∈ ks.drop (i : ℕ) := by rw [hdeq]; exact List.mem_cons_self
            have hAllL : ∀ x ∈ ks.take (i : ℕ), x < hd :=
              fun x hx => hks.rel_of_mem_take_of_mem_drop hx hdmem
            have hDropPairwise : (hd :: tl0).Pairwise (· < ·) := by
              have hdp := hks.drop (i := (i : ℕ))
              rwa [hdeq] at hdp
            have hAllR : ∀ y ∈ tl0, hd < y := (List.pairwise_cons.mp hDropPairwise).1
            have htakelen : (ks.take (i : ℕ)).length < n := by
              have h1 : (ks.take (i : ℕ)).length = min (i : ℕ) ks.length := List.length_take
              have h2 := i.isLt
              omega
            have htl0len : tl0.length < n := by
              have h1 : tl0.length = (ks.drop ((i : ℕ) + 1)).length := by rw [htl0]
              have h2 : (ks.drop ((i : ℕ) + 1)).length = ks.length - ((i : ℕ) + 1) :=
                List.length_drop
              have h3 := i.isLt
              omega
            have hTakePairwise : (ks.take (i : ℕ)).Pairwise (· < ·) := hks.take
            have hTl0Pairwise : tl0.Pairwise (· < ·) := by rw [htl0]; exact hks.drop
            obtain ⟨tL, hSortedL, hInorderL, hCostL⟩ :=
              (ih (ks.take (i : ℕ)).length htakelen (ks.take (i : ℕ)) rfl hTakePairwise).1
            obtain ⟨tR, hSortedR, hInorderR, hCostR⟩ :=
              (ih tl0.length htl0len tl0 rfl hTl0Pairwise).1
            refine ⟨node tL hd tR, ⟨?_, ?_, hSortedL, hSortedR⟩, ?_, ?_⟩
            · exact (all_iff_forall_mem_inorder _ tL).mpr (by rw [hInorderL]; exact hAllL)
            · exact (all_iff_forall_mem_inorder _ tR).mpr (by rw [hInorderR]; exact hAllR)
            · rw [inorder_node, hInorderL, hInorderR, hsplit]
            · have hSumSplit : (ks.map w).sum
                  = ((ks.take (i : ℕ)).map w).sum + (w hd + (tl0.map w).sum) := by
                conv_lhs => rw [← hsplit]
                simp [List.sum_append]
              have e1 : cost w (node tL hd tR)
                  = cost w tL + cost w tR + weight w tL + weight w tR + w hd :=
                cost_node w tL hd tR
              have e2 : weight w tL = ((ks.take (i : ℕ)).map w).sum := by
                rw [weight_eq_sum, hInorderL]
              have e3 : weight w tR = (tl0.map w).sum := by
                rw [weight_eq_sum, hInorderR]
              have e4 : optCost w ks
                  = optCost w (ks.take (i : ℕ)) + optCost w tl0 + (ks.map w).sum := by
                rw [hopt, hieq, ← htl0]
              omega
        · -- Optimality: any valid tree's split point is bounded below by the recurrence at it.
          intro t' ht' hinorder
          cases t' with
          | leaf => simp only [inorder_leaf] at hinorder; exact absurd hinorder.symm hks0
          | node l' k' r' =>
            obtain ⟨hAllL', hAllR', hSortedL', hSortedR'⟩ := ht'
            have hinorder' : inorder l' ++ k' :: inorder r' = ks := by
              rw [← inorder_node]; exact hinorder
            set j := (inorder l').length with hj
            have htakeL : ks.take j = inorder l' := by
              rw [← hinorder']; exact List.take_left
            have hdropL : ks.drop j = k' :: inorder r' := by
              rw [← hinorder']; exact List.drop_left
            have hdropL' : ks.drop (j + 1) = inorder r' := by
              have hdd := List.drop_drop (i := 1) (j := j) (l := ks)
              rw [hdropL] at hdd
              simpa using hdd.symm
            have hlenEq : ks.length = (inorder l').length + (k' :: inorder r').length := by
              rw [← hinorder', List.length_append]
            simp only [List.length_cons] at hlenEq
            have hltj : j < ks.length := by omega
            have htakelen : (ks.take j).length < n := by
              rw [htakeL, ← hj]
              omega
            have hdroplen : (ks.drop (j + 1)).length < n := by
              rw [hdropL']
              omega
            have hTakePairwise : (ks.take j).Pairwise (· < ·) := hks.take
            have hDropPairwise : (ks.drop (j + 1)).Pairwise (· < ·) := hks.drop
            have hminL : optCost w (ks.take j) ≤ cost w l' :=
              (ih (ks.take j).length htakelen (ks.take j) rfl hTakePairwise).2 l' hSortedL'
                htakeL.symm
            have hminR : optCost w (ks.drop (j + 1)) ≤ cost w r' :=
              (ih (ks.drop (j + 1)).length hdroplen (ks.drop (j + 1)) rfl hDropPairwise).2 r'
                hSortedR' hdropL'.symm
            have hw : weight w l' + weight w r' + w k' = (ks.map w).sum := by
              rw [← weight_node, weight_eq_sum, hinorder]
            have hcostt' : cost w (node l' k' r') = cost w l' + cost w r' + (ks.map w).sum := by
              rw [cost_node]
              omega
            have hle : optCost w ks
                ≤ optCost w (ks.take j) + optCost w (ks.drop (j + 1)) + (ks.map w).sum := by
              rw [hopt]
              set f : Fin ks.length → ℕ :=
                fun i => optCost w (ks.take i) + optCost w (ks.drop (i + 1)) with hf
              have hinf : (Finset.univ : Finset (Fin ks.length)).inf' hne f
                  ≤ optCost w (ks.take j) + optCost w (ks.drop (j + 1)) :=
                Finset.inf'_le f (Finset.mem_univ (⟨j, hltj⟩ : Fin ks.length))
              simpa using Nat.add_le_add_right hinf ((ks.map w).sum)
            rw [hcostt']
            omega
  exact main keys.length keys rfl hsorted

omit [LinearOrder α] in
/-- **The internal-path-length recurrence for a randomly-built BST** (Sedgewick–Flajolet, §6.6):
insert `n + 1` keys in uniformly random order into an initially-empty BST; the root is equally
likely to be any of the `n + 1` keys, splitting the rest into a left subtree of size `i` and right
subtree of size `n - i` for a uniformly random `i`, each itself a random BST of that size. Internal
path length (sum of node depths, root at depth `0`) satisfies `IPL(t) = IPL(l) + IPL(r) + (size l +
size r)` for `t = node l k r` (every node in `l`/`r` gains one level of depth under the new root),
so in expectation over the random split point `C (n+1) = n + average over i of (C i + C (n-i))`
— the same shape as the quicksort comparison-count recurrence (§1.5/§3.10), but with `n` (not
`n + 2`) keys getting redistributed at the root step, hence `n` rather than `n + 1` as the "toll"
and `n + 1` (not `n - 1`) as the divisor — this is exactly the off-by-one Sedgewick–Flajolet flag
as the key difference from quicksort.
That derivation is the informal argument the recurrence comes from; only the recurrence itself is
formal here, and no theorem connects it to `BST.insert` over random orders. Indexed by
`Fin (n + 1)` rather than `Finset.range (n + 1)` directly so that well-founded
recursion's decreasing-call obligation (`↑k < n + 1`) comes for free from `k.isLt`. -/
def internalPathLength : ℕ → ℚ
  | 0 => 0
  | n + 1 => (n : ℚ) + (2 / (n + 1)) * ∑ k : Fin (n + 1), internalPathLength k

omit [LinearOrder α] in
@[simp] theorem internalPathLength_zero : internalPathLength 0 = 0 := by
  simp [internalPathLength]

omit [LinearOrder α] in
theorem internalPathLength_succ (n : ℕ) :
    internalPathLength (n + 1)
      = (n : ℚ) + (2 / ((n : ℚ) + 1)) * ∑ k : Fin (n + 1), internalPathLength k := by
  simp [internalPathLength]

omit [LinearOrder α] in
/-- The two-term recurrence obtained by peeling the last summand off `internalPathLength`'s
defining sum (`Fin.sum_univ_castSucc`) and eliminating the partial sum via the defining equation
for `internalPathLength (n + 1)` itself (solved for that sum). This is the form the closed-form
theorem below actually inducts on — the raw definition's sum-of-all-previous-values shape isn't
directly an induction step, but this two-term shape is. -/
theorem internalPathLength_two_term (n : ℕ) :
    ((n : ℚ) + 2) * internalPathLength (n + 2) =
      ((n : ℚ) + 3) * internalPathLength (n + 1) + 2 * ((n : ℚ) + 1) := by
  have hidx : n + 1 + 1 = n + 2 := by omega
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hn2 : ((n : ℚ) + 1 + 1) ≠ 0 := by positivity
  have hC1' : ((n : ℚ) + 1) * internalPathLength (n + 1)
      = (n : ℚ) * ((n : ℚ) + 1) + 2 * ∑ k : Fin (n + 1), internalPathLength k := by
    rw [internalPathLength_succ n]
    field_simp
  have hC2' : ((n : ℚ) + 2) * internalPathLength (n + 2)
      = ((n : ℚ) + 1) * ((n : ℚ) + 2) + 2 * ∑ k : Fin (n + 2), internalPathLength k := by
    have h := internalPathLength_succ (n + 1)
    rw [hidx] at h
    push_cast at h
    rw [h]
    field_simp
    ring
  have hsum : (∑ k : Fin (n + 2), internalPathLength k)
      = (∑ k : Fin (n + 1), internalPathLength k) + internalPathLength (n + 1) := by
    have h : (∑ k : Fin (n + 1 + 1), internalPathLength k)
        = (∑ k : Fin (n + 1), internalPathLength k) + internalPathLength (n + 1) := by
      rw [Fin.sum_univ_castSucc]
      simp
    rwa [hidx] at h
  rw [hsum] at hC2'
  linear_combination hC2' - hC1'

omit [LinearOrder α] in
/-- The one-step recurrence relating consecutive values, valid at every `n` (including the `n = 0`
base transition, which is a direct definitional unfold rather than an instance of
`internalPathLength_two_term`). -/
theorem internalPathLength_step (n : ℕ) :
    ((n : ℚ) + 1) * internalPathLength (n + 1) = ((n : ℚ) + 2) * internalPathLength n + 2 * n := by
  cases n with
  | zero => simp [internalPathLength_succ]
  | succ m =>
    have h := internalPathLength_two_term m
    have hidx : m + 1 + 1 = m + 2 := by omega
    rw [hidx]
    push_cast
    linear_combination h

omit [LinearOrder α] in
/-- **Sedgewick–Flajolet's exact internal-path-length formula** (Theorem 6.5), as
a closed form of the recurrence: `internalPathLength n =
2(n+1) H_n - 4n`, where `H_n` is the `n`th harmonic number (`harmonic n` in Mathlib,
`∑_{i=1}^n 1/i`). Sedgewick–Flajolet derive that recurrence as the expected internal path length
of a BST built from `n` random keys; here the recurrence is the definition, and that it is that
expectation is not proved (no probability space over insertion orders is modelled). The book
states this as `C_N = 2(N+1)(H_{N+1} - 1) - 2N`; the two forms are the
same fact (`H_{N+1} = H_N + 1/(N+1)` turns one into the other by pure algebra), and this form is
the one that inducts most directly against `internalPathLength_step`. -/
theorem internalPathLength_eq (n : ℕ) :
    internalPathLength n = 2 * ((n : ℚ) + 1) * harmonic n - 4 * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hstep := internalPathLength_step m
    rw [ih] at hstep
    have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    rw [harmonic_succ]
    push_cast
    field_simp
    linear_combination hstep

omit [LinearOrder α] in
/-- The book's own form of Theorem 6.5, `C_N = 2(N+1)(H_{N+1} - 1) - 2N`, as a corollary of
`internalPathLength_eq` via `harmonic_succ`. -/
theorem internalPathLength_eq' (n : ℕ) :
    internalPathLength n = 2 * ((n : ℚ) + 1) * (harmonic (n + 1) - 1) - 2 * n := by
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [internalPathLength_eq, harmonic_succ]
  push_cast
  field_simp
  ring

omit [LinearOrder α] in
/-- Sedgewick–Flajolet's exact average successful-search-cost formula (Theorem 6.6), obtained
algebraically from `internalPathLength_eq` (their proof, and this one, needs no fresh recurrence —
average search cost and average path length differ only by the constant reweighting `C_N/N`). -/
theorem internalPathLength_search_cost (n : ℕ) (hn : n ≠ 0) :
    internalPathLength n / n + 1 = 2 * (1 + 1 / (n : ℚ)) * harmonic n - 3 := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [internalPathLength_eq]
  field_simp
  ring

omit [LinearOrder α] in
/-- Sedgewick–Flajolet's exact average unsuccessful-search-cost formula (Theorem 6.6). -/
theorem internalPathLength_unsuccessful_search_cost (n : ℕ) :
    (internalPathLength n + 2 * n) / ((n : ℚ) + 1) = 2 * harmonic (n + 1) - 2 := by
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [internalPathLength_eq, harmonic_succ]
  push_cast
  field_simp
  ring

/-- **The ~2 ln N average-case asymptotic** (Sedgewick–Flajolet's Theorem 6.10 context:
about 2·ln N ≈ 1.39·lg N compares on average): the solution of the internal-path-length
recurrence (`internalPathLength`, which
Sedgewick–Flajolet derive as the expected internal path length of a random `n`-key BST; that
reading is the recurrence's origin, not a theorem here), divided by `n log n`, tends to `2` as
`n → ∞`. Proved by squeezing `internalPathLength n / (n log n)` between two sequences
built from Mathlib's ready-made harmonic-number log bounds (`Mathlib.NumberTheory.Harmonic.Bounds`,
`log n ≤ harmonic n ≤ 1 + log n` — the exact-formula route above makes this tractable without any
of Sedgewick–Flajolet's own generating-function machinery: their singularity analysis is needed for
the *height* asymptotic (`exists_heightConstant`'s docstring), not this additive, harmonic-number
one). Both bounding sequences tend to `2`: `2(n+1)/n - 4/log n → 2 + 0` from below and
`2(n+1)/n + 2(n+1)/(n log n) - 4/log n → 2 + 0 + 0` from above, using only `log n ≤ harmonic n` (the
weaker, elementary-to-state half of the Mathlib bound suffices for both directions here since
`log(n+1) ≥ log n`). -/
theorem tendsto_internalPathLength_div_mul_log :
    Filter.Tendsto (fun n : ℕ => (internalPathLength n : ℝ) / ((n : ℝ) * Real.log n))
      Filter.atTop (nhds 2) := by
  have hloginv : Filter.Tendsto (fun n : ℕ => (Real.log n)⁻¹) Filter.atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hninv : Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlower : Filter.Tendsto
      (fun n : ℕ => (2 : ℝ) + 2 * (n : ℝ)⁻¹ - 4 * (Real.log n)⁻¹) Filter.atTop (nhds 2) := by
    have h : Filter.Tendsto (fun n : ℕ => (2 : ℝ) + 2 * (n : ℝ)⁻¹ - 4 * (Real.log n)⁻¹)
        Filter.atTop (nhds (2 + 2 * 0 - 4 * 0)) :=
      (tendsto_const_nhds.add (hninv.const_mul 2)).sub (hloginv.const_mul 4)
    simpa using h
  have hupper : Filter.Tendsto
      (fun n : ℕ => (2 : ℝ) + 2 * (n : ℝ)⁻¹ - 4 * (Real.log n)⁻¹
        + 2 * ((n : ℝ)⁻¹ * (Real.log n)⁻¹) + 2 * (Real.log n)⁻¹)
      Filter.atTop (nhds 2) := by
    have h : Filter.Tendsto (fun n : ℕ => (2 : ℝ) + 2 * (n : ℝ)⁻¹ - 4 * (Real.log n)⁻¹
        + 2 * ((n : ℝ)⁻¹ * (Real.log n)⁻¹) + 2 * (Real.log n)⁻¹)
        Filter.atTop (nhds (2 + 2 * 0 - 4 * 0 + 2 * (0 * 0) + 2 * 0)) :=
      (((tendsto_const_nhds.add (hninv.const_mul 2)).sub (hloginv.const_mul 4)).add
        ((hninv.mul hloginv).const_mul 2)).add (hloginv.const_mul 2)
    simpa using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1lt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1lt
    have hbound : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by
      have h1 := log_add_one_le_harmonic n
      have h2 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
        rw [Real.log_le_log_iff hn0 (by linarith)]; linarith
      refine h2.trans ?_
      have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [← this]; exact h1
    have hCeq : (internalPathLength n : ℝ) =
        2 * ((n : ℝ) + 1) * (harmonic n : ℝ) - 4 * (n : ℝ) := by
      exact_mod_cast internalPathLength_eq n
    rw [hCeq, le_div_iff₀ (by positivity)]
    have key : ((2 : ℝ) + 2 * (n : ℝ)⁻¹ - 4 * (Real.log n)⁻¹) * ((n : ℝ) * Real.log n)
        = 2 * ((n : ℝ) + 1) * Real.log n - 4 * (n : ℝ) := by
      field_simp
    rw [key]
    nlinarith [hbound, hn0]
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn1lt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1lt
    have hbound : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
    have hCeq : (internalPathLength n : ℝ) =
        2 * ((n : ℝ) + 1) * (harmonic n : ℝ) - 4 * (n : ℝ) := by
      exact_mod_cast internalPathLength_eq n
    rw [hCeq, div_le_iff₀ (by positivity)]
    have key : ((2 : ℝ) + 2 * (n : ℝ)⁻¹ - 4 * (Real.log n)⁻¹
        + 2 * ((n : ℝ)⁻¹ * (Real.log n)⁻¹) + 2 * (Real.log n)⁻¹) * ((n : ℝ) * Real.log n)
        = 2 * ((n : ℝ) + 1) * Real.log n - 4 * (n : ℝ) + 2 * ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [key]
    nlinarith [hbound, hn0]

/-- **Existence of the random-BST height-growth constant** (Sedgewick–Flajolet, *An Introduction
to the Analysis of Algorithms*, Theorem 6.10): the average height of a BST built from
`N` random keys is `~ c * log N`, where the constant `c ≈ 4.31107` is the unique positive root of
the defining
equation `c * log (2e/c) = 1`. Proving the constant's *value*, or that the height/N ratio actually
*converges* to it, is genuinely research-grade — Sedgewick–Flajolet themselves cite Devroye (1986)
for that, via singularity analysis on generating functions, not induction — and is out
of scope here. What elementary real analysis *does* reach is
**existence**: some positive real number satisfies the defining equation at all. This is a genuine,
if modest, theorem — obtained via the Intermediate Value Theorem, bracketing on `[2, 2e]`: at the
left endpoint `c = 2`, `c * log (2e/c) = 2 * log e = 2 > 1`; at the right endpoint `c = 2e`,
`c * log (2e/c) = 2e * log 1 = 0 < 1`. So `f (c) := c * log (2e/c) - 1` changes sign on `[2, 2e]`,
and by IVT some `c` in that interval hits `f c = 0`. (This does not by itself identify *which* root,
nor does it rule out other roots elsewhere — only that the equation is solvable at all.) -/
theorem exists_heightConstant :
    ∃ c ∈ Set.Icc (2 : ℝ) (2 * Real.exp 1), c * Real.log (2 * Real.exp 1 / c) = 1 := by
  have h2e : (2 : ℝ) ≤ 2 * Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    nlinarith
  have hcont : ContinuousOn (fun c : ℝ => c * Real.log (2 * Real.exp 1 / c) - 1)
      (Set.Icc (2 : ℝ) (2 * Real.exp 1)) := by
    have hne : ∀ c ∈ Set.Icc (2 : ℝ) (2 * Real.exp 1), c ≠ 0 := fun c hc => by
      have : (0:ℝ) < c := lt_of_lt_of_le (by norm_num) hc.1
      exact this.ne'
    have hne' : ∀ c ∈ Set.Icc (2 : ℝ) (2 * Real.exp 1), 2 * Real.exp 1 / c ≠ 0 := fun c hc => by
      have hc0 : (0:ℝ) < c := lt_of_lt_of_le (by norm_num) hc.1
      exact div_ne_zero (by positivity) (hne c hc)
    have hg : ContinuousOn (fun c : ℝ => 2 * Real.exp 1 / c) (Set.Icc (2 : ℝ) (2 * Real.exp 1)) :=
      continuousOn_const.div continuousOn_id hne
    have hlog : ContinuousOn (fun c : ℝ => Real.log (2 * Real.exp 1 / c))
        (Set.Icc (2 : ℝ) (2 * Real.exp 1)) := hg.log hne'
    exact (continuousOn_id.mul hlog).sub continuousOn_const
  have key := intermediate_value_Icc' h2e hcont
  have hf2 : (2 : ℝ) * Real.log (2 * Real.exp 1 / 2) - 1 = 1 := by
    have : (2 : ℝ) * Real.exp 1 / 2 = Real.exp 1 := by ring
    rw [this, Real.log_exp]; ring
  have hf2e : (2 * Real.exp 1) * Real.log (2 * Real.exp 1 / (2 * Real.exp 1)) - 1 = -1 := by
    have hne : (2 * Real.exp 1 : ℝ) ≠ 0 := by positivity
    rw [div_self hne, Real.log_one]; ring
  have h0mem : (0:ℝ) ∈ Set.Icc
      ((fun c : ℝ => c * Real.log (2 * Real.exp 1 / c) - 1) (2 * Real.exp 1))
      ((fun c : ℝ => c * Real.log (2 * Real.exp 1 / c) - 1) 2) := by
    simp only [hf2, hf2e]; norm_num
  obtain ⟨c, hc, hfc⟩ := key h0mem
  refine ⟨c, hc, ?_⟩
  have : c * Real.log (2 * Real.exp 1 / c) - 1 = 0 := hfc
  linarith

end BST

end AlgoDesign.Searching
