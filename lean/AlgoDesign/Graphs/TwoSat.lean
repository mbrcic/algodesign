/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc
public import Mathlib.Data.Nat.Bitwise

/-!
# 2-SAT: a rule per group

Sources: the Graphs chapter, "Knots"; Aspvall, Plass and Tarjan, *A linear-time algorithm for
testing the truth of certain quantified boolean formulas* (1979), p. 122, the procedure; the
parity of the answer as cp-algorithms' 2-SAT page states it.

Literal `2 i` is `xᵢ` and `2 i + 1` is `¬xᵢ`, so a literal's negation is the literal xor 1. A
clause `(a ∨ b)` gives two arrows, `¬a → b` and `¬b → a`: "if this is false, that must be true".
A clause `(x ∨ x)` gives two parallel arrows, and `(x ∨ ¬x)` two loops; both are accepted.

**The rule**, read off any grouping of the arrows' graph: the formula is unsatisfiable if some
`xᵢ` and `¬xᵢ` share a group, and the smallest such `i` is reported; otherwise `xᵢ` is true
exactly when `xᵢ`'s group has the larger id.

[proved] `satisfies_of_rule`: if the rule answers an assignment from a grouping whose ids never
fall along an arrow (as ids in topological order never do: `gid_le_of_arrow`), the assignment
satisfies every clause. [proved] `not_satisfiable_of_mutual`: if some `xᵢ` and `¬xᵢ` reach each
other, no assignment satisfies the formula, so `not_satisfiable_of_rule`: the rule's `Unsat`
answer is right on the strong components. `twoSat` runs the rule on Algorithm T's grouping;
`twoSat_spec` proves it right from Algorithm T's promise (`algorithmTPromise`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.TwoSat

open Relation Scc

/-- A literal's negation: `2 i` and `2 i + 1` swap. -/
def neg (l : ℕ) : ℕ := l ^^^ 1

/-- The value of literal `l` under an assignment, `xᵢ` being the assignment's entry `i`. -/
def value (a : List Bool) (l : ℕ) : Bool :=
  if l % 2 = 0 then a.getD (l / 2) false else !a.getD (l / 2) false

/-- An assignment satisfies a formula: each clause has a true literal. -/
def Satisfies (a : List Bool) (clauses : List (ℕ × ℕ)) : Prop :=
  ∀ cl ∈ clauses, value a cl.1 = true ∨ value a cl.2 = true

instance (a : List Bool) (clauses : List (ℕ × ℕ)) : Decidable (Satisfies a clauses) := by
  unfold Satisfies; infer_instance

/-- **The graph of implications** on the `2 n` literals of `n` variables: a clause `(a ∨ b)` gives
the arrows `¬a → b` and `¬b → a`, in that order. -/
def implications (n : ℕ) (clauses : List (ℕ × ℕ)) : Digraph :=
  ⟨2 * n, clauses.flatMap fun cl => [(neg cl.1, cl.2), (neg cl.2, cl.1)]⟩

/-- **The rule**, read off a grouping of the graph of implications: `Sum.inl i` for the smallest
`i` whose `xᵢ` and `¬xᵢ` share a group (unsatisfiable), else `Sum.inr` the assignment with `xᵢ`
true exactly when `xᵢ`'s group has the larger id. -/
def rule (n : ℕ) (c : List ℕ) : ℕ ⊕ List Bool :=
  match (List.range n).find? fun i => gid c (2 * i) = gid c (2 * i + 1) with
  | some i => .inl i
  | none => .inr ((List.range n).map fun i => gid c (2 * i + 1) < gid c (2 * i))

/-! ## Negation -/

theorem neg_of_even {l : ℕ} (h : l % 2 = 0) : neg l = l + 1 :=
  Nat.xor_one_of_even (Nat.even_iff.mpr h)

theorem neg_of_odd {l : ℕ} (h : l % 2 = 1) : neg l = l - 1 :=
  Nat.xor_one_of_odd (Nat.odd_iff.mpr h)

/-- A literal's negation has the opposite value. -/
theorem value_neg (a : List Bool) (l : ℕ) : value a (neg l) = !value a l := by
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · rw [neg_of_even h]
    have h1 : (l + 1) % 2 = 1 := by omega
    have h2 : (l + 1) / 2 = l / 2 := by omega
    simp [value, h, h1, h2]
  · rw [neg_of_odd h]
    have h1 : (l - 1) % 2 = 0 := by omega
    have h2 : (l - 1) / 2 = l / 2 := by omega
    simp [value, h, h1, h2]

/-! ## Unsatisfiable when a variable and its negation reach each other -/

theorem mem_implications {n : ℕ} {clauses : List (ℕ × ℕ)} {x y : ℕ} :
    (implications n clauses).Arrow x y ↔
      ∃ cl ∈ clauses, (x = neg cl.1 ∧ y = cl.2) ∨ (x = neg cl.2 ∧ y = cl.1) := by
  simp only [Digraph.Arrow, implications, List.mem_flatMap, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false]

/-- Along an arrow, a satisfying assignment never goes from true to false. -/
theorem value_of_arrow {n : ℕ} {clauses : List (ℕ × ℕ)} {a : List Bool} (ha : Satisfies a clauses)
    {x y : ℕ} (hxy : (implications n clauses).Arrow x y) (hx : value a x = true) :
    value a y = true := by
  obtain ⟨cl, hcl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := mem_implications.mp hxy
  · rw [value_neg] at hx
    rcases ha cl hcl with h | h
    · simp [h] at hx
    · exact h
  · rw [value_neg] at hx
    rcases ha cl hcl with h | h
    · exact h
    · simp [h] at hx

theorem value_of_reaches {n : ℕ} {clauses : List (ℕ × ℕ)} {a : List Bool}
    (ha : Satisfies a clauses) {x y : ℕ} (hxy : (implications n clauses).Reaches x y)
    (hx : value a x = true) : value a y = true := by
  induction hxy with
  | refl => exact hx
  | tail _ hbc ih => exact value_of_arrow ha hbc ih

/-- **If some `xᵢ` and `¬xᵢ` reach each other, no assignment satisfies the formula.** -/
theorem not_satisfiable_of_mutual {n : ℕ} {clauses : List (ℕ × ℕ)} {i : ℕ}
    (h : Mutual (implications n clauses) (2 * i) (2 * i + 1)) :
    ¬ ∃ a, Satisfies a clauses := by
  rintro ⟨a, ha⟩
  have hn : neg (2 * i) = 2 * i + 1 := neg_of_even (by omega)
  cases hv : value a (2 * i)
  · have : value a (2 * i + 1) = true := by rw [← hn, value_neg, hv]; rfl
    rw [value_of_reaches ha h.2 this] at hv
    exact Bool.noConfusion hv
  · have := value_of_reaches ha h.1 hv
    rw [← hn, value_neg, hv] at this
    exact Bool.noConfusion this

/-- **The rule's `Unsat` answer is right** on the strong components; it names the smallest
variable sharing a group with its negation. -/
theorem not_satisfiable_of_rule {n : ℕ} {clauses : List (ℕ × ℕ)} {c : List ℕ}
    (hs : IsSccPartition (implications n clauses) c) {i : ℕ} (h : rule n c = .inl i) :
    (¬ ∃ a, Satisfies a clauses) ∧ i < n ∧
      ∀ j < i, gid c (2 * j) ≠ gid c (2 * j + 1) := by
  unfold rule at h
  split at h
  · rename_i j hj
    cases h
    obtain ⟨hp, hlt, hfirst⟩ := List.find?_range_eq_some.mp hj
    simp only [decide_eq_true_eq, List.mem_range] at hp hlt
    refine ⟨not_satisfiable_of_mutual ((hs.2 _ ?_ _ ?_).mp hp), hlt, fun k hk => ?_⟩
    · simp only [implications]; omega
    · simp only [implications]; omega
    · simpa using hfirst k hk
  · cases h

/-! ## The rule's assignment satisfies every clause -/

/-- Ids in topological order never fall along an arrow. -/
theorem gid_le_of_arrow {g : Digraph} {c : List ℕ} (h : IdsTopological g c) {x y : ℕ}
    (hxy : g.Arrow x y) : gid c x ≤ gid c y := by
  by_cases hne : gid c x = gid c y
  · exact hne.le
  · exact (h _ (mem_quotient_arrows.mpr ⟨x, y, hxy, hne, rfl⟩)).le

/-- Under the rule's assignment, a literal is true exactly when its group's id is larger than its
negation's; the two ids differ. -/
theorem value_rule {n : ℕ} {c : List ℕ} (hne : ∀ i < n, gid c (2 * i) ≠ gid c (2 * i + 1))
    {l : ℕ} (hl : l < 2 * n) :
    (value ((List.range n).map fun i => decide (gid c (2 * i + 1) < gid c (2 * i))) l = true ↔
      gid c (neg l) < gid c l) ∧ gid c l ≠ gid c (neg l) := by
  obtain ⟨i, rfl | rfl⟩ : ∃ i, l = 2 * i ∨ l = 2 * i + 1 := ⟨l / 2, by omega⟩
  · have hi : i < n := by omega
    have hn : neg (2 * i) = 2 * i + 1 := neg_of_even (by omega)
    have h1 : 2 * i % 2 = 0 := by omega
    have h2 : 2 * i / 2 = i := by omega
    rw [hn]
    simp only [value, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some, ite_true, decide_eq_true_eq]
    exact ⟨trivial, hne i hi⟩
  · have hi : i < n := by omega
    have hn : neg (2 * i + 1) = 2 * i := by rw [neg_of_odd (by omega)]; omega
    have h1 : (2 * i + 1) % 2 = 1 := by omega
    have h2 : (2 * i + 1) / 2 = i := by omega
    rw [hn]
    simp only [value, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some, one_ne_zero, ite_false,
      Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    exact ⟨⟨fun h => lt_of_le_of_ne h (hne i hi), le_of_lt⟩, (hne i hi).symm⟩

/-- **The rule's assignment satisfies every clause**, read off any grouping whose ids never fall
along an arrow: two false literals `a`, `b` in one clause would give
`id a < id ¬a ≤ id b < id ¬b ≤ id a`. -/
theorem satisfies_of_rule {n : ℕ} {clauses : List (ℕ × ℕ)} {c : List ℕ}
    (hlits : ∀ cl ∈ clauses, cl.1 < 2 * n ∧ cl.2 < 2 * n)
    (hmono : ∀ x y, (implications n clauses).Arrow x y → gid c x ≤ gid c y) {a : List Bool}
    (h : rule n c = .inr a) : Satisfies a clauses := by
  unfold rule at h
  split at h
  · cases h
  · rename_i hnone
    cases h
    have hne : ∀ i < n, gid c (2 * i) ≠ gid c (2 * i + 1) := by
      intro i hi heq
      have := List.find?_eq_none.mp hnone i (List.mem_range.mpr hi)
      simp [heq] at this
    intro cl hcl
    obtain ⟨h1, h2⟩ := hlits cl hcl
    obtain ⟨hv1, hn1⟩ := value_rule hne h1
    obtain ⟨hv2, hn2⟩ := value_rule hne h2
    rw [hv1, hv2]
    by_contra hcon
    push Not at hcon
    have a1 := hmono _ _ (mem_implications.mpr ⟨cl, hcl, Or.inl ⟨rfl, rfl⟩⟩)
    have a2 := hmono _ _ (mem_implications.mpr ⟨cl, hcl, Or.inr ⟨rfl, rfl⟩⟩)
    have := lt_of_le_of_ne hcon.1 hn1
    have := lt_of_le_of_ne hcon.2 hn2
    omega

/-- The same, for a grouping with ids in topological order. -/
theorem satisfies_of_rule_topological {n : ℕ} {clauses : List (ℕ × ℕ)} {c : List ℕ}
    (hlits : ∀ cl ∈ clauses, cl.1 < 2 * n ∧ cl.2 < 2 * n)
    (ht : IdsTopological (implications n clauses) c) {a : List Bool} (h : rule n c = .inr a) :
    Satisfies a clauses :=
  satisfies_of_rule hlits (fun _ _ hxy => gid_le_of_arrow ht hxy) h

/-! ## 2-SAT by Algorithm T -/

/-- **2-SAT**: the rule, read off Algorithm T's grouping of the graph of implications. -/
def twoSat (n : ℕ) (clauses : List (ℕ × ℕ)) : ℕ ⊕ List Bool :=
  rule n (algorithmT (implications n clauses)).groupOf

/-- **2-SAT is right**: on clauses over `n` variables, an assignment it answers satisfies every
clause; an `Unsat i` answer means no assignment does, `i < n`, and no smaller variable shares a
group with its negation. -/
theorem twoSat_spec {n : ℕ} {clauses : List (ℕ × ℕ)}
    (hlits : ∀ cl ∈ clauses, cl.1 < 2 * n ∧ cl.2 < 2 * n) :
    (∀ a, twoSat n clauses = .inr a → Satisfies a clauses) ∧
      ∀ i, twoSat n clauses = .inl i → (¬ ∃ a, Satisfies a clauses) ∧ i < n ∧
        ∀ j < i, gid (algorithmT (implications n clauses)).groupOf (2 * j) ≠
          gid (algorithmT (implications n clauses)).groupOf (2 * j + 1) := by
  have hg : (implications n clauses).WellFormed := by
    intro a ha
    simp only [implications, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at ha
    obtain ⟨cl, hcl, rfl | rfl⟩ := ha
    · have := hlits cl hcl
      rcases Nat.mod_two_eq_zero_or_one cl.1 with h | h
      · rw [neg_of_even h]; simp only [implications]; omega
      · rw [neg_of_odd h]; simp only [implications]; omega
    · have := hlits cl hcl
      rcases Nat.mod_two_eq_zero_or_one cl.2 with h | h
      · rw [neg_of_even h]; simp only [implications]; omega
      · rw [neg_of_odd h]; simp only [implications]; omega
  obtain ⟨hs, ht, -⟩ := algorithmTPromise _ hg
  exact ⟨fun a h => satisfies_of_rule_topological hlits ht h,
    fun i h => not_satisfiable_of_rule hs h⟩

/-- `(x₀ ∨ x₀)`: two parallel arrows `¬x₀ → x₀`; `x₀` true. -/
example : twoSat 1 [(0, 0)] = .inr [true] := by decide

/-- `(x₀ ∨ ¬x₀)`: two loops; satisfiable. -/
example : (twoSat 1 [(0, 1)]).isRight = true := by decide

/-- `(x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀)`: `x₀` and `¬x₀` reach each other; unsatisfiable at `x₀`. -/
example : twoSat 1 [(0, 0), (1, 1)] = .inl 0 := by decide

end AlgoDesign.Graphs.TwoSat
