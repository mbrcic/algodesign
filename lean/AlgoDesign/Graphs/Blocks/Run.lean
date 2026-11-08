/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.StepShape
public import AlgoDesign.Graphs.Blocks.Final
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Bridges, cut vertices and blocks: the walk finishes within its fuel

The rows hold two entries per link, `2 m` in all (`sum_length_adj`). Each step that is not the
last moves the outer loop on, takes a row entry, or finishes a vertex, so it lowers by one the
number of vertices the outer loop has still to pass plus, for each vertex not yet finished, the
entries of its row still to take and one for its finish (`measure_step`). That number starts at
`2 n + 2 m`, the walk's fuel `steps`, so the walk has finished when the fuel runs out
(`done_final`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable {g : Graph}

theorem list_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem length_entries (v y i : ℕ) : (g.entries v y i).length =
    (if g.links[i]? = some (v, y) then 1 else 0) +
      (if g.links[i]? = some (y, v) then 1 else 0) := by
  unfold Graph.entries
  rcases g.links[i]? with _ | ⟨a, b⟩
  · simp
  · simp only [Option.some.injEq, Prod.mk.injEq, List.length_append]
    split_ifs <;> (try simp only [List.length_singleton, List.length_nil]) <;>
      first | rfl | omega

/-- **The rows hold two entries per link.** -/
theorem sum_length_adj (hg : g.WellFormed) :
    ((List.range g.n).map fun v => (g.adj v).length).sum = 2 * g.links.length := by
  have hadj : ∀ v, (g.adj v).length = ∑ y ∈ Finset.range g.n, ∑ i ∈ Finset.range g.links.length,
      (g.entries v y i).length := by
    intro v
    simp only [Graph.adj, List.length_flatMap, List.length_map]
    rw [list_sum_range]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [list_sum_range]
  simp only [hadj, length_entries]
  rw [list_sum_range]
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_comm, Finset.sum_comm]
  rw [show 2 * g.links.length = ∑ _i ∈ Finset.range g.links.length, 2 by simp [mul_comm]]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  obtain ⟨⟨a, b⟩, hab⟩ : ∃ l, g.links[i]? = some l := ⟨_, List.getElem?_eq_getElem hi⟩
  have han : a < g.n := (hg _ (List.mem_of_getElem? hab)).1
  have hbn : b < g.n := (hg _ (List.mem_of_getElem? hab)).2
  simp only [hab, Option.some.injEq, Prod.mk.injEq, Finset.sum_add_distrib]
  simp [ite_and, Finset.sum_ite_eq, han, hbn]

variable (g) in
/-- What the walk has still to do: vertices the outer loop has still to pass, and for each vertex
not yet finished, the entries of its row still to take and one for its finish. -/
def measure (w : Walk) : ℕ :=
  (g.n - w.next) + ((List.range g.n).map fun x =>
    if w.finished x then 0 else (g.adj x).length - w.taken x + 1).sum

theorem sum_update {n v : ℕ} (hv : v < n) {f f' : ℕ → ℕ} (h : ∀ x, x ≠ v → f' x = f x)
    (hv' : f' v + 1 = f v) : ((List.range n).map f').sum + 1 = ((List.range n).map f).sum := by
  rw [list_sum_range, list_sum_range, ← Finset.add_sum_erase _ f' (Finset.mem_range.mpr hv),
    ← Finset.add_sum_erase _ f (Finset.mem_range.mpr hv)]
  have : ∑ x ∈ (Finset.range n).erase v, f' x = ∑ x ∈ (Finset.range n).erase v, f x :=
    Finset.sum_congr rfl fun x hx => h x (Finset.ne_of_mem_erase hx)
  rw [this]
  omega

theorem measure_core (w : Walk) : measure g (core w) = measure g w := rfl

section Shape

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

omit hO in
/-- The top frame's vertex takes its next entry. -/
theorem measure_tick {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame} {s : ℕ × ℕ}
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hs : (g.adj v)[i]? = some s) :
    measure g (tick w v arr i rest) + 1 = measure g w := by
  obtain ⟨-, -, -, hall⟩ := hS.2.1
  obtain ⟨hvn, -, -, hpos, -⟩ := hall ⟨v, arr, i⟩ (by simp [hp])
  simp only at hpos hvn
  have hnf : w.finished v = false := by
    have := (hS.2.2.1 v hvn).2.1
    have hon : w.onPath v = true := by simp [onPath, hp]
    simpa [hon] using this
  have hlt : i < (g.adj v).length := (List.getElem?_eq_some_iff.mp hs).1
  unfold measure tick
  simp only
  have := sum_update (n := g.n) (v := v) hvn
    (f := fun x => if w.finished x then 0 else (g.adj x).length - w.taken x + 1)
    (f' := fun x => if w.finished x then 0 else (g.adj x).length -
      Function.update w.taken v (i + 1) x + 1)
    (fun x hx => by simp [Function.update_of_ne hx]) (by simp [hnf, ← hpos]; omega)
  omega

omit hO in
/-- The top frame's vertex finishes. -/
theorem measure_pop {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame}
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hs : (g.adj v)[i]? = none) :
    measure g (pop w v rest) + 1 = measure g w := by
  obtain ⟨-, -, -, hall⟩ := hS.2.1
  obtain ⟨hvn, -, -, hpos, hle⟩ := hall ⟨v, arr, i⟩ (by simp [hp])
  simp only at hpos hvn hle
  have hnf : w.finished v = false := by
    have := (hS.2.2.1 v hvn).2.1
    have hon : w.onPath v = true := by simp [onPath, hp]
    simpa [hon] using this
  have hge : (g.adj v).length ≤ i := List.getElem?_eq_none_iff.mp hs
  unfold measure pop
  simp only
  have := sum_update (n := g.n) (v := v) hvn
    (f := fun x => if w.finished x then 0 else (g.adj x).length - w.taken x + 1)
    (f' := fun x => if Function.update w.finished v true x then 0 else
      (g.adj x).length - w.taken x + 1)
    (fun x hx => by simp [Function.update_of_ne hx]) (by simp [hnf]; omega)
  omega

omit hO in
/-- **Each step but the last lowers the measure by one.** -/
theorem measure_step : (w.path = [] ∧ g.n ≤ w.next) ∨ measure g (step g w) + 1 = measure g w := by
  rcases step_cases (g := g) w with ⟨-, hn, -, h⟩ | ⟨-, hn, -, h⟩ | ⟨hp, hn, -⟩ |
    ⟨v, arr, i, rest, x, e, hp, hs, hcase⟩ | ⟨v, arr, i, rest, hp, hs, hc, -⟩
  · right
    rw [h]
    unfold measure newRoot enter
    simp only
    omega
  · right
    rw [h]
    unfold measure
    simp only
    omega
  · exact Or.inl ⟨hp, hn⟩
  · right
    rcases hcase with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · rw [h]
      exact measure_tick hS hp hs
    · rw [← measure_core, h, measure_core]
      exact measure_tick hS hp hs
    · rw [← measure_core, h, measure_core]
      unfold descend enter
      exact measure_tick hS hp hs
  · right
    rw [← measure_core, hc, measure_core]
    exact measure_pop hS hp hs

end Shape

theorem step_of_terminal {w : Walk} (h : w.path = [] ∧ g.n ≤ w.next) : step g w = w := by
  unfold step
  rw [h.1]
  simp only [show ¬ w.next < g.n by omega, ite_false]

theorem run_succ' (k : ℕ) (w : Walk) : run g (k + 1) w = step g (run g k w) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    change run g (k + 1) (step g w) = _
    rw [ih]
    rfl

theorem measure_start (hg : g.WellFormed) : measure g (start g) = steps g := by
  unfold measure steps start
  simp only [Bool.false_eq_true, ite_false, Nat.sub_zero]
  have : ((List.range g.n).map fun x => (g.adj x).length + 1).sum =
      ((List.range g.n).map fun x => (g.adj x).length).sum + g.n := by
    rw [list_sum_range, list_sum_range, Finset.sum_add_distrib]
    simp
  rw [this, sum_length_adj hg]
  omega

/-- **The walk finishes within its fuel**, given that every state of the run keeps its shape. -/
theorem done_final (hg : g.WellFormed)
    (hsh : ∀ k, Shape (g := g) (run g k (start g)) ∧ Outside (g := g) (run g k (start g))) :
    Done (g := g) (final g) := by
  have key : ∀ k, ((run g k (start g)).path = [] ∧ g.n ≤ (run g k (start g)).next) ∨
      measure g (run g k (start g)) + k = steps g := by
    intro k
    induction k with
    | zero => exact Or.inr (by simp only [run, Nat.add_zero]; exact measure_start hg)
    | succ k ih =>
      rw [run_succ']
      rcases ih with h | h
      · exact Or.inl (by rw [step_of_terminal h]; exact h)
      · rcases measure_step (hsh k).1 with h' | h'
        · exact Or.inl (by rw [step_of_terminal h']; exact h')
        · exact Or.inr (by omega)
  have hS := (hsh (steps g)).1
  have hnext := hS.2.2.2.2.2.2.1.1
  unfold final
  rcases key (steps g) with h | h
  · exact ⟨h.1, by omega⟩
  · have h0 : measure g (run g (steps g) (start g)) = 0 := by omega
    unfold measure at h0
    have hn : g.n ≤ (run g (steps g) (start g)).next := by omega
    have hfin : ∀ x < g.n, (run g (steps g) (start g)).finished x = true := by
      intro x hx
      by_contra hf
      have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x =>
        if (run g (steps g) (start g)).finished x then 0 else
          (g.adj x).length - (run g (steps g) (start g)).taken x + 1) (List.mem_range.mpr hx))
      simp only [hf, ite_false] at hle
      omega
    refine ⟨?_, by omega⟩
    rcases hp : (run g (steps g) (start g)).path with _ | ⟨fr, rest⟩
    · rfl
    · exfalso
      obtain ⟨-, -, -, hall⟩ := hS.2.1
      have hfr := hall fr (by simp [hp])
      have hon : (run g (steps g) (start g)).onPath fr.vertex = true := by simp [onPath, hp]
      have := (hS.2.2.1 fr.vertex hfr.1).2.1
      exact this ⟨hon, hfin _ hfr.1⟩

end Walk

end AlgoDesign.Graphs.Blocks
