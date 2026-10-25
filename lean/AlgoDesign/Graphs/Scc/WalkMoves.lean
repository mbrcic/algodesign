/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkInv

/-!
# Algorithm T: what each move changes

Coming back over an arrow from `v` to `x` changes only the log of retreats and `v`'s low value and
lead bit (`retreat_low`, `retreat_lead`). It changes one climb-back number: `v`'s becomes the
smaller of `v`'s and `x`'s when the two reach each other (`climbBack_add`); no climb-back number
grows. Entering a vertex `x` changes no other vertex's climb-back number, and gives `x` its own
entry number (`climbBack_previsit`). The facts on arrows come back over only grow with the log.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-! ## Coming back over an arrow -/

section Retreat

variable (w : Walk) (v x : ℕ)

@[simp] theorem retreat_pre : (retreat w v x).pre = w.pre := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_time : (retreat w v x).time = w.time := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_path : (retreat w v x).path = w.path := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_followers : (retreat w v x).followers = w.followers := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_groups : (retreat w v x).groups = w.groups := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_emitted : (retreat w v x).emitted = w.emitted := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_next : (retreat w v x).next = w.next := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_finished : (retreat w v x).finished = w.finished := by
  unfold retreat; dsimp only; split <;> rfl

@[simp] theorem retreat_retreats : (retreat w v x).retreats = w.retreats ++ [(v, x)] := by
  unfold retreat; dsimp only; split <;> rfl

theorem retreat_low :
    (retreat w v x).low = if w.low x < w.low v then Function.update w.low v (w.low x)
      else w.low := by
  unfold retreat; dsimp only; split <;> rfl

theorem retreat_lead :
    (retreat w v x).lead = if w.low x < w.low v then Function.update w.lead v false
      else w.lead := by
  unfold retreat; dsimp only; split <;> rfl

theorem retreat_low_apply (y : ℕ) :
    (retreat w v x).low y = if y = v then min (w.low v) (w.low x) else w.low y := by
  rw [retreat_low]
  by_cases hy : y = v
  · subst hy
    split_ifs with h1 <;> simp [Function.update_self] <;> omega
  · split_ifs <;> simp [Function.update_of_ne hy]

theorem retreat_lead_apply (y : ℕ) :
    (retreat w v x).lead y = if y = v ∧ w.low x < w.low v then false else w.lead y := by
  rw [retreat_lead]
  by_cases hy : y = v
  · subst hy
    split_ifs <;> simp_all
  · split_ifs <;> simp_all

end Retreat

/-- Adding a retreat from `v` to `x` to the log changes only `v`'s list, by `x`'s, when the two
reach each other. -/
theorem mem_reachList_add {log : List (ℕ × ℕ)} {v x y z : ℕ} :
    z ∈ reachList g (log ++ [(v, x)]) (log ++ [(v, x)]).length y ↔
      z ∈ reachList g log log.length y ∨
        (y = v ∧ Mutual g v x ∧ v < g.n ∧ z ∈ reachList g log log.length x) := by
  rw [List.length_append, List.length_singleton, mem_reachList_succ, List.getElem?_concat_length]
  simp only [reachList_append _ le_rfl, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨hy, h | ⟨y', ⟨rfl, rfl⟩, hm, hz⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, hm, hy, hz⟩
  · rintro (h | ⟨rfl, hm, hy, hz⟩)
    · exact ⟨lt_of_mem_reachList h, Or.inl h⟩
    · exact ⟨hy, Or.inr ⟨x, ⟨rfl, rfl⟩, hm, hz⟩⟩

/-- **A retreat's climb-back numbers**: `v`'s becomes the smaller of `v`'s and `x`'s when they
reach each other; no other changes. -/
theorem climbBack_add {w w' : Walk} {v x : ℕ} (hp : w'.pre = w.pre)
    (hr : w'.retreats = w.retreats ++ [(v, x)]) (hx : x < g.n) (y : ℕ) :
    climbBack (g := g) w' y = if y = v ∧ Mutual g v x ∧ v < g.n then
      min (climbBack (g := g) w v) (climbBack (g := g) w x) else climbBack (g := g) w y := by
  apply eq_of_forall_le_iff
  intro k
  rw [le_climbBack_iff, hp, hr]
  simp only [mem_reachList_add]
  split_ifs with hc
  · obtain ⟨rfl, hm, hv⟩ := hc
    rw [le_min_iff, le_climbBack_iff, le_climbBack_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun z hz => h2 z (Or.inl hz)⟩,
        ⟨h2 x (Or.inr ⟨rfl, hm, hv, self_mem_reachList hx _⟩),
          fun z hz => h2 z (Or.inr ⟨rfl, hm, hv, hz⟩)⟩⟩
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      exact ⟨h1, fun z hz => hz.elim (h2 z) fun hz => h3 z hz.2.2.2⟩
  · rw [le_climbBack_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun z hz => h2 z (Or.inl hz)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun z hz => hz.elim (h2 z) fun hz' => absurd ⟨hz'.1, hz'.2.1, hz'.2.2.1⟩ hc⟩

theorem climbBack_add_le {w w' : Walk} {v x : ℕ} (hp : w'.pre = w.pre)
    (hr : w'.retreats = w.retreats ++ [(v, x)]) (hx : x < g.n) (y : ℕ) :
    climbBack (g := g) w' y ≤ climbBack (g := g) w y := by
  rw [climbBack_add hp hr hx]
  split_ifs with hc
  · obtain ⟨rfl, -⟩ := hc
    exact min_le_left _ _
  · exact le_rfl

theorem climbBack_add_of_ne {w w' : Walk} {v x : ℕ} (hp : w'.pre = w.pre)
    (hr : w'.retreats = w.retreats ++ [(v, x)]) (hx : x < g.n) {y : ℕ} (hy : y ≠ v) :
    climbBack (g := g) w' y = climbBack (g := g) w y := by
  rw [climbBack_add hp hr hx]
  simp [hy]

theorem climbBack_add_of_not_mutual {w w' : Walk} {v x : ℕ} (hp : w'.pre = w.pre)
    (hr : w'.retreats = w.retreats ++ [(v, x)]) (hx : x < g.n) (hm : ¬ Mutual g v x) (y : ℕ) :
    climbBack (g := g) w' y = climbBack (g := g) w y := by
  rw [climbBack_add hp hr hx]
  simp [hm]

theorem climbBack_add_self {w w' : Walk} {v x : ℕ} (hp : w'.pre = w.pre)
    (hr : w'.retreats = w.retreats ++ [(v, x)]) (hx : x < g.n) (hm : Mutual g v x)
    (hv : v < g.n) :
    climbBack (g := g) w' v = min (climbBack (g := g) w v) (climbBack (g := g) w x) := by
  rw [climbBack_add hp hr hx]
  simp [hm, hv]

/-! ## The facts on arrows come back over only grow with the log -/

theorem RowRetreated.mono {log log' : List (ℕ × ℕ)} (hl : ∀ a ∈ log, a ∈ log') {v k : ℕ}
    (h : RowRetreated g log v k) : RowRetreated g log' v k :=
  fun j hj e he => hl _ (h j hj e he)

theorem RowRetreated.le {log : List (ℕ × ℕ)} {v k k' : ℕ} (h : RowRetreated g log v k)
    (hk : k' ≤ k) : RowRetreated g log v k' :=
  fun j hj e he => h j (by omega) e he

theorem FramesRetreated.mono {log log' : List (ℕ × ℕ)} (hl : ∀ a ∈ log, a ∈ log') :
    ∀ {a : Option ℕ} {s : List (ℕ × ℕ)}, FramesRetreated g log a s → FramesRetreated g log' a s
  | _, [], _ => trivial
  | none, (_, _) :: _, ⟨h1, h2, h3⟩ => ⟨h1, h2.mono hl, FramesRetreated.mono hl h3⟩
  | some _, (_, _) :: _, ⟨h0, h1, h2, h3, h4⟩ =>
    ⟨h0, h1, h2, h3.mono hl, FramesRetreated.mono hl h4⟩

theorem FramesRetreated.le_length {log : List (ℕ × ℕ)} {a : Option ℕ} {v i : ℕ}
    {rest : List (ℕ × ℕ)} (h : FramesRetreated g log a ((v, i) :: rest)) :
    i ≤ (g.out v).length := by
  cases a with
  | none => exact h.1
  | some _ => exact h.2.1

theorem FramesRetreated.tail {log : List (ℕ × ℕ)} {a : Option ℕ} {v i : ℕ}
    {rest : List (ℕ × ℕ)} (h : FramesRetreated g log a ((v, i) :: rest)) :
    FramesRetreated g log (some v) rest := by
  cases a with
  | none => exact h.2.2
  | some _ => exact h.2.2.2.2

/-- Once the walk comes back over the arrow to the vertex above, the frame below is where the walk
left it. -/
theorem FramesRetreated.pop {log : List (ℕ × ℕ)} {v : ℕ} :
    ∀ {s : List (ℕ × ℕ)}, FramesRetreated g log (some v) s →
      FramesRetreated g (log ++ [((s.headD (0, 0)).1, v)]) none s
  | [], _ => trivial
  | (u, j) :: rest, ⟨h0, h1, h2, h3, h4⟩ => by
    refine ⟨h1, fun j' hj' e he => ?_, h4.mono fun a ha => List.mem_append_left _ ha⟩
    by_cases hj : j' < j - 1
    · exact List.mem_append_left _ (h3 j' hj e he)
    · have : j' = j - 1 := by omega
      subst this
      rw [he] at h2
      simp only [Option.map_some, Option.some.injEq] at h2
      simp [← h2]

/-! ## Entering a vertex -/

section Previsit

variable (w : Walk) (x : ℕ)

@[simp] theorem previsit_pre : (previsit w x).pre = Function.update w.pre x (w.time + 1) := rfl
@[simp] theorem previsit_time : (previsit w x).time = w.time + 1 := rfl
@[simp] theorem previsit_low : (previsit w x).low = Function.update w.low x (w.time + 1) := rfl
@[simp] theorem previsit_lead : (previsit w x).lead = Function.update w.lead x true := rfl
@[simp] theorem previsit_path : (previsit w x).path = (x, 0) :: w.path := rfl
@[simp] theorem previsit_followers : (previsit w x).followers = w.followers := rfl
@[simp] theorem previsit_groups : (previsit w x).groups = w.groups := rfl
@[simp] theorem previsit_emitted : (previsit w x).emitted = w.emitted := rfl
@[simp] theorem previsit_next : (previsit w x).next = w.next := rfl
@[simp] theorem previsit_finished : (previsit w x).finished = w.finished := rfl
@[simp] theorem previsit_retreats : (previsit w x).retreats = w.retreats := rfl

end Previsit

/-- Entering `x`, whose entry number was `0` and which heads no retreat, changes no other
vertex's climb-back number. -/
theorem climbBack_previsit_of_ne {w : Walk} {x : ℕ} (hx : ∀ a ∈ w.retreats, a.2 ≠ x) {y : ℕ}
    (hy : y ≠ x) : climbBack (g := g) (previsit w x) y = climbBack (g := g) w y := by
  refine climbBack_congr rfl (by simp [Function.update_of_ne hy]) fun z hz => ?_
  have : z ≠ x := by
    rcases head_of_mem_reachList hz with rfl | ⟨a, ha⟩
    · exact hy
    · exact hx _ ha
  simp [Function.update_of_ne this]

/-- A vertex that starts no retreat climbs back to its own entry number. -/
theorem climbBack_of_no_source {w : Walk} {x : ℕ} (hx : ∀ a ∈ w.retreats, a.1 ≠ x) :
    climbBack (g := g) w x = w.pre x := by
  refine le_antisymm (climbBack_le_pre w x) (le_climbBack_iff.2 ⟨le_rfl, fun z hz => ?_⟩)
  rcases source_of_mem_reachList hz with rfl | ⟨y, hy⟩
  · exact le_rfl
  · exact absurd rfl (hx _ hy)

end AlgorithmT

end AlgoDesign.Graphs.Scc
