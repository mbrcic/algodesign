/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Inv
public import AlgoDesign.Graphs.Blocks.CycleTheory

/-!
# Bridges, cut vertices and blocks: the walk's tree

What `Shape` says about the tree the walk grows: `Above a x`, `a` is `x` or above it, read by
following arrival links up; `Anc`, which follows them with fuel, says the same; vertices above a
vertex were entered before it, and the vertices above one vertex stand in a line. Open vertices have
only open vertices above them, so everything below a finished vertex has finished. The climb-back
number is the least of the entry numbers it reads, and is one of them.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

open Relation

variable {g : Graph}

/-- `a` is `x` or above it in the walk's tree: following arrival links up from `x` reaches `a`. -/
def Above (w : Walk) (a x : ℕ) : Prop :=
  ReflTransGen (fun y z => w.arrival z ≠ none ∧ w.up z = y) a x

theorem Above.refl (w : Walk) (x : ℕ) : Above w x x := ReflTransGen.refl

theorem Above.trans {w : Walk} {a b x : ℕ} (h₁ : Above w a b) (h₂ : Above w b x) : Above w a x :=
  ReflTransGen.trans h₁ h₂

theorem Above.up {w : Walk} {x : ℕ} (h : w.arrival x ≠ none) : Above w (w.up x) x :=
  ReflTransGen.single ⟨h, rfl⟩

/-- Above `x` is `x` itself or something above the vertex it hangs from. -/
theorem above_iff {w : Walk} {a x : ℕ} :
    Above w a x ↔ a = x ∨ (w.arrival x ≠ none ∧ Above w a (w.up x)) := by
  constructor
  · intro h
    rcases ReflTransGen.cases_tail h with h | ⟨y, hy, ⟨hx, rfl⟩⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hx, hy⟩
  · rintro (rfl | ⟨hx, h⟩)
    · exact Above.refl w a
    · exact h.trans (Above.up hx)

/-- With enough fuel, `chain` lists exactly the vertices above. -/
theorem mem_chain_iff {w : Walk}
    (hfuel : ∀ x, w.arrival x ≠ none → w.entry (w.up x) < w.entry x)
    (hpos : ∀ x, w.arrival x ≠ none → w.entry (w.up x) ≠ 0) :
    ∀ (k x a : ℕ), w.entry x ≤ k + 1 → (a ∈ chain w k x ↔ Above w a x)
  | 0, x, a, hk => by
    simp only [chain, List.mem_singleton]
    constructor
    · rintro rfl
      exact Above.refl w a
    · intro h
      rcases above_iff.mp h with h | ⟨hx, -⟩
      · exact h
      · have := hfuel x hx
        have := hpos x hx
        omega
  | k + 1, x, a, hk => by
    rw [above_iff]
    simp only [chain]
    rcases hx : w.arrival x with _ | e
    · simp
    · have h1 := hfuel x (by simp [hx])
      simp only [List.mem_cons, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      rw [mem_chain_iff hfuel hpos k (w.up x) a (by omega)]

/-! ## What the shape gives -/

section Shape

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
include hS hO

/-- A vertex hanging from another was entered after it, and both are vertices of the graph. -/
theorem hangs (x : ℕ) (hx : w.arrival x ≠ none) :
    x < g.n ∧ w.entry x ≠ 0 ∧ w.up x < g.n ∧ w.entry (w.up x) ≠ 0 ∧
      w.entry (w.up x) < w.entry x ∧ ∀ e ∈ w.arrival x, Joins g e (w.up x) x := by
  have hxn : x < g.n := by
    by_contra h
    exact hx (hO x (by omega)).2.2.2.2
  have hxe : w.entry x ≠ 0 := fun h0 => hx ((hS.2.2.1 x hxn).2.2.2 h0).2
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hx
  have ht := hS.2.2.2.1 x hxn hxe e (by simp [he])
  exact ⟨hxn, hxe, ht.2.1, ht.2.2.1, ht.2.2.2, fun e' he' => by
    rw [he] at he'
    cases he'
    exact ht.1⟩

/-- `Anc`, read with fuel, is `Above`. -/
theorem anc_iff (a x : ℕ) : Anc (g := g) w a x ↔ Above w a x := by
  unfold Anc
  have hfuel : ∀ x, w.arrival x ≠ none → w.entry (w.up x) < w.entry x :=
    fun x hx => (hangs hS hO x hx).2.2.2.2.1
  have hpos : ∀ x, w.arrival x ≠ none → w.entry (w.up x) ≠ 0 :=
    fun x hx => (hangs hS hO x hx).2.2.2.1
  refine mem_chain_iff hfuel hpos g.n x a ?_
  by_cases hx : x < g.n
  · have := hS.1.1 x hx
    have : w.time ≤ g.n := by
      rw [hS.1.2.2]
      exact (List.length_filter_le _ _).trans (by simp)
    omega
  · rw [(hO x (by omega)).1]
    omega

/-- Above an entered vertex are entered vertices, entered no later. -/
theorem entry_le_of_above {a x : ℕ} (h : Above w a x) (hx : w.entry x ≠ 0) :
    w.entry a ≠ 0 ∧ w.entry a ≤ w.entry x ∧ (a ≠ x → w.entry a < w.entry x) := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨hx, le_rfl, fun h => absurd rfl h⟩
  | @head b c hst _ ih =>
    obtain ⟨hc, rfl⟩ := hst
    obtain ⟨-, -, -, h1, h2, -⟩ := hangs hS hO c hc
    obtain ⟨i1, i2, -⟩ := ih
    refine ⟨h1, by omega, fun _ => by omega⟩

omit hS hO in
/-- Two vertices above one are one above the other. -/
theorem above_total {a b x : ℕ} (ha : Above w a x) (hb : Above w b x) :
    Above w a b ∨ Above w b a := by
  have key := ReflTransGen.total_of_right_unique
    (r := fun z y => w.arrival z ≠ none ∧ w.up z = y)
    (fun {_ _ _} h1 h2 => h1.2.symm.trans h2.2) ha.swap hb.swap
  rcases key with h | h
  · exact Or.inr h.swap
  · exact Or.inl h.swap

theorem above_antisymm {a b : ℕ} (h₁ : Above w a b) (h₂ : Above w b a) : a = b := by
  by_contra hne
  rcases Nat.eq_zero_or_pos (w.entry b) with hb | hb
  · rcases above_iff.mp h₁ with h | ⟨hb', -⟩
    · exact hne h
    · exact (hangs hS hO b hb').2.1 hb
  · obtain ⟨ha, -, h3⟩ := entry_le_of_above hS hO h₁ (by omega)
    have := (entry_le_of_above hS hO h₂ ha).2.1
    have := h3 hne
    omega

omit hS hO in
/-- Nothing is above a root but itself. -/
theorem above_root {a x : ℕ} (hx : w.arrival x = none) (h : Above w a x) : a = x := by
  rcases above_iff.mp h with h | ⟨h, -⟩
  · exact h
  · exact absurd hx h

omit hS hO in
theorem onPath_iff (x : ℕ) : w.onPath x = true ↔ ∃ fr ∈ w.path, fr.vertex = x := by
  simp [onPath]

omit hO in
/-- The frame below an open vertex that is not a root holds the vertex it hangs from. -/
theorem onPath_up {x : ℕ} (hx : w.onPath x = true) (ha : w.arrival x ≠ none) :
    w.onPath (w.up x) = true := by
  rw [onPath_iff] at hx ⊢
  obtain ⟨fr, hfr, rfl⟩ := hx
  obtain ⟨-, hch, hlast, hall⟩ := hS.2.1
  have key : ∀ l : List Frame, l.IsChain (Hangs (g := g) w) →
      (∀ fr ∈ l.getLast?, fr.arrival = none) → (∀ fr ∈ l, w.arrival fr.vertex = fr.arrival) →
      ∀ fr ∈ l, w.arrival fr.vertex ≠ none → ∃ fr' ∈ l, fr'.vertex = w.up fr.vertex := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hc hl ha fr hfr hne
      rcases l with _ | ⟨b, l⟩
      · simp only [List.mem_singleton] at hfr
        subst hfr
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq,
          forall_eq'] at hl
        exact absurd ((ha _ (by simp)).trans hl) hne
      · rw [List.isChain_cons_cons] at hc
        rcases List.mem_cons.mp hfr with rfl | hfr
        · exact ⟨b, by simp, hc.1.2.1.symm⟩
        · obtain ⟨fr', h1, h2⟩ := ih hc.2 (by simpa [List.getLast?_cons_cons] using hl)
            (fun f hf => ha f (List.mem_cons_of_mem _ hf)) fr hfr hne
          exact ⟨fr', List.mem_cons_of_mem _ h1, h2⟩
  exact key w.path hch hlast (fun f hf => (hall f hf).2.2.1) fr hfr ha

omit hO in
/-- Above an open vertex are only open vertices. -/
theorem onPath_of_above {a x : ℕ} (h : Above w a x) (hx : w.onPath x = true) :
    w.onPath a = true := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih =>
    obtain ⟨hc, rfl⟩ := hbc
    exact ih (onPath_up hS hx hc)

/-- Below a finished vertex every entered vertex has finished. -/
theorem finished_of_above {a x : ℕ} (h : Above w a x) (ha : w.finished a = true)
    (hx : w.entry x ≠ 0) : w.finished x = true := by
  have hxn : x < g.n := by
    by_contra hn
    exact hx (hO x (by omega)).1
  rcases ((hS.2.2.1 x hxn).1.mp hx) with hp | hf
  · have hpa := onPath_of_above hS h hp
    have han : a < g.n := by
      by_contra hn
      have := (hO a (by omega)).2.2.1
      simp_all
    exact absurd ⟨hpa, ha⟩ (hS.2.2.1 a han).2.1
  · exact hf

omit hS hO in
/-- Between a vertex and one above it, a vertex hanging from the upper one. -/
theorem exists_child_of_above {a x : ℕ} (h : Above w a x) (hne : a ≠ x) :
    ∃ y, Above w y x ∧ w.arrival y ≠ none ∧ w.up y = a := by
  rcases ReflTransGen.cases_head h with h | ⟨y, ⟨hy, hya⟩, hyx⟩
  · exact absurd h hne
  · exact ⟨y, hyx, hy, hya⟩

/-! ## Walking up the tree -/

/-- The steps from `x` up to `y`, by arrival links, with fuel `k`. -/
def upSteps (w : Walk) : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _ => []
  | k + 1, x, y =>
    if x = y then []
    else match w.arrival x with
      | some e => (e, w.up x) :: upSteps w k (w.up x) y
      | none => []

/-- **The way up**: from an entered vertex `x` to a vertex `y` above it, the arrival links walk
through distinct vertices, every step taken from a vertex strictly below `y`. -/
theorem upSteps_spec : ∀ (k x y : ℕ), w.entry x ≤ k → Above w y x → w.entry x ≠ 0 →
    IsPath g x (upSteps w k x y) y ∧
    (∀ p ∈ upSteps w k x y, ∃ t, Above w y t ∧ Above w t x ∧ t ≠ y ∧
      w.arrival t = some p.1 ∧ w.up t = p.2) ∧
    (∀ t, Above w y t → Above w t x → t ≠ y → ∃ e, w.arrival t = some e ∧
      (e, w.up t) ∈ upSteps w k x y)
  | 0, x, y, hk, _, hx => by omega
  | k + 1, x, y, hk, hyx, hx => by
    by_cases hxy : x = y
    · subst hxy
      simp only [upSteps, ite_true]
      refine ⟨⟨trivial, rfl, by simp⟩, by simp, fun t h1 h2 h3 => ?_⟩
      exact absurd (above_antisymm hS hO h1 h2).symm h3
    · rcases above_iff.mp hyx with h | ⟨ha, hy⟩
      · exact absurd h.symm hxy
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp ha
      obtain ⟨-, -, -, hue, hlt, hj⟩ := hangs hS hO x ha
      have ih := upSteps_spec k (w.up x) y (by omega) hy hue
      obtain ⟨⟨htr, hend, hnd⟩, hsteps, hall⟩ := ih
      simp only [upSteps, hxy, ite_false, he]
      refine ⟨⟨⟨(hj e (by simp [he])).symm, htr⟩, by rw [endOf_cons]; exact hend, ?_⟩,
        ?_, ?_⟩
      · simp only [List.map_cons]
        refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
        rcases List.mem_cons.mp hm with h | h
        · have := congrArg w.entry h
          omega
        · obtain ⟨⟨f, z⟩, hp, hzx⟩ := List.mem_map.mp h
          obtain ⟨t, -, ht, -, hta, hz⟩ := hsteps _ hp
          simp only at hzx hz
          have hab : Above w z (w.up x) := hz ▸ (Above.up (by simp [hta])).trans ht
          have := (entry_le_of_above hS hO hab hue).2.1
          rw [hzx] at this
          omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨x, hyx, Above.refl w x, hxy, he, rfl⟩
        · obtain ⟨t, h1, h2, h3, h4, h5⟩ := hsteps p hp
          exact ⟨t, h1, h2.trans (Above.up ha), h3, h4, h5⟩
      · intro t h1 h2 h3
        by_cases htx : t = x
        · subst htx
          exact ⟨e, he, by simp⟩
        · rcases above_iff.mp h2 with h | ⟨-, h⟩
          · exact absurd h htx
          · obtain ⟨e', he', hm⟩ := hall t h1 h h3
            exact ⟨e', he', List.mem_cons_of_mem _ hm⟩

end Shape

/-! ## The climb-back number is the least entry number it reads -/

theorem le_foldr_min {α : Type} (h : α → ℕ) (l : List α) (b m : ℕ) :
    m ≤ l.foldr (fun s m => min (h s) m) b ↔ m ≤ b ∧ ∀ s ∈ l, m ≤ h s := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, le_min_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

/-- **The climb-back number, read**: at least `m` exactly when `v`'s entry number is, and so is
the entry number of every row entry taken in `v`'s explored subtree other than the arrival link of
the vertex taking it. -/
theorem le_climb_iff (w : Walk) (v m : ℕ) :
    m ≤ climb (g := g) w v ↔ m ≤ w.entry v ∧ ∀ x < g.n, Explored (g := g) w v x →
      ∀ s ∈ looked (g := g) w x, w.arrival x ≠ some s.2 → m ≤ w.entry s.1 := by
  unfold climb
  generalize (w.entry v) = b
  have : ∀ xs : List ℕ, m ≤ xs.foldr (fun x m => ((looked (g := g) w x).filter
      fun s => w.arrival x ≠ some s.2).foldr (fun s m => min (w.entry s.1) m) m) b ↔
      m ≤ b ∧ ∀ x ∈ xs, ∀ s ∈ looked (g := g) w x, w.arrival x ≠ some s.2 →
        m ≤ w.entry s.1 := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.foldr_cons, le_foldr_min, ih, List.mem_filter, decide_eq_true_eq,
        List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, fun s hs ha => h3 s ⟨hs, ha⟩, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h3⟩, fun s ⟨hs, ha⟩ => h2 s hs ha⟩
  rw [this]
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, and_imp]

theorem climb_lt_iff (w : Walk) (v m : ℕ) :
    climb (g := g) w v < m ↔ w.entry v < m ∨ ∃ x < g.n, Explored (g := g) w v x ∧
      ∃ s ∈ looked (g := g) w x, w.arrival x ≠ some s.2 ∧ w.entry s.1 < m := by
  rw [← not_le, le_climb_iff]
  push Not
  constructor
  · intro h
    by_cases hv : m ≤ w.entry v
    · obtain ⟨x, hx, he, s, hs, ha, hlt⟩ := h hv
      exact Or.inr ⟨x, hx, he, s, hs, ha, hlt⟩
    · exact Or.inl (by omega)
  · rintro (h | ⟨x, hx, he, s, hs, ha, hlt⟩) hv
    · omega
    · exact ⟨x, hx, he, s, hs, ha, hlt⟩

end Walk

end AlgoDesign.Graphs.Blocks
