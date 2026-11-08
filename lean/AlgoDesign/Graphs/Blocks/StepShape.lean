/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Tree

/-!
# Bridges, cut vertices and blocks: one step keeps the tree's shape

The start has the whole `Shape`, and one step of the walk keeps `Outside` and the pieces of
`Shape` that speak of entry numbers, the path, each vertex's status, the tree, the vertices below an
open vertex, the row entries taken, the outer loop and the root's children. A step does one of six
things to these: enter a new root, move the outer loop on, nothing, take a row entry, take a row
entry and descend to a new vertex, or finish the current vertex. The pieces read none of the fields
the finishing rules change, so `core`, the walk with those fields cleared, carries them.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable {g : Graph}

/-! ## The six moves of a step -/

/-- The walk with the climb-back numbers, the edge stack, the cut flags and what was found
cleared: the fields the pieces of the tree's shape read. -/
def core (w : Walk) : Walk :=
  ⟨w.g, w.time, w.entry, fun _ => 0, w.path, [], fun _ => false, [], [], [], w.children, w.next,
    w.arrival, w.up, w.finished, w.taken⟩

/-- The current vertex `v` takes its row entry `i`. -/
def tick (w : Walk) (v : ℕ) (arr : Option ℕ) (i : ℕ) (rest : List Frame) : Walk :=
  { w with path := ⟨v, arr, i + 1⟩ :: rest, taken := Function.update w.taken v (i + 1) }

/-- The current vertex `v` finishes and leaves the path. -/
def pop (w : Walk) (v : ℕ) (rest : List Frame) : Walk :=
  { w with path := rest, finished := Function.update w.finished v true }

/-- The outer loop enters a new root. -/
def newRoot (w : Walk) : Walk :=
  enter { w with next := w.next + 1, children := 0 } w.next none w.next

/-- The current vertex `v` takes its row entry `i`, to `x` by link `e`, and descends to `x`. -/
def descend (w : Walk) (v : ℕ) (arr : Option ℕ) (i : ℕ) (rest : List Frame) (x e : ℕ) : Walk :=
  enter { tick w v arr i rest with
    children := if rest.isEmpty then w.children + 1 else w.children } x (some e) v

theorem entriesOk_core (w : Walk) : EntriesOk (g := g) (core w) ↔ EntriesOk (g := g) w := Iff.rfl
theorem pathOk_core (w : Walk) : PathOk (g := g) (core w) ↔ PathOk (g := g) w := Iff.rfl
theorem statusOk_core (w : Walk) : StatusOk (g := g) (core w) ↔ StatusOk (g := g) w := Iff.rfl
theorem treeOk_core (w : Walk) : TreeOk (g := g) (core w) ↔ TreeOk (g := g) w := Iff.rfl
theorem outerOk_core (w : Walk) : OuterOk (g := g) (core w) ↔ OuterOk (g := g) w := Iff.rfl
theorem childrenOk_core (w : Walk) : ChildrenOk (g := g) (core w) ↔ ChildrenOk (g := g) w :=
  Iff.rfl

theorem core_finishUnder (w : Walk) (u v e : ℕ) (b : Bool) :
    core (finishUnder g w u v e b) = core w := by
  unfold finishUnder
  dsimp only
  split_ifs <;> rfl

theorem core_finishRoot (w : Walk) (v : ℕ) : core (finishRoot w v) = core w := by
  unfold finishRoot
  dsimp only
  split_ifs <;> rfl

theorem cut_finishUnder (w : Walk) (u v e : ℕ) (b : Bool) (y : ℕ) (hy : y ≠ u) :
    (finishUnder g w u v e b).cut y = w.cut y := by
  unfold finishUnder
  dsimp only
  split_ifs <;> simp [Function.update_of_ne hy]

theorem cut_finishRoot (w : Walk) (v y : ℕ) (hy : y ≠ v) : (finishRoot w v).cut y = w.cut y := by
  unfold finishRoot
  dsimp only
  split_ifs <;> simp [Function.update_of_ne hy]

/-- **The six moves**: what one step does to the fields the tree's shape reads. -/
theorem step_cases (w : Walk) :
    (w.path = [] ∧ w.next < g.n ∧ w.entry w.next = 0 ∧ step g w = newRoot w) ∨
    (w.path = [] ∧ w.next < g.n ∧ w.entry w.next ≠ 0 ∧
      step g w = { w with next := w.next + 1 }) ∨
    (w.path = [] ∧ g.n ≤ w.next ∧ step g w = w) ∨
    (∃ v arr i rest x e, w.path = ⟨v, arr, i⟩ :: rest ∧ (g.adj v)[i]? = some (x, e) ∧
      (((x = v ∨ arr = some e) ∨ (w.entry x ≠ 0 ∧ w.entry v ≤ w.entry x)) ∧
          step g w = tick w v arr i rest ∨
        (x ≠ v ∧ w.entry x ≠ 0 ∧ w.entry x < w.entry v) ∧
          core (step g w) = core (tick w v arr i rest) ∧ (step g w).cut = w.cut ∨
        w.entry x = 0 ∧
          core (step g w) = core (descend w v arr i rest x e) ∧ (step g w).cut = w.cut)) ∨
    (∃ v arr i rest, w.path = ⟨v, arr, i⟩ :: rest ∧ (g.adj v)[i]? = none ∧
      core (step g w) = core (pop w v rest) ∧
      ∀ y, (step g w).cut y = w.cut y ∨ y = v ∨ ∃ fr ∈ rest, fr.vertex = y) := by
  unfold step
  rcases hp : w.path with _ | ⟨⟨v, arr, i⟩, rest⟩
  · by_cases h1 : w.next < g.n
    · by_cases h2 : w.entry w.next = 0
      · exact Or.inl ⟨rfl, h1, h2, by simp only [h1, h2, ite_true]; unfold newRoot; rw [hp]⟩
      · exact Or.inr (Or.inl ⟨rfl, h1, h2, by simp only [h1, h2, ite_true, ite_false]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega, by simp only [h1, ite_false]⟩))
  · right; right; right
    rcases hx : (g.adj v)[i]? with _ | ⟨x, e⟩
    · right
      refine ⟨v, arr, i, rest, rfl, hx, ?_, fun y => ?_⟩
      · simp only [hx]
        rcases rest with _ | ⟨⟨u, a, j⟩, above⟩ <;> rcases arr with _ | e <;>
          simp only [core_finishUnder, core_finishRoot] <;> rfl
      · simp only [hx]
        rcases rest with _ | ⟨⟨u, a, j⟩, above⟩ <;> rcases arr with _ | e
        · by_cases hyv : y = v
          · exact Or.inr (Or.inl hyv)
          · exact Or.inl (cut_finishRoot _ _ _ hyv)
        · by_cases hyv : y = v
          · exact Or.inr (Or.inl hyv)
          · exact Or.inl (cut_finishRoot _ _ _ hyv)
        · by_cases hyv : y = v
          · exact Or.inr (Or.inl hyv)
          · exact Or.inl (cut_finishRoot _ _ _ hyv)
        · by_cases hyu : y = u
          · exact Or.inr (Or.inr ⟨_, List.mem_cons_self, hyu.symm⟩)
          · exact Or.inl (cut_finishUnder _ _ _ _ _ _ hyu)
    · left
      refine ⟨v, arr, i, rest, x, e, rfl, hx, ?_⟩
      simp only [hx]
      unfold look
      dsimp only
      by_cases h1 : x = v ∨ arr = some e
      · exact Or.inl ⟨Or.inl h1, by rw [ite_eq_left h1]; rfl⟩
      · have hxv : x ≠ v := fun h => h1 (Or.inl h)
        rw [ite_eq_right h1]
        by_cases h2 : w.entry x = 0
        · rw [ite_eq_left h2]
          exact Or.inr (Or.inr ⟨h2, rfl, rfl⟩)
        · rw [ite_eq_right h2]
          by_cases h3 : w.entry x < w.entry v
          · rw [ite_eq_left h3]
            exact Or.inr (Or.inl ⟨⟨hxv, h2, h3⟩, rfl, rfl⟩)
          · rw [ite_eq_right h3]
            exact Or.inl ⟨Or.inr ⟨h2, by omega⟩, rfl⟩

/-! ## Fields carried over -/

theorem chain_congr {w w' : Walk} (ha : w'.arrival = w.arrival) (hu : w'.up = w.up) :
    chain w' = chain w := by
  funext k x
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [chain, ha, hu, ih]

theorem anc_congr {w w' : Walk} (ha : w'.arrival = w.arrival) (hu : w'.up = w.up) :
    Anc (g := g) w' = Anc (g := g) w := by
  funext a x
  simp only [Anc, chain_congr ha hu]

theorem openBelow_congr {w w' : Walk} (hp : w'.path = w.path) (he : w'.entry = w.entry)
    (ha : w'.arrival = w.arrival) (hu : w'.up = w.up) :
    OpenBelow (g := g) w' ↔ OpenBelow (g := g) w := by
  unfold OpenBelow onPath
  rw [anc_congr ha hu, hp, he]

theorem takenOk_congr {w w' : Walk} (ht : w'.taken = w.taken) (he : w'.entry = w.entry)
    (ha : w'.arrival = w.arrival) (hu : w'.up = w.up) :
    TakenOk (g := g) w' ↔ TakenOk (g := g) w := by
  unfold TakenOk looked
  rw [anc_congr ha hu, ht, he]

theorem openBelow_core (w : Walk) : OpenBelow (g := g) (core w) ↔ OpenBelow (g := g) w :=
  openBelow_congr rfl rfl rfl rfl

theorem takenOk_core (w : Walk) : TakenOk (g := g) (core w) ↔ TakenOk (g := g) w :=
  takenOk_congr rfl rfl rfl rfl

/-- A piece that reads only what `core` keeps passes between walks with one `core`. -/
theorem of_core {P : Walk → Prop} (hP : ∀ w, P (core w) ↔ P w) {w₁ w₂ : Walk}
    (h : core w₁ = core w₂) (h₂ : P w₂) : P w₁ := by
  rw [← hP, h, hP]
  exact h₂

theorem anc_self (w : Walk) (a : ℕ) : Anc (g := g) w a a := by
  unfold Anc
  cases g.n <;> simp [chain]

/-- `Anc` is `Above` when every vertex hangs from one entered earlier and the numbers are small. -/
theorem anc_iff_of {w : Walk} (hfuel : ∀ x, w.arrival x ≠ none → w.entry (w.up x) < w.entry x)
    (hpos : ∀ x, w.arrival x ≠ none → w.entry (w.up x) ≠ 0) (hb : ∀ x, w.entry x ≤ g.n + 1)
    (a x : ℕ) : Anc (g := g) w a x ↔ Above w a x :=
  mem_chain_iff hfuel hpos g.n x a (hb x)

/-! ## Rows -/

theorem mem_entries {v y i j : ℕ} : j ∈ g.entries v y i ↔ j = i ∧ Joins g i v y := by
  unfold Graph.entries Joins
  rcases g.links[i]? with _ | ⟨a, b⟩
  · simp
  · grind

theorem joins_lt {i a b : ℕ} (h : Joins g i a b) : i < g.links.length := by
  rcases h with h | h <;> exact (List.getElem?_eq_some_iff.mp h).1

/-- An entry of `v`'s row leads to a vertex of the graph by a link joining it to `v`. -/
theorem mem_adj {v y i : ℕ} : (y, i) ∈ g.adj v ↔ y < g.n ∧ Joins g i v y := by
  simp only [Graph.adj, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq,
    mem_entries]
  constructor
  · rintro ⟨y', hy', j, ⟨k, hk, rfl, hj⟩, rfl, rfl⟩
    exact ⟨hy', hj⟩
  · rintro ⟨hy, hj⟩
    exact ⟨y, hy, i, ⟨i, joins_lt hj, rfl, hj⟩, rfl, rfl⟩

/-- Changing a predicate at one vertex of `0 .. n - 1` from false to true adds one to its count. -/
theorem length_filter_range_add {p q : ℕ → Bool} {n x : ℕ} (hx : x < n) (hp : p x = false)
    (hq : q x = true) (h : ∀ y, y ≠ x → q y = p y) :
    ((List.range n).filter q).length = ((List.range n).filter p).length + 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.filter_append, List.length_append]
    by_cases hxn : x < n
    · rw [ih hxn, List.filter_congr (p := q) (q := p) (l := [n])
        (by simpa using h n (by omega))]
      omega
    · obtain rfl : x = n := by omega
      rw [List.filter_congr (p := q) (q := p) (l := List.range x)
        (fun y hy => h y (by simp at hy; omega))]
      simp [hp, hq]

/-! ## The path -/

theorem getLast_tick {fr : Frame} {v i j : ℕ} {arr : Option ℕ} {rest : List Frame}
    (h : fr ∈ (⟨v, arr, j⟩ :: rest).getLast?) :
    ∃ fr' ∈ (⟨v, arr, i⟩ :: rest).getLast?, fr'.vertex = fr.vertex ∧ fr'.arrival = fr.arrival := by
  rcases rest with _ | ⟨b, l⟩
  · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, rfl, rfl⟩
  · rw [List.getLast?_cons_cons] at h
    exact ⟨fr, by rw [List.getLast?_cons_cons]; exact h, rfl, rfl⟩

section Shape

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
variable {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame}

include hS

theorem time_le : w.time ≤ g.n := by
  rw [hS.1.2.2]
  exact (List.length_filter_le _ _).trans (by simp)

include hO in
theorem entry_le_time (y : ℕ) : w.entry y ≤ w.time := by
  by_cases hy : y < g.n
  · exact hS.1.1 y hy
  · rw [(hO y (by omega)).1]
    omega

theorem entry_of_onPath {u : ℕ} (hu : w.onPath u = true) : u < g.n ∧ w.entry u ≠ 0 := by
  obtain ⟨fr, hfr, rfl⟩ := (onPath_iff (w := w) u).mp hu
  exact ⟨(hS.2.1.2.2.2 fr hfr).1, (hS.2.1.2.2.2 fr hfr).2.1⟩

variable (hp : w.path = ⟨v, arr, i⟩ :: rest)
include hp

theorem top_facts : v < g.n ∧ w.entry v ≠ 0 ∧ w.arrival v = arr ∧ w.taken v = i ∧
    w.taken v ≤ (g.adj v).length ∧ w.onPath v = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS.2.1.2.2.2 ⟨v, arr, i⟩ (by simp [hp])
  exact ⟨h1, h2, h3, h4.symm, h5, by simp [onPath, hp]⟩

theorem not_mem_rest {fr : Frame} (hfr : fr ∈ rest) : fr.vertex ≠ v := by
  have hnd := hS.2.1.1
  rw [hp, List.map_cons, List.nodup_cons] at hnd
  intro h
  exact hnd.1 (List.mem_map.mpr ⟨fr, hfr, h⟩)

/-- Every open vertex is above the current one. -/
theorem above_top {u : ℕ} (hu : w.onPath u = true) : Above w u v := by
  have key : ∀ (l : List Frame) (a : Frame), (a :: l).IsChain (Hangs (g := g) w) →
      (∀ fr ∈ a :: l, w.arrival fr.vertex = fr.arrival) →
      ∀ fr ∈ a :: l, Above w fr.vertex a.vertex := by
    intro l
    induction l with
    | nil =>
      intro a _ _ fr hfr
      rw [List.mem_singleton.mp hfr]
      exact Above.refl w _
    | cons b l ih =>
      intro a hc ha fr hfr
      rw [List.isChain_cons_cons] at hc
      have hab : Above w b.vertex a.vertex := by
        obtain ⟨⟨e, he, -⟩, hup, -⟩ := hc.1
        rw [← hup]
        exact Above.up (by rw [ha a (by simp), Option.mem_def.mp he]; simp)
      rcases List.mem_cons.mp hfr with rfl | hfr
      · exact Above.refl w _
      · exact (ih b hc.2 (fun f hf => ha f (List.mem_cons_of_mem _ hf)) fr hfr).trans hab
  obtain ⟨fr, hfr, rfl⟩ := (onPath_iff (w := w) u).mp hu
  have hch : (⟨v, arr, i⟩ :: rest).IsChain (Hangs (g := g) w) := by
    rw [← hp]
    exact hS.2.1.2.1
  rw [hp] at hfr
  exact key rest ⟨v, arr, i⟩ hch
    (fun f hf => (hS.2.1.2.2.2 f (by rw [hp]; exact hf)).2.2.1) fr hfr

end Shape

/-! ## Entering a vertex -/

section Enter

variable {p : Walk} {x u : ℕ} {arr : Option ℕ}

theorem onPath_enter (y : ℕ) : (enter p x arr u).onPath y = true ↔ x = y ∨ p.onPath y = true := by
  simp [onPath, enter]

theorem entry_enter_ne {z : ℕ} (hz : p.entry z ≠ 0) : (enter p x arr u).entry z ≠ 0 := by
  simp only [enter, Function.update_apply]
  split_ifs <;> omega

/-- Entering a vertex no vertex hangs from keeps every link up the tree. -/
theorem above_enter_of (hx : p.arrival x = none) {a y : ℕ} (h : Above p a y) :
    Above (enter p x arr u) a y := by
  induction h with
  | refl => exact Above.refl _ _
  | @tail b c _ hbc ih =>
    obtain ⟨hc, rfl⟩ := hbc
    have hcx : c ≠ x := fun h => hc (h ▸ hx)
    have h1 : (enter p x arr u).arrival c ≠ none := by
      simpa [enter, Function.update_of_ne hcx] using hc
    have h2 : (enter p x arr u).up c = p.up c := by simp [enter, Function.update_of_ne hcx]
    exact ih.trans (h2 ▸ Above.up h1)

theorem above_enter_self (e : ℕ) : Above (enter p x (some e) u) u x :=
  Relation.ReflTransGen.single ⟨by simp [enter], by simp [enter]⟩

theorem entriesOk_enter (h : EntriesOk (g := g) p) (hx : x < g.n) (h0 : p.entry x = 0) :
    EntriesOk (g := g) (enter p x arr u) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun y hy => ?_, fun y hy z hz hyz hne => ?_, ?_⟩
  · simp only [enter, Function.update_apply]
    split_ifs
    · omega
    · have := h1 y hy
      omega
  · simp only [enter, Function.update_apply] at hyz hne
    split_ifs at hyz hne with hyx hzx hzx
    · exact hyx.trans hzx.symm
    · have := h1 z hz
      omega
    · have := h1 y hy
      omega
    · exact h2 y hy z hz hyz hne
  · simp only [enter]
    rw [length_filter_range_add (p := fun y => decide (p.entry y ≠ 0)) hx (by simp [h0])
      (by simp) (fun y hy => by simp [Function.update_of_ne hy])]
    omega

theorem statusOk_enter (h : StatusOk (g := g) p) (hx : x < g.n) (h0 : p.entry x = 0) :
    StatusOk (g := g) (enter p x arr u) := by
  intro y hy
  by_cases hyx : y = x
  · rw [hyx]
    have hnf : p.finished x = false := by
      by_contra hf
      exact ((h x hx).1.mpr (Or.inr (by simpa using hf))) h0
    have hon : (enter p x arr u).onPath x = true := (onPath_enter x).mpr (Or.inl rfl)
    rw [hon]
    simp [enter, hnf]
  · obtain ⟨h1, h2, h3, h4⟩ := h y hy
    have hon : (enter p x arr u).onPath y = p.onPath y := by
      simp [onPath, enter, Ne.symm hyx]
    rw [hon]
    simp only [enter, Function.update_of_ne hyx]
    exact ⟨h1, h2, h3, h4⟩

theorem treeOk_enter (h : TreeOk (g := g) p) (hE : EntriesOk (g := g) p)
    (h0 : p.entry x = 0) (harr : ∀ e ∈ arr, Joins g e u x ∧ u < g.n ∧ p.entry u ≠ 0) :
    TreeOk (g := g) (enter p x arr u) := by
  intro y hy hye e he
  by_cases hyx : y = x
  · rw [hyx] at he ⊢
    simp only [enter, Function.update_self] at he ⊢
    obtain ⟨h1, h2, h3⟩ := harr e he
    have hux : u ≠ x := fun h => h3 (by rw [h]; exact h0)
    simp only [Function.update_of_ne hux]
    exact ⟨h1, h2, h3, by have := hE.1 u h2; omega⟩
  · simp only [enter, Function.update_of_ne hyx] at hye he ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h y hy hye e he
    have hux : p.up y ≠ x := fun h => h3 (by rw [h]; exact h0)
    simp only [Function.update_of_ne hux]
    exact ⟨h1, h2, h3, h4⟩

theorem pathOk_enter (hP : PathOk (g := g) p) (hE : EntriesOk (g := g) p)
    (hSt : StatusOk (g := g) p) (hx : x < g.n) (h0 : p.entry x = 0)
    (hnil : p.path = [] → arr = none)
    (hhead : ∀ fr ∈ p.path.head?, (∃ e ∈ arr, Joins g e fr.vertex x) ∧ u = fr.vertex) :
    PathOk (g := g) (enter p x arr u) := by
  obtain ⟨hnd, hch, hlast, hall⟩ := hP
  have hnot : ∀ fr ∈ p.path, fr.vertex ≠ x := fun fr hfr h => (hall fr hfr).2.1 (h ▸ h0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [enter, List.map_cons, List.nodup_cons, List.mem_map]
    exact ⟨fun ⟨fr, hfr, h⟩ => hnot fr hfr h, hnd⟩
  · simp only [enter]
    rw [List.isChain_cons]
    refine ⟨fun fr hfr => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hhead fr hfr
      have hfr' : fr ∈ p.path := List.mem_of_mem_head? hfr
      refine ⟨h1, by simp [h2], ?_⟩
      simp only [Function.update_self, Function.update_of_ne (hnot fr hfr')]
      have := hE.1 fr.vertex (hall fr hfr').1
      omega
    · refine hch.imp_of_mem_imp (fun a b ha hb h => ?_)
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, ?_, ?_⟩
      · simp only [Function.update_of_ne (hnot a ha)]
        exact h2
      · simp only [Function.update_of_ne (hnot a ha), Function.update_of_ne (hnot b hb)]
        exact h3
  · intro fr hfr
    simp only [enter] at hfr
    rcases hpp : p.path with _ | ⟨b, l⟩
    · rw [hpp] at hfr
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hfr
      subst hfr
      exact hnil hpp
    · rw [hpp, List.getLast?_cons_cons] at hfr
      exact hlast fr (by rw [hpp]; exact hfr)
  · intro fr hfr
    simp only [enter, List.mem_cons] at hfr
    rcases hfr with rfl | hfr
    · have := (hSt x hx).2.2.2 h0
      simp [enter, this.1, hx]
    · have hne := hnot fr hfr
      obtain ⟨h1, h2, h3, h4, h5⟩ := hall fr hfr
      simp only [enter, Function.update_of_ne hne]
      exact ⟨h1, h2, h3, h4, h5⟩

end Enter

/-- `Anc` is `Above` once a new vertex is entered, from an entered vertex or as a root. -/
theorem anc_iff_enter {w p : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hpe : p.entry = w.entry) (hpa : p.arrival = w.arrival) (hpu : p.up = w.up)
    (hpt : p.time = w.time) {x u : ℕ} {arr : Option ℕ} (h0 : w.entry x = 0)
    (hu : arr ≠ none → w.entry u ≠ 0) (a y : ℕ) :
    Anc (g := g) (enter p x arr u) a y ↔ Above (enter p x arr u) a y := by
  have hn := time_le hS
  apply anc_iff_of
  · intro z hz
    by_cases hzx : z = x
    · rw [hzx] at hz ⊢
      simp only [enter, Function.update_self, ne_eq] at hz ⊢
      have hu' := hu hz
      have hux : u ≠ x := fun h => hu' (by rw [h]; exact h0)
      rw [Function.update_of_ne hux, hpe, hpt]
      have := entry_le_time hS hO u
      omega
    · simp only [enter, Function.update_of_ne hzx, hpa, hpu, hpe] at hz ⊢
      have hux : w.up z ≠ x := fun h => (hangs hS hO z hz).2.2.2.1 (by rw [h]; exact h0)
      rw [Function.update_of_ne hux]
      exact (hangs hS hO z hz).2.2.2.2.1
  · intro z hz
    by_cases hzx : z = x
    · rw [hzx] at hz ⊢
      simp only [enter, Function.update_self, ne_eq] at hz ⊢
      have hux : u ≠ x := fun h => hu hz (by rw [h]; exact h0)
      rw [Function.update_of_ne hux, hpe]
      exact hu hz
    · simp only [enter, Function.update_of_ne hzx, hpa, hpu, hpe] at hz ⊢
      have hux : w.up z ≠ x := fun h => (hangs hS hO z hz).2.2.2.1 (by rw [h]; exact h0)
      rw [Function.update_of_ne hux]
      exact (hangs hS hO z hz).2.2.2.1
  · intro z
    simp only [enter, Function.update_apply, hpe, hpt]
    split_ifs
    · omega
    · have := entry_le_time hS hO z
      omega

/-! ## A new root -/

section Root

variable {w : Walk}

theorem anc_iff_newRoot (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (h0 : w.entry w.next = 0) (a y : ℕ) :
    Anc (g := g) (newRoot w) a y ↔ Above (newRoot w) a y :=
  anc_iff_enter (p := { w with next := w.next + 1, children := 0 }) (u := w.next) hS hO rfl rfl
    rfl rfl h0 (fun h => absurd rfl h) a y

theorem entriesOk_newRoot (hS : Shape (g := g) w) (hn : w.next < g.n)
    (h0 : w.entry w.next = 0) : EntriesOk (g := g) (newRoot w) :=
  entriesOk_enter hS.1 hn h0

theorem pathOk_newRoot (hS : Shape (g := g) w) (hp : w.path = []) (hn : w.next < g.n)
    (h0 : w.entry w.next = 0) : PathOk (g := g) (newRoot w) :=
  pathOk_enter hS.2.1 hS.1 hS.2.2.1 hn h0 (fun _ => rfl) (fun fr hfr => by simp [hp] at hfr)

theorem statusOk_newRoot (hS : Shape (g := g) w) (hn : w.next < g.n)
    (h0 : w.entry w.next = 0) : StatusOk (g := g) (newRoot w) :=
  statusOk_enter hS.2.2.1 hn h0

theorem treeOk_newRoot (hS : Shape (g := g) w)
    (h0 : w.entry w.next = 0) : TreeOk (g := g) (newRoot w) :=
  treeOk_enter hS.2.2.2.1 hS.1 h0 (fun e he => by simp at he)

theorem openBelow_newRoot (hS : Shape (g := g) w) (hO : Outside (g := g) w) (hp : w.path = [])
    (h0 : w.entry w.next = 0) : OpenBelow (g := g) (newRoot w) := by
  intro u hun hu y hy hye hle
  have hu' : w.next = u := by
    rcases (onPath_enter (p := { w with next := w.next + 1, children := 0 }) u).mp hu with h | h
    · exact h
    · simp [onPath, hp] at h
  rw [anc_iff_newRoot hS hO h0, ← hu']
  have hyn : y = w.next := by
    by_contra hne
    simp only [newRoot, enter, ← hu', Function.update_self, Function.update_of_ne hne] at hle
    have := entry_le_time hS hO y
    omega
  rw [hyn]
  exact Above.refl _ _

theorem takenOk_newRoot (hS : Shape (g := g) w) (hO : Outside (g := g) w) (hn : w.next < g.n)
    (h0 : w.entry w.next = 0) : TakenOk (g := g) (newRoot w) := by
  have hxa : w.arrival w.next = none := ((hS.2.2.1 w.next hn).2.2.2 h0).2
  have hlift : ∀ a b, Above w a b → Above (newRoot w) a b := fun a b h =>
    above_enter_of (p := { w with next := w.next + 1, children := 0 }) hxa h
  intro y hy s hs
  obtain ⟨h1, h2⟩ := hS.2.2.2.2.2.1 y hy s hs
  rw [anc_iff_newRoot hS hO h0, anc_iff_newRoot hS hO h0]
  refine ⟨entry_enter_ne h1, fun hne => ?_⟩
  rcases h2 hne with h | h
  · exact Or.inl (hlift _ _ ((anc_iff hS hO _ _).mp h))
  · exact Or.inr (hlift _ _ ((anc_iff hS hO _ _).mp h))

theorem outerOk_newRoot (hS : Shape (g := g) w) (hp : w.path = []) (hn : w.next < g.n) :
    OuterOk (g := g) (newRoot w) := by
  obtain ⟨-, h2, -⟩ := hS.2.2.2.2.2.2.1
  refine ⟨by simp only [newRoot, enter]; omega, fun h => by simp [newRoot, enter] at h, ?_⟩
  intro fr hfr
  simp only [newRoot, enter, hp, List.getLast?_singleton, Option.mem_def,
    Option.some.injEq] at hfr
  subst hfr
  refine ⟨rfl, fun y hy => ?_⟩
  have hy' : y < w.next := hy
  have := h2 hp y (by omega)
  exact this.2 (this.1 hy')

theorem childrenOk_newRoot (hS : Shape (g := g) w) (hO : Outside (g := g) w) (hp : w.path = [])
    (h0 : w.entry w.next = 0) : ChildrenOk (g := g) (newRoot w) := by
  intro fr hfr
  simp only [newRoot, enter, hp, List.getLast?_singleton, Option.mem_def,
    Option.some.injEq] at hfr
  subst hfr
  change 0 = numChildren (g := g) (newRoot w) w.next
  unfold numChildren
  rw [eq_comm, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro y _ hc
  have hc' : Child (newRoot w) w.next y := of_decide_eq_true hc
  obtain ⟨-, h2, h3⟩ := hc'
  simp only [newRoot, enter] at h2 h3
  by_cases hyn : y = w.next
  · rw [hyn] at h2
    simp at h2
  · simp only [Function.update_of_ne hyn] at h2 h3
    exact (hangs hS hO y h2).2.2.2.1 (by rw [h3]; exact h0)

theorem outside_newRoot (hO : Outside (g := g) w) (hn : w.next < g.n) :
    Outside (g := g) (newRoot w) := by
  intro y hy
  have hyn : y ≠ w.next := by omega
  simp only [newRoot, enter, Function.update_of_ne hyn]
  exact hO y hy

theorem outerOk_next (hS : Shape (g := g) w) (hp : w.path = []) (hn : w.next < g.n)
    (h0 : w.entry w.next ≠ 0) : OuterOk (g := g) { w with next := w.next + 1 } := by
  obtain ⟨-, h2, -⟩ := hS.2.2.2.2.2.2.1
  refine ⟨by simp only; omega, fun _ y hy => ⟨fun hyn => ?_, (h2 hp y hy).2⟩,
    fun fr hfr => by simp [hp] at hfr⟩
  have hyn' : y < w.next + 1 := hyn
  by_cases hy' : y < w.next
  · exact (h2 hp y hy).1 hy'
  · obtain rfl : y = w.next := by omega
    exact h0

end Root

/-! ## Taking a row entry -/

section Tick

variable {w : Walk} {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame} {x e : ℕ}

theorem pathOk_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) : PathOk (g := g) (tick w v arr i rest) := by
  obtain ⟨hnd, hch, hlast, hall⟩ := hS.2.1
  rw [hp] at hnd hch hlast hall
  have hi : i < (g.adj v).length := (List.getElem?_eq_some_iff.mp hx).1
  refine ⟨hnd, ?_, fun fr hfr => ?_, fun fr hfr => ?_⟩
  · change (⟨v, arr, i + 1⟩ :: rest).IsChain _
    rcases rest with _ | ⟨b, l⟩
    · exact List.isChain_singleton _
    · rw [List.isChain_cons_cons] at hch ⊢
      exact ⟨hch.1, hch.2⟩
  · obtain ⟨fr', hfr', -, harr⟩ := getLast_tick (i := i) hfr
    rw [← harr]
    exact hlast fr' hfr'
  · simp only [tick, List.mem_cons] at hfr
    rcases hfr with rfl | hfr
    · obtain ⟨h1, h2, h3, -, -⟩ := hall _ List.mem_cons_self
      refine ⟨h1, h2, h3, by simp [tick], ?_⟩
      simp only [tick, Function.update_self]
      omega
    · have hne := not_mem_rest hS hp hfr
      obtain ⟨h1, h2, h3, h4, h5⟩ := hall fr (List.mem_cons_of_mem _ hfr)
      simp only [tick, Function.update_of_ne hne]
      exact ⟨h1, h2, h3, h4, h5⟩

theorem statusOk_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    StatusOk (g := g) (tick w v arr i rest) := by
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := hS.2.2.1 y hy
  have hon : (tick w v arr i rest).onPath y = w.onPath y := by simp [onPath, tick, hp]
  rw [hon]
  by_cases hyv : y = v
  · rw [hyv] at h1 h2 h3 h4 ⊢
    obtain ⟨-, hve, -, -, -, hvon⟩ := top_facts hS hp
    exact ⟨h1, h2, fun hf => absurd ⟨hvon, hf⟩ h2, fun h => absurd h hve⟩
  · simp only [tick, Function.update_of_ne hyv]
    exact ⟨h1, h2, h3, h4⟩

theorem openBelow_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    OpenBelow (g := g) (tick w v arr i rest) := by
  intro u hun hu y hy hye hle
  rw [anc_congr (w' := tick w v arr i rest) (w := w) rfl rfl]
  have hon : (tick w v arr i rest).onPath u = w.onPath u := by simp [onPath, tick, hp]
  exact hS.2.2.2.2.1 u hun (by rwa [hon] at hu) y hy hye hle

theorem mem_looked_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) {y : ℕ} {s : ℕ × ℕ}
    (hs : s ∈ looked (g := g) (tick w v arr i rest) y) :
    s ∈ looked (g := g) w y ∨ (y = v ∧ s = (x, e)) := by
  have htk := (top_facts hS hp).2.2.2.1
  by_cases hyv : y = v
  · rw [hyv] at hs ⊢
    simp only [looked, tick, Function.update_self, List.take_add_one, hx, Option.toList_some,
      List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | hs
    · left
      unfold looked
      rw [htk]
      exact hs
    · exact Or.inr ⟨rfl, hs⟩
  · left
    simpa [looked, tick, Function.update_of_ne hyv] using hs

/-- The entry just taken leads to an entered vertex above or below the current one. -/
theorem taken_entry (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e))
    (h : (x = v ∨ arr = some e) ∨ (w.entry x ≠ 0 ∧ w.entry v ≤ w.entry x) ∨
      (w.entry x ≠ 0 ∧ w.entry x < w.entry v)) :
    w.entry x ≠ 0 ∧ (x ≠ v → Anc (g := g) w x v ∨ Anc (g := g) w v x) := by
  have hj : x < g.n ∧ Joins g e v x := mem_adj.mp (List.mem_of_getElem? hx)
  obtain ⟨hvn, hve, hva, -, -, hvon⟩ := top_facts hS hp
  rcases h with (hxv | harr) | ⟨hxe, hle⟩ | ⟨hxe, hlt⟩
  · exact ⟨by rw [hxv]; exact hve, fun h => absurd hxv h⟩
  · rw [harr] at hva
    have ht := hS.2.2.2.1 v hvn hve e (by rw [hva]; rfl)
    rcases Joins.ends ht.1 hj.2 with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact ⟨by rw [h2]; exact hve, fun h => absurd h2 h⟩
    · refine ⟨by rw [h2]; exact ht.2.2.1, fun _ => Or.inl ?_⟩
      rw [anc_iff hS hO, h2]
      exact Above.up (by rw [hva]; simp)
  · exact ⟨hxe, fun _ => Or.inr (hS.2.2.2.2.1 v hvn hvon x hj.1 hxe hle)⟩
  · refine ⟨hxe, fun hxv => Or.inl ?_⟩
    rw [anc_iff hS hO]
    apply above_top hS hp
    rcases (hS.2.2.1 x hj.1).1.mp hxe with hxp | hxf
    · exact hxp
    · exfalso
      have htk := (hS.2.2.1 x hj.1).2.2.1 hxf
      have hmem : (v, e) ∈ looked (g := g) w x := by
        unfold looked
        rw [htk, List.take_length]
        exact mem_adj.mpr ⟨hvn, hj.2.symm⟩
      obtain ⟨-, h2⟩ := hS.2.2.2.2.2.1 x hj.1 _ hmem
      rcases h2 (Ne.symm hxv) with h | h
      · have : w.entry v ≤ w.entry x :=
          (entry_le_of_above hS hO ((anc_iff hS hO _ _).mp h) hxe).2.1
        omega
      · have hvf := finished_of_above hS hO ((anc_iff hS hO _ _).mp h) hxf hve
        exact (hS.2.2.1 v hvn).2.1 ⟨hvon, hvf⟩

theorem takenOk_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e))
    (hnew : w.entry x ≠ 0 ∧ (x ≠ v → Anc (g := g) w x v ∨ Anc (g := g) w v x)) :
    TakenOk (g := g) (tick w v arr i rest) := by
  intro y hy s hs
  rw [anc_congr (w' := tick w v arr i rest) (w := w) rfl rfl]
  rcases mem_looked_tick hS hp hx hs with hs | ⟨rfl, rfl⟩
  · exact hS.2.2.2.2.2.1 y hy s hs
  · exact hnew

theorem outerOk_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    OuterOk (g := g) (tick w v arr i rest) := by
  obtain ⟨h1, -, h3⟩ := hS.2.2.2.2.2.2.1
  refine ⟨h1, fun h => by simp [tick] at h, fun fr hfr => ?_⟩
  obtain ⟨fr', hfr', hpl, -⟩ := getLast_tick (i := i) hfr
  rw [hp] at h3
  rw [← hpl]
  exact h3 fr' hfr'

theorem childrenOk_tick (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    ChildrenOk (g := g) (tick w v arr i rest) := by
  intro fr hfr
  obtain ⟨fr', hfr', hpl, -⟩ := getLast_tick (i := i) hfr
  have h := hS.2.2.2.2.2.2.2.1 fr' (by rw [hp]; exact hfr')
  rw [← hpl]
  exact h

theorem outside_tick (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) : Outside (g := g) (tick w v arr i rest) := by
  intro y hy
  have hyv : y ≠ v := by
    have := (top_facts hS hp).1
    omega
  simp only [tick, Function.update_of_ne hyv]
  exact hO y hy

/-! ## Descending to a new vertex -/

theorem anc_iff_descend (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (h0 : w.entry x = 0) (a y : ℕ) :
    Anc (g := g) (descend w v arr i rest x e) a y ↔ Above (descend w v arr i rest x e) a y :=
  anc_iff_enter (p := { tick w v arr i rest with
      children := if rest.isEmpty then w.children + 1 else w.children }) (u := v) hS hO rfl rfl
    rfl rfl h0 (fun _ => (top_facts hS hp).2.1) a y

theorem entriesOk_descend (hS : Shape (g := g) w) (hx : (g.adj v)[i]? = some (x, e))
    (h0 : w.entry x = 0) : EntriesOk (g := g) (descend w v arr i rest x e) :=
  entriesOk_enter hS.1 (mem_adj.mp (List.mem_of_getElem? hx)).1 h0

theorem pathOk_descend (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) :
    PathOk (g := g) (descend w v arr i rest x e) := by
  have hj := mem_adj.mp (List.mem_of_getElem? hx)
  refine pathOk_enter (pathOk_tick hS hp hx) hS.1 (statusOk_tick hS hp) hj.1 h0
    (fun h => by simp [tick] at h) (fun fr hfr => ?_)
  simp only [tick, List.head?_cons, Option.mem_def, Option.some.injEq] at hfr
  subst hfr
  exact ⟨⟨e, rfl, hj.2⟩, rfl⟩

theorem statusOk_descend (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) :
    StatusOk (g := g) (descend w v arr i rest x e) :=
  statusOk_enter (statusOk_tick hS hp) (mem_adj.mp (List.mem_of_getElem? hx)).1 h0

theorem treeOk_descend (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) :
    TreeOk (g := g) (descend w v arr i rest x e) := by
  have hj := mem_adj.mp (List.mem_of_getElem? hx)
  refine treeOk_enter hS.2.2.2.1 hS.1 h0 (fun e' he' => ?_)
  rw [Option.mem_def, Option.some.injEq] at he'
  subst he'
  exact ⟨hj.2, (top_facts hS hp).1, (top_facts hS hp).2.1⟩

theorem openBelow_descend (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e))
    (h0 : w.entry x = 0) : OpenBelow (g := g) (descend w v arr i rest x e) := by
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  have hxa : w.arrival x = none := ((hS.2.2.1 x hxn).2.2.2 h0).2
  have hlift : ∀ a b, Above w a b → Above (descend w v arr i rest x e) a b := fun a b h =>
    above_enter_of (p := { tick w v arr i rest with
      children := if rest.isEmpty then w.children + 1 else w.children }) hxa h
  have hup : Above (descend w v arr i rest x e) v x := above_enter_self e
  intro u hun hu y hy hye hle
  rw [anc_iff_descend hS hO hp h0]
  have hent : ∀ z, (descend w v arr i rest x e).entry z =
      Function.update w.entry x (w.time + 1) z := fun _ => rfl
  rw [hent, hent] at hle
  rw [hent] at hye
  have hon : x = u ∨ (tick w v arr i rest).onPath u = true :=
    (onPath_enter (p := tick w v arr i rest) (x := x) (arr := some e) (u := v) u).mp hu
  have hton : (tick w v arr i rest).onPath u = w.onPath u := by simp [onPath, tick, hp]
  rw [hton] at hon
  rcases hon with hxu | hu'
  · rw [← hxu] at hle ⊢
    by_cases hyx : y = x
    · rw [hyx]
      exact Above.refl _ _
    · rw [Function.update_self, Function.update_of_ne hyx] at hle
      have := entry_le_time hS hO y
      omega
  · have hun := entry_of_onPath hS hu'
    have hux : u ≠ x := fun h => hun.2 (by rw [h]; exact h0)
    by_cases hyx : y = x
    · rw [hyx]
      exact (hlift u v (above_top hS hp hu')).trans hup
    · rw [Function.update_of_ne hux, Function.update_of_ne hyx] at hle
      rw [Function.update_of_ne hyx] at hye
      exact hlift u y ((anc_iff hS hO u y).mp (hS.2.2.2.2.1 u hun.1 hu' y hy hye hle))

theorem takenOk_descend (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e))
    (h0 : w.entry x = 0) : TakenOk (g := g) (descend w v arr i rest x e) := by
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  have hxa : w.arrival x = none := ((hS.2.2.1 x hxn).2.2.2 h0).2
  have hlift : ∀ a b, Above w a b → Above (descend w v arr i rest x e) a b := fun a b h =>
    above_enter_of (p := { tick w v arr i rest with
      children := if rest.isEmpty then w.children + 1 else w.children }) hxa h
  have hup : Above (descend w v arr i rest x e) v x := above_enter_self e
  intro y hy s hs
  rw [anc_iff_descend hS hO hp h0, anc_iff_descend hS hO hp h0]
  rcases mem_looked_tick hS hp hx (y := y) hs with hs | ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := hS.2.2.2.2.2.1 y hy s hs
    refine ⟨entry_enter_ne h1, fun hne => ?_⟩
    rcases h2 hne with h | h
    · exact Or.inl (hlift _ _ ((anc_iff hS hO _ _).mp h))
    · exact Or.inr (hlift _ _ ((anc_iff hS hO _ _).mp h))
  · exact ⟨by simp [descend, enter], fun _ => Or.inr hup⟩

theorem outerOk_descend (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    OuterOk (g := g) (descend w v arr i rest x e) := by
  have ht := outerOk_tick hS hp
  refine ⟨ht.1, fun h => by simp [descend, enter] at h, fun fr hfr => ?_⟩
  have hfr2 : fr ∈ (tick w v arr i rest).path.getLast? := by
    simpa [descend, enter, tick] using hfr
  exact ht.2.2 fr hfr2

theorem numChildren_descend (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) (r : ℕ) :
    numChildren (g := g) (descend w v arr i rest x e) r =
      numChildren (g := g) w r + if v = r then 1 else 0 := by
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  unfold numChildren
  by_cases hvr : v = r
  · rw [ite_eq_left hvr]
    apply length_filter_range_add hxn
    · simp [Child, h0]
    · simp [Child, descend, enter, hvr]
    · intro y hyx
      refine decide_eq_decide.mpr ?_
      simp only [Child, descend, enter, tick, Function.update_of_ne hyx]
  · rw [ite_eq_right hvr, add_zero]
    congr 1
    apply List.filter_congr
    intro y _
    by_cases hyx : y = x
    · rw [hyx]
      simp [Child, descend, enter, h0, hvr]
    · refine decide_eq_decide.mpr ?_
      simp only [Child, descend, enter, tick, Function.update_of_ne hyx]

theorem childrenOk_descend (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) :
    ChildrenOk (g := g) (descend w v arr i rest x e) := by
  intro fr hfr
  have hfr2 : fr ∈ (tick w v arr i rest).path.getLast? := by
    simpa [descend, enter, tick] using hfr
  obtain ⟨fr', hfr', hpl, -⟩ := getLast_tick (i := i) hfr2
  have hold := hS.2.2.2.2.2.2.2.1 fr' (by rw [hp]; exact hfr')
  rw [← hpl, numChildren_descend hx h0, ← hold]
  change (if rest.isEmpty then w.children + 1 else w.children) = _
  rcases rest with _ | ⟨b, l⟩
  · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hfr'
    subst hfr'
    simp
  · rw [List.getLast?_cons_cons] at hfr'
    have hne := not_mem_rest hS hp (List.mem_of_getLast? hfr')
    simp [Ne.symm hne]

theorem outside_descend (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e)) :
    Outside (g := g) (descend w v arr i rest x e) := by
  intro y hy
  have hyx : y ≠ x := by
    have := (mem_adj.mp (List.mem_of_getElem? hx)).1
    omega
  have hyv : y ≠ v := by
    have := (top_facts hS hp).1
    omega
  simp only [descend, enter, tick, Function.update_of_ne hyx, Function.update_of_ne hyv]
  exact hO y hy

end Tick

/-! ## Finishing a vertex -/

section Pop

variable {w : Walk} {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame}

theorem pathOk_pop (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    PathOk (g := g) (pop w v rest) := by
  obtain ⟨hnd, hch, hlast, hall⟩ := hS.2.1
  rw [hp] at hnd hch hlast hall
  rw [List.map_cons, List.nodup_cons] at hnd
  refine ⟨hnd.2, hch.tail, fun fr hfr => ?_, fun fr hfr => hall fr (List.mem_cons_of_mem _ hfr)⟩
  rcases rest with _ | ⟨b, l⟩
  · simp [pop] at hfr
  · exact hlast fr (by rw [List.getLast?_cons_cons]; exact hfr)

theorem statusOk_pop (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = none) : StatusOk (g := g) (pop w v rest) := by
  obtain ⟨-, hve, -, htk, hle, -⟩ := top_facts hS hp
  have hlen : w.taken v = (g.adj v).length := by
    have := List.getElem?_eq_none_iff.mp hx
    omega
  intro y hy
  obtain ⟨h1, h2, h3, h4⟩ := hS.2.2.1 y hy
  have hpop : (pop w v rest).onPath y = true ↔ ∃ fr ∈ rest, fr.vertex = y := by
    simp [onPath, pop]
  have hw : w.onPath y = true ↔ v = y ∨ ∃ fr ∈ rest, fr.vertex = y := by simp [onPath, hp]
  by_cases hyv : y = v
  · have hnot : ¬ (pop w v rest).onPath y = true := fun h => by
      obtain ⟨fr, hfr, hpl⟩ := hpop.mp h
      exact not_mem_rest hS hp hfr (hpl.trans hyv)
    rw [hyv] at hnot ⊢
    refine ⟨⟨fun _ => Or.inr (by simp [pop]), fun _ => hve⟩, fun h => hnot h.1, fun _ => hlen,
      fun h => absurd h hve⟩
  · have hon : (pop w v rest).onPath y = w.onPath y := by
      rw [Bool.eq_iff_iff, hpop, hw]
      simp [Ne.symm hyv]
    rw [hon]
    simp only [pop, Function.update_of_ne hyv]
    exact ⟨h1, h2, h3, h4⟩

theorem openBelow_pop (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    OpenBelow (g := g) (pop w v rest) := by
  intro u hun hu y hy hye hle
  rw [anc_congr (w' := pop w v rest) (w := w) rfl rfl]
  have hu' : w.onPath u = true := by
    simp only [onPath, pop] at hu
    simp [onPath, hp, hu]
  exact hS.2.2.2.2.1 u hun hu' y hy hye hle

theorem outerOk_pop (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    OuterOk (g := g) (pop w v rest) := by
  obtain ⟨h1, -, h3⟩ := hS.2.2.2.2.2.2.1
  obtain ⟨-, hve, -⟩ := top_facts hS hp
  rw [hp] at h3
  refine ⟨h1, fun hr y hy => ?_, fun fr hfr => ?_⟩
  · have hr' : rest = [] := hr
    subst hr'
    obtain ⟨h4, h5⟩ := h3 ⟨v, arr, i⟩ rfl
    have h4' : v + 1 = w.next := h4
    refine ⟨fun hyn => ?_, fun hye => ?_⟩
    · have hyn' : y < w.next := hyn
      by_cases hyv : y = v
      · rw [hyv]
        exact hve
      · exact (hS.2.2.1 y hy).1.mpr (Or.inr (h5 y (by change y < v; omega)))
    · change Function.update w.finished v true y = true
      by_cases hyv : y = v
      · simp [hyv]
      · rw [Function.update_of_ne hyv]
        rcases (hS.2.2.1 y hy).1.mp hye with hon | hf
        · simp [onPath, hp] at hon
          exact absurd hon.symm hyv
        · exact hf
  · rcases rest with _ | ⟨b, l⟩
    · simp [pop] at hfr
    · obtain ⟨h4, h5⟩ := h3 fr (by rw [List.getLast?_cons_cons]; exact hfr)
      refine ⟨h4, fun y hy => ?_⟩
      change Function.update w.finished v true y = true
      by_cases hyv : y = v
      · simp [hyv]
      · rw [Function.update_of_ne hyv]
        exact h5 y hy

theorem childrenOk_pop (hS : Shape (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    ChildrenOk (g := g) (pop w v rest) := by
  intro fr hfr
  rcases rest with _ | ⟨b, l⟩
  · simp [pop] at hfr
  · exact hS.2.2.2.2.2.2.2.1 fr (by rw [hp, List.getLast?_cons_cons]; exact hfr)

theorem outside_pop (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) : Outside (g := g) (pop w v rest) := by
  intro y hy
  have hyv : y ≠ v := by
    have := (top_facts hS hp).1
    omega
  simp only [pop, Function.update_of_ne hyv]
  exact hO y hy

end Pop

/-! ## One step -/

variable {w : Walk}

/-- **The start**: nothing entered, nothing on the stack, nothing found; the whole shape holds. -/
theorem shape_start : Shape (g := g) (start g) ∧ Outside (g := g) (start g) := by
  simp [Shape, Outside, EntriesOk, PathOk, StatusOk, TreeOk, OpenBelow, TakenOk, OuterOk,
    ChildrenOk, ClimbBackIsEarliest, StackOk, BlocksOk, BridgesOk, CutOk, Taken, start,
    looked, onPath, BlockTop, LoneRoot, IsGroupOf, EmptyAt]

/-- **A step touches nothing beyond the vertices of the graph.** -/
theorem outside_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w) :
    Outside (g := g) (step g w) := by
  have key : ∀ X : Walk, core (step g w) = core X → Outside (g := g) X →
      (∀ y ≥ g.n, (step g w).cut y = X.cut y) → Outside (g := g) (step g w) := by
    intro X h hX hc y hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hX y hy
    have he : (step g w).entry = X.entry := by have := congrArg Walk.entry h; exact this
    have hf : (step g w).finished = X.finished := by
      have := congrArg Walk.finished h; exact this
    have ht : (step g w).taken = X.taken := by have := congrArg Walk.taken h; exact this
    have ha : (step g w).arrival = X.arrival := by
      have := congrArg Walk.arrival h; exact this
    rw [he, hf, ht, ha, hc y hy]
    exact ⟨h1, h2, h3, h4, h5⟩
  rcases step_cases (g := g) w with ⟨-, hn, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, hc⟩ | ⟨-, h, hc⟩⟩ |
    ⟨v, arr, i, rest, hp, -, h, hc⟩
  · rw [h]
    exact outside_newRoot hO hn
  · rw [h]
    exact hO
  · rw [h]
    exact hO
  · rw [h]
    exact outside_tick hS hO hp
  · exact key _ h (outside_tick hS hO hp) (fun y _ => by rw [hc]; rfl)
  · exact key _ h (outside_descend hS hO hp hx) (fun y _ => by rw [hc]; rfl)
  · refine key _ h (outside_pop hS hO hp) (fun y hy => ?_)
    rcases hc y with hc | hyv | ⟨fr, hfr, hpl⟩
    · exact hc
    · exact absurd hy (not_le.mpr (hyv ▸ (top_facts hS hp).1))
    · have := (hS.2.1.2.2.2 fr (by rw [hp]; exact List.mem_cons_of_mem _ hfr)).1
      rw [hpl] at this
      exact absurd hy (not_le.mpr this)

/-- **A step keeps the entry numbers right**: given to vertices once each, counted by `time`. -/
theorem entriesOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w)
    (_hO : Outside (g := g) w) :
    EntriesOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨-, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, -, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, -, -, h, -⟩
  · rw [h]
    exact entriesOk_newRoot hS hn h0
  · rw [h]
    exact hS.1
  · rw [h]
    exact hS.1
  · rw [h]
    exact hS.1
  · exact of_core (P := EntriesOk (g := g)) entriesOk_core h hS.1
  · exact of_core (P := EntriesOk (g := g)) entriesOk_core h (entriesOk_descend hS hx h0)
  · exact of_core (P := EntriesOk (g := g)) entriesOk_core h hS.1

/-- **A step keeps the path right**: distinct open vertices, each hanging from the one below. -/
theorem pathOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w)
    (_hO : Outside (g := g) w) :
    PathOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨hp, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, hp, -, h, -⟩
  · rw [h]
    exact pathOk_newRoot hS hp hn h0
  · rw [h]
    exact hS.2.1
  · rw [h]
    exact hS.2.1
  · rw [h]
    exact pathOk_tick hS hp hx
  · exact of_core (P := PathOk (g := g)) pathOk_core h (pathOk_tick hS hp hx)
  · exact of_core (P := PathOk (g := g)) pathOk_core h (pathOk_descend hS hp hx h0)
  · exact of_core (P := PathOk (g := g)) pathOk_core h (pathOk_pop hS hp)

/-- **A step keeps each vertex's status right**: not entered, open or finished. -/
theorem statusOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w)
    (_hO : Outside (g := g) w) :
    StatusOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨-, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, hp, hx, h, -⟩
  · rw [h]
    exact statusOk_newRoot hS hn h0
  · rw [h]
    exact hS.2.2.1
  · rw [h]
    exact hS.2.2.1
  · rw [h]
    exact statusOk_tick hS hp
  · exact of_core (P := StatusOk (g := g)) statusOk_core h (statusOk_tick hS hp)
  · exact of_core (P := StatusOk (g := g)) statusOk_core h (statusOk_descend hS hp hx h0)
  · exact of_core (P := StatusOk (g := g)) statusOk_core h (statusOk_pop hS hp hx)

/-- **A step keeps the tree right**: each vertex hangs by its arrival link from an earlier one. -/
theorem treeOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w)
    (_hO : Outside (g := g) w) :
    TreeOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨-, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, -, -, h, -⟩
  · rw [h]
    exact treeOk_newRoot hS h0
  · rw [h]
    exact hS.2.2.2.1
  · rw [h]
    exact hS.2.2.2.1
  · rw [h]
    exact hS.2.2.2.1
  · exact of_core (P := TreeOk (g := g)) treeOk_core h hS.2.2.2.1
  · exact of_core (P := TreeOk (g := g)) treeOk_core h (treeOk_descend hS hp hx h0)
  · exact of_core (P := TreeOk (g := g)) treeOk_core h hS.2.2.2.1

/-- **A step keeps every vertex entered after an open vertex below it.** -/
theorem openBelow_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w) :
    OpenBelow (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨hp, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, hp, -, h, -⟩
  · rw [h]
    exact openBelow_newRoot hS hO hp h0
  · rw [h]
    exact (openBelow_congr (w := w) (w' := { w with next := w.next + 1 }) rfl rfl rfl
      rfl).mpr hS.2.2.2.2.1
  · rw [h]
    exact hS.2.2.2.2.1
  · rw [h]
    exact openBelow_tick hS hp
  · exact of_core (P := OpenBelow (g := g)) openBelow_core h (openBelow_tick hS hp)
  · exact of_core (P := OpenBelow (g := g)) openBelow_core h
      (openBelow_descend hS hO hp hx h0)
  · exact of_core (P := OpenBelow (g := g)) openBelow_core h (openBelow_pop hS hp)

/-- **A step keeps every row entry taken leading above or below.** -/
theorem takenOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w) :
    TakenOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨-, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨hc, h⟩ | ⟨hc, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, -, -, h, -⟩
  · rw [h]
    exact takenOk_newRoot hS hO hn h0
  · rw [h]
    exact (takenOk_congr (w := w) (w' := { w with next := w.next + 1 }) rfl rfl rfl
      rfl).mpr hS.2.2.2.2.2.1
  · rw [h]
    exact hS.2.2.2.2.2.1
  · rw [h]
    exact takenOk_tick hS hp hx (taken_entry hS hO hp hx (hc.elim Or.inl (Or.inr ∘ Or.inl)))
  · exact of_core (P := TakenOk (g := g)) takenOk_core h
      (takenOk_tick hS hp hx (taken_entry hS hO hp hx (Or.inr (Or.inr hc.2))))
  · exact of_core (P := TakenOk (g := g)) takenOk_core h (takenOk_descend hS hO hp hx h0)
  · exact of_core (P := TakenOk (g := g)) takenOk_core h
      ((takenOk_congr (w := w) (w' := pop w v rest) rfl rfl rfl rfl).mpr hS.2.2.2.2.2.1)

/-- **A step keeps the outer loop right.** -/
theorem outerOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w)
    (_hO : Outside (g := g) w) :
    OuterOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨hp, hn, -, h⟩ | ⟨hp, hn, h0, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, -, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩⟩ |
    ⟨v, arr, i, rest, hp, -, h, -⟩
  · rw [h]
    exact outerOk_newRoot hS hp hn
  · rw [h]
    exact outerOk_next hS hp hn h0
  · rw [h]
    exact hS.2.2.2.2.2.2.1
  · rw [h]
    exact outerOk_tick hS hp
  · exact of_core (P := OuterOk (g := g)) outerOk_core h (outerOk_tick hS hp)
  · exact of_core (P := OuterOk (g := g)) outerOk_core h (outerOk_descend hS hp)
  · exact of_core (P := OuterOk (g := g)) outerOk_core h (outerOk_pop hS hp)

/-- **A step keeps the count of the current root's children.** -/
theorem childrenOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w)
    (hO : Outside (g := g) w) : ChildrenOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨hp, -, h0, h⟩ | ⟨hp, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, hp, -, h, -⟩
  · rw [h]
    exact childrenOk_newRoot hS hO hp h0
  · rw [h]
    exact fun fr hfr => by simp [hp] at hfr
  · rw [h]
    exact hS.2.2.2.2.2.2.2.1
  · rw [h]
    exact childrenOk_tick hS hp
  · exact of_core (P := ChildrenOk (g := g)) childrenOk_core h (childrenOk_tick hS hp)
  · exact of_core (P := ChildrenOk (g := g)) childrenOk_core h
      (childrenOk_descend hS hp hx h0)
  · exact of_core (P := ChildrenOk (g := g)) childrenOk_core h (childrenOk_pop hS hp)

end Walk

end AlgoDesign.Graphs.Blocks
