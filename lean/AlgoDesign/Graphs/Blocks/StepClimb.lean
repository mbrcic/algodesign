/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.StepShape
public import AlgoDesign.Graphs.Blocks.Groups

/-!
# Bridges, cut vertices and blocks: one step keeps the climb-back numbers and the stack

One step of the walk keeps `OpenTaken` and `RootsOk`, the climb-back numbers
(`ClimbBackIsEarliest`), and the edge stack's contents and order (`StackOk`). The finer case
split `stack_step_moves` names the walk after each of the step's moves; `popBlock` cuts the stack
after the link it pops down to, and a link other than a loop appears once in a row.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable {g : Graph}

/-! ## Pieces read through `core` -/

theorem climb_openTaken_core (w : Walk) : OpenTaken (g := g) (core w) ↔ OpenTaken (g := g) w :=
  Iff.rfl

theorem climb_rootsOk_congr {w w' : Walk} (he : w'.entry = w.entry) (ha : w'.arrival = w.arrival)
    (hu : w'.up = w.up) : RootsOk (g := g) w' ↔ RootsOk (g := g) w := by
  unfold RootsOk
  rw [anc_congr ha hu, he, ha]

theorem climb_rootsOk_core (w : Walk) : RootsOk (g := g) (core w) ↔ RootsOk (g := g) w :=
  climb_rootsOk_congr rfl rfl rfl

/-- Reading `Above` back through `enter`: away from the new vertex, the tree is the old one. -/
theorem climb_above_of_enter {p : Walk} {x u : ℕ} {arr : Option ℕ}
    (hup : ∀ z, p.arrival z ≠ none → p.up z ≠ x) {a y : ℕ}
    (h : Above (enter p x arr u) a y) (hy : y ≠ x) : Above p a y ∧ a ≠ x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨Above.refl p _, hy⟩
  | @head b c hbc _ ih =>
    obtain ⟨h1, hcx⟩ := ih
    obtain ⟨hca, hcb⟩ := hbc
    simp only [enter, Function.update_of_ne hcx] at hca hcb
    subst hcb
    exact ⟨(Above.up hca).trans h1, hup c hca⟩

section Shape

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
variable {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame} {x e : ℕ}

include hS hO in
/-- No vertex hangs from a vertex not entered. -/
theorem climb_up_ne_of_zero (h0 : w.entry x = 0) : ∀ z, w.arrival z ≠ none → w.up z ≠ x :=
  fun z hz h => (hangs hS hO z hz).2.2.2.1 (by rw [h]; exact h0)

/-! ## `OpenTaken` -/

include hS in
theorem climb_openTaken_newRoot (hp : w.path = []) (hn : w.next < g.n) (h0 : w.entry w.next = 0) :
    OpenTaken (g := g) (newRoot w) := by
  intro y _ hyon s hs
  have hy : y = w.next := by
    simpa [onPath, newRoot, enter, hp, eq_comm] using hyon
  subst hy
  have := ((hS.2.2.1 w.next hn).2.2.2 h0).1
  simp [looked, newRoot, enter, this] at hs

include hS hO in
theorem climb_openTaken_tick (hT : OpenTaken (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) : OpenTaken (g := g) (tick w v arr i rest) := by
  intro y hy hyon s hs hson hlt
  have hon : ∀ z, (tick w v arr i rest).onPath z = w.onPath z := fun z => by
    simp [onPath, tick, hp]
  rw [hon] at hyon hson
  rcases mem_looked_tick hS hp hx hs with hs | ⟨rfl, rfl⟩
  · exact hT y hy hyon s hs hson hlt
  · exfalso
    have hlt' : w.entry y < w.entry x := hlt
    have h2 : w.entry x ≤ w.entry y :=
      (entry_le_of_above hS hO (above_top hS hp hson) (top_facts hS hp).2.1).2.1
    omega

include hS in
theorem climb_openTaken_descend (hT : OpenTaken (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) :
    OpenTaken (g := g) (descend w v arr i rest x e) := by
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  have htx : w.taken x = 0 := ((hS.2.2.1 x hxn).2.2.2 h0).1
  have hxv : x ≠ v := fun h => (top_facts hS hp).2.1 (h ▸ h0)
  have hon : ∀ z, (descend w v arr i rest x e).onPath z = true ↔ x = z ∨ w.onPath z = true :=
    fun z => by simp [descend, onPath, enter, tick, hp]
  intro y hy hyon s hs hson hlt
  by_cases hyx : y = x
  · subst hyx
    simp [looked, descend, enter, tick, Function.update_of_ne hxv, htx] at hs
  · have hs' : s ∈ looked (g := g) (tick w v arr i rest) y := hs
    rcases mem_looked_tick hS hp hx hs' with hs | ⟨rfl, rfl⟩
    · have hsx : s.1 ≠ x := fun h => (hS.2.2.2.2.2.1 y hy s hs).1 (h ▸ h0)
      have hyon' := ((hon y).mp hyon).resolve_left (Ne.symm hyx)
      have hson' := ((hon s.1).mp hson).resolve_left (Ne.symm hsx)
      simp only [descend, enter, Function.update_of_ne hyx, Function.update_of_ne hsx] at hlt ⊢
      exact hT y hy hyon' s hs hson' hlt
    · simp [descend, enter]

theorem climb_openTaken_pop (hT : OpenTaken (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest) :
    OpenTaken (g := g) (pop w v rest) := by
  intro y hy hyon s hs hson hlt
  have hon : ∀ z, (pop w v rest).onPath z = true → w.onPath z = true := fun z h => by
    simp only [onPath, pop] at h
    simp [onPath, hp, h]
  exact hT y hy (hon y hyon) s hs (hon _ hson) hlt

/-! ## `RootsOk` -/

include hS hO in
theorem climb_rootsOk_newRoot (hR : RootsOk (g := g) w) (h0 : w.entry w.next = 0) :
    RootsOk (g := g) (newRoot w) := by
  intro y hy hye r hr hanc hra
  rw [anc_iff_newRoot hS hO h0] at hanc
  have hanc' : Above (enter { w with next := w.next + 1, children := 0 } w.next none w.next) r y :=
    hanc
  by_cases hyx : y = w.next
  · subst hyx
    have := above_root (by simp [newRoot, enter]) hanc
    omega
  · obtain ⟨hab, hrx⟩ := climb_above_of_enter (climb_up_ne_of_zero hS hO h0) hanc' hyx
    have hye' : w.entry y ≠ 0 := by simpa [newRoot, enter, Function.update_of_ne hyx] using hye
    have hra' : w.arrival r = none := by
      simpa [newRoot, enter, Function.update_of_ne hrx] using hra
    exact hR y hy hye' r hr ((anc_iff hS hO r y).mpr hab) hra'

include hS hO in
theorem climb_rootsOk_descend (hR : RootsOk (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (h0 : w.entry x = 0) :
    RootsOk (g := g) (descend w v arr i rest x e) := by
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  have hxv : x ≠ v := fun h => (top_facts hS hp).2.1 (h ▸ h0)
  have hup := climb_up_ne_of_zero hS hO h0
  intro y hy hye r hr hanc hra
  rw [anc_iff_descend hS hO hp h0] at hanc
  have hanc' : Above (enter { tick w v arr i rest with
      children := if rest.isEmpty then w.children + 1 else w.children } x (some e) v) r y := hanc
  by_cases hyx : y = x
  · subst hyx
    rcases above_iff.mp hanc' with hry | ⟨-, hrv⟩
    · subst hry
      simp [descend, enter] at hra
    · simp only [enter, Function.update_self] at hrv
      obtain ⟨hab, hrx⟩ := climb_above_of_enter hup hrv (Ne.symm hxv)
      have hra' : w.arrival r = none := by
        simpa [descend, enter, tick, Function.update_of_ne hrx] using hra
      rcases hl : w.path.getLast? with _ | fr
      · simp [hp] at hl
      have hfr : fr ∈ w.path := List.mem_of_getLast? hl
      obtain ⟨-, -, hlast, hall⟩ := hS.2.1
      have hfa : w.arrival fr.vertex = none := ((hall fr hfr).2.2.1).trans (hlast fr hl)
      have hbv := above_top hS hp ((onPath_iff fr.vertex).mpr ⟨fr, hfr, rfl⟩)
      have hrb : r = fr.vertex := by
        rcases above_total hab hbv with h | h
        · exact above_root hfa h
        · exact (above_root hra' h).symm
      obtain ⟨-, -, hout⟩ := hS.2.2.2.2.2.2.1
      have hnf : w.finished y = false := by
        by_contra hf
        exact ((hS.2.2.1 y hxn).1.mpr (Or.inr (by simpa using hf))) h0
      by_contra hlt
      have := (hout fr hl).2 y (by omega)
      simp_all
  · obtain ⟨hab, hrx⟩ := climb_above_of_enter hup hanc' hyx
    have hye' : w.entry y ≠ 0 := by
      simpa [descend, enter, tick, Function.update_of_ne hyx] using hye
    have hra' : w.arrival r = none := by
      simpa [descend, enter, tick, Function.update_of_ne hrx] using hra
    exact hR y hy hye' r hr ((anc_iff hS hO r y).mpr hab) hra'

end Shape

variable {w : Walk}

/-- **A step keeps the rule on open vertices' taken entries**: an open vertex has taken an entry to
an open vertex below it only by descending to it. -/
theorem openTaken_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hT : OpenTaken (g := g) w) : OpenTaken (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨hp, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, hp, -, h, -⟩
  · rw [h]
    exact climb_openTaken_newRoot hS hp hn h0
  · rw [h]
    exact hT
  · rw [h]
    exact hT
  · rw [h]
    exact climb_openTaken_tick hS hO hT hp hx
  · exact of_core (P := OpenTaken (g := g)) climb_openTaken_core h
      (climb_openTaken_tick hS hO hT hp hx)
  · exact of_core (P := OpenTaken (g := g)) climb_openTaken_core h
      (climb_openTaken_descend hS hT hp hx h0)
  · exact of_core (P := OpenTaken (g := g)) climb_openTaken_core h (climb_openTaken_pop hT hp)

/-- **At the start no vertex is open**, so `OpenTaken` holds. -/
theorem openTaken_start : OpenTaken (g := g) (start g) := by
  intro x _ hx
  simp [onPath, start] at hx

/-- **A step keeps each tree's root its smallest vertex.** -/
theorem rootsOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (_hT : OpenTaken (g := g) w) (hR : RootsOk (g := g) w) : RootsOk (g := g) (step g w) := by
  rcases step_cases (g := g) w with ⟨-, -, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨h0, h, -⟩⟩ |
    ⟨v, arr, i, rest, -, -, h, -⟩
  · rw [h]
    exact climb_rootsOk_newRoot hS hO hR h0
  · rw [h]
    exact (climb_rootsOk_congr (w := w) (w' := { w with next := w.next + 1 }) rfl rfl rfl).mpr hR
  · rw [h]
    exact hR
  · rw [h]
    exact (climb_rootsOk_congr (w := w) (w' := tick w v arr i rest) rfl rfl rfl).mpr hR
  · exact of_core (P := RootsOk (g := g)) climb_rootsOk_core h
      ((climb_rootsOk_congr (w := w) (w' := tick w v arr i rest) rfl rfl rfl).mpr hR)
  · exact of_core (P := RootsOk (g := g)) climb_rootsOk_core h
      (climb_rootsOk_descend hS hO hR hp hx h0)
  · exact of_core (P := RootsOk (g := g)) climb_rootsOk_core h
      ((climb_rootsOk_congr (w := w) (w' := pop w v rest) rfl rfl rfl).mpr hR)

/-- **At the start nothing is entered**, so `RootsOk` holds. -/
theorem rootsOk_start : RootsOk (g := g) (start g) := by
  intro x _ hx
  simp [start] at hx

/-! ## The moves of a step, in full -/

/-- **The moves of a step**, with the whole walk after each: enter a new root, move the outer loop
on, nothing, take a row entry and skip it, take a row entry and push a link back, take a row entry
and descend, finish a vertex under another, finish a root. -/
theorem stack_step_moves (w : Walk) :
    (w.path = [] ∧ w.next < g.n ∧ w.entry w.next = 0 ∧ step g w = newRoot w) ∨
    (w.path = [] ∧ w.next < g.n ∧ w.entry w.next ≠ 0 ∧
      step g w = { w with next := w.next + 1 }) ∨
    (w.path = [] ∧ g.n ≤ w.next ∧ step g w = w) ∨
    (∃ v arr i rest x e, w.path = ⟨v, arr, i⟩ :: rest ∧ (g.adj v)[i]? = some (x, e) ∧
      ((x = v ∨ arr = some e ∨ (w.entry x ≠ 0 ∧ w.entry v ≤ w.entry x)) ∧
          step g w = tick w v arr i rest ∨
        (x ≠ v ∧ arr ≠ some e ∧ w.entry x ≠ 0 ∧ w.entry x < w.entry v) ∧
          step g w = { tick w v arr i rest with
            edges := e :: w.edges, low := Function.update w.low v (min (w.low v) (w.entry x)) } ∨
        (x ≠ v ∧ arr ≠ some e ∧ w.entry x = 0) ∧
          step g w = { descend w v arr i rest x e with edges := e :: w.edges })) ∨
    (∃ v e i u a j above, w.path = ⟨v, some e, i⟩ :: ⟨u, a, j⟩ :: above ∧
      (g.adj v)[i]? = none ∧
      step g w = finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty) ∨
    (∃ v arr i rest, w.path = ⟨v, arr, i⟩ :: rest ∧ (g.adj v)[i]? = none ∧
      (rest = [] ∨ arr = none) ∧ step g w = finishRoot (pop w v rest) v) := by
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
      simp only [hx]
      rcases rest with _ | ⟨⟨u, a, j⟩, above⟩ <;> rcases arr with _ | e
      · exact Or.inr ⟨v, none, i, [], rfl, hx, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨v, some e, i, [], rfl, hx, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨_, none, i, _, rfl, hx, Or.inr rfl, rfl⟩
      · exact Or.inl ⟨v, e, i, u, a, j, above, rfl, hx, rfl⟩
    · left
      refine ⟨v, arr, i, rest, x, e, rfl, hx, ?_⟩
      simp only [hx]
      unfold look
      dsimp only
      by_cases h1 : x = v ∨ arr = some e
      · exact Or.inl ⟨h1.elim Or.inl (Or.inr ∘ Or.inl), by rw [ite_eq_left h1]; rfl⟩
      · rw [ite_eq_right h1]
        have hxv : x ≠ v := fun h => h1 (Or.inl h)
        have hae : arr ≠ some e := fun h => h1 (Or.inr h)
        by_cases h2 : w.entry x = 0
        · rw [ite_eq_left h2]
          exact Or.inr (Or.inr ⟨⟨hxv, hae, h2⟩, rfl⟩)
        · rw [ite_eq_right h2]
          by_cases h3 : w.entry x < w.entry v
          · rw [ite_eq_left h3]
            exact Or.inr (Or.inl ⟨⟨hxv, hae, h2, h3⟩, rfl⟩)
          · rw [ite_eq_right h3]
            exact Or.inl ⟨Or.inr (Or.inr ⟨h2, by omega⟩), rfl⟩

theorem stack_finishUnder_low (w : Walk) (u v e : ℕ) (b : Bool) :
    (finishUnder g w u v e b).low = Function.update w.low u (min (w.low u) (w.low v)) := by
  unfold finishUnder
  dsimp only
  split_ifs <;> rfl

theorem stack_finishUnder_edges (w : Walk) {u v : ℕ} (e : ℕ) (b : Bool) (huv : u ≠ v) :
    (finishUnder g w u v e b).edges =
      if w.entry u ≤ w.low v then (popBlock e w.edges).2 else w.edges := by
  unfold finishUnder
  dsimp only
  simp only [Function.update_of_ne (Ne.symm huv)]
  split_ifs <;> rfl

theorem stack_finishUnder_blocks (w : Walk) {u v : ℕ} (e : ℕ) (b : Bool) (huv : u ≠ v) :
    (finishUnder g w u v e b).blocks =
      if w.entry u ≤ w.low v then w.blocks ++ [(popBlock e w.edges).1] else w.blocks := by
  unfold finishUnder
  dsimp only
  simp only [Function.update_of_ne (Ne.symm huv)]
  split_ifs <;> rfl

theorem stack_finishRoot_fields (w : Walk) (v : ℕ) : (finishRoot w v).low = w.low ∧
    (finishRoot w v).edges = w.edges ∧ (finishRoot w v).blocks.flatten = w.blocks.flatten := by
  unfold finishRoot
  dsimp only
  split_ifs <;> simp

/-- `popBlock e` cuts the stack just after `e`. -/
theorem stack_popBlock_eq (e : ℕ) : ∀ l : List ℕ,
    popBlock e l = (l.take (l.idxOf e + 1), l.drop (l.idxOf e + 1))
  | [] => rfl
  | x :: rest => by
    unfold popBlock
    by_cases h : x = e
    · subst h
      simp
    · simp only [h, ↓reduceIte]
      rw [stack_popBlock_eq e rest, List.idxOf_cons_ne _ h]
      simp

/-! ## A row lists a link other than a loop once -/

/-- The entries of a row leading away from the vertex are all different. -/
theorem stack_adj_filter_nodup (v : ℕ) : ((g.adj v).filter fun s => s.1 ≠ v).Nodup := by
  unfold Graph.adj
  rw [List.filter_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun y _ => ?_, ?_⟩
  · by_cases hyv : y = v
    · subst hyv
      rw [List.filter_eq_nil_iff.mpr (fun s hs => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
        simp)]
      exact List.nodup_nil
    · rw [List.filter_eq_self.mpr (fun s hs => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
        simpa using hyv)]
      refine List.Nodup.map (fun a b h => (Prod.mk.inj h).2) ?_
      refine List.nodup_flatMap.mpr ⟨fun k _ => ?_, ?_⟩
      · unfold Graph.entries
        split
        · split_ifs <;> simp_all
        · simp
      · refine List.nodup_range.imp fun {a b} hab z hza hzb => hab ?_
        rw [(mem_entries.mp hza).1] at hzb
        exact (mem_entries.mp hzb).1
  · refine List.nodup_range.imp fun {a b} hab z hza hzb => hab ?_
    simp only [List.mem_filter, List.mem_map] at hza hzb
    obtain ⟨⟨k, -, rfl⟩, -⟩ := hza
    obtain ⟨⟨k', -, h⟩, -⟩ := hzb
    exact (Prod.mk.inj h).1.symm

/-- A row entry to another vertex is not among the entries before it. -/
theorem stack_not_mem_take_adj {v i x e : ℕ} (hx : (g.adj v)[i]? = some (x, e)) (hxv : x ≠ v) :
    (x, e) ∉ (g.adj v).take i := by
  intro hm
  have hnd := stack_adj_filter_nodup (g := g) v
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hx
  rw [← List.take_append_drop i (g.adj v), List.drop_eq_getElem_cons hi, hget,
    List.filter_append, List.nodup_append] at hnd
  exact hnd.2.2 (x, e) (List.mem_filter.mpr ⟨hm, by simpa using hxv⟩) (x, e)
    (List.mem_filter.mpr ⟨List.mem_cons_self, by simpa using hxv⟩) rfl

/-! ## The links taken -/

theorem stack_taken_congr {w₁ w₂ : Walk} (ht : w₂.taken = w₁.taken) (f : ℕ) :
    Taken (g := g) w₂ f ↔ Taken (g := g) w₁ f := by
  unfold Taken looked
  rw [ht]

section Stack

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
variable {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame} {x e : ℕ}

include hS in
/-- Taking a row entry adds its link to the links taken, unless it is a loop. -/
theorem stack_taken_tick (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e))
    (f : ℕ) :
    Taken (g := g) (tick w v arr i rest) f ↔ Taken (g := g) w f ∨ (f = e ∧ NonLoop g e) := by
  have htk := (top_facts hS hp).2.2.2.1
  have hlv : looked (g := g) (tick w v arr i rest) v = looked (g := g) w v ++ [(x, e)] := by
    simp only [looked, tick, Function.update_self, List.take_add_one, hx, Option.toList_some, htk]
  constructor
  · rintro ⟨hnl, y, hy, s, hs, rfl⟩
    rcases mem_looked_tick hS hp hx hs with hs | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hnl, y, hy, s, hs, rfl⟩
    · exact Or.inr ⟨rfl, hnl⟩
  · rintro (⟨hnl, y, hy, s, hs, rfl⟩ | ⟨hfe, hnl⟩)
    · refine ⟨hnl, y, hy, s, ?_, rfl⟩
      by_cases hyv : y = v
      · rw [hyv, hlv]
        rw [hyv] at hs
        exact List.mem_append_left _ hs
      · simpa [looked, tick, Function.update_of_ne hyv] using hs
    · rw [hfe]
      exact ⟨hnl, v, (top_facts hS hp).1, (x, e), by rw [hlv]; simp, rfl⟩

include hS hO in
/-- A link pushed was not taken before: not from the current vertex, which lists it once in its
row, and not from the other end, which has either taken nothing or is open above. -/
theorem stack_not_taken_push (hT : OpenTaken (g := g) w) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (hxv : x ≠ v) (hae : arr ≠ some e)
    (hlt : w.entry x < w.entry v) : ¬ Taken (g := g) w e := by
  obtain ⟨hvn, hve, hva, htk, -, hvon⟩ := top_facts hS hp
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  have hj : Joins g e v x := (mem_adj.mp (List.mem_of_getElem? hx)).2
  rintro ⟨-, y, hy, s, hs, hse⟩
  have hjs : Joins g e y s.1 := hse ▸ joins_of_adj_mem (List.mem_of_mem_take hs)
  rcases Joins.ends hj hjs with ⟨hyv, h1⟩ | ⟨hyx, h1⟩
  · have hs' : s = (x, e) := Prod.ext h1 hse
    rw [hyv, hs'] at hs
    unfold looked at hs
    rw [htk] at hs
    exact stack_not_mem_take_adj hx hxv hs
  · rw [hyx] at hs
    by_cases hx0 : w.entry x = 0
    · have := ((hS.2.2.1 x hxn).2.2.2 hx0).1
      simp [looked, this] at hs
    · have hab := (hS.2.2.2.2.2.1 x hxn s hs).2 (by rw [h1]; exact Ne.symm hxv)
      rw [h1, anc_iff hS hO, anc_iff hS hO] at hab
      rcases hab with hab | hab
      · have := (entry_le_of_above hS hO hab hx0).2.1
        omega
      · rcases (hS.2.2.1 x hxn).1.mp hx0 with hxon | hxf
        · have := hT x hxn hxon s hs (by rw [h1]; exact hvon) (by rw [h1]; exact hlt)
          rw [h1, hse, hva] at this
          exact hae this
        · exact (hS.2.2.1 v hvn).2.1 ⟨hvon, finished_of_above hS hO hab hxf hve⟩

include hS hO in
/-- A link pushed is in no block emitted: its deeper end is the current vertex, still open. -/
theorem stack_not_mem_blocks_push (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) (hlt : w.entry x < w.entry v) :
    e ∉ w.blocks.flatten := by
  obtain ⟨hvn, hve, -, -, -, hvon⟩ := top_facts hS hp
  have hj : Joins g e v x := (mem_adj.mp (List.mem_of_getElem? hx)).2
  intro hm
  obtain ⟨b, hb, heb⟩ := List.mem_flatten.mp hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hbk : w.blocks.getD k [] = w.blocks[k] := by simp [hk]
  have hBO := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨c, -, -, hct, hiff⟩ := hBO.2.2.1 k hk (by rw [hbk]; exact List.ne_nil_of_mem heb)
  rw [hbk] at hiff
  obtain ⟨-, z, -, hdeep, hhead⟩ := (hiff e (joins_lt hj)).mp heb
  have hcz := ((headIs_iff hS hO).mp hhead).1
  have h1 := le_max_left (w.entry v) (w.entry x)
  have h2 := le_max_right (w.entry x) (w.entry v)
  have hzv : z = v := by
    rcases hj with h | h
    · obtain ⟨hz, hmax⟩ := (deep_iff h).mp hdeep
      rcases hz with hz | hz
      · exact hz.symm
      · rw [← hz] at hmax
        omega
    · obtain ⟨hz, hmax⟩ := (deep_iff h).mp hdeep
      rcases hz with hz | hz
      · rw [← hz] at hmax
        omega
      · exact hz.symm
  rw [hzv] at hcz
  exact (hS.2.2.1 v hvn).2.1 ⟨hvon, finished_of_above hS hO hcz hct.1 hve⟩

include hS hO in
/-- A link skipped, other than a loop, was taken before: it is the current vertex's arrival link,
on the stack, or it leads to a finished vertex below, whose whole row was taken. -/
theorem stack_taken_skip (hg : g.WellFormed) (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e))
    (h : x = v ∨ arr = some e ∨ (w.entry x ≠ 0 ∧ w.entry v ≤ w.entry x))
    (hnl : NonLoop g e) : Taken (g := g) w e := by
  obtain ⟨hvn, hve, hva, -, -, hvon⟩ := top_facts hS hp
  have hxn : x < g.n := (mem_adj.mp (List.mem_of_getElem? hx)).1
  have hj : Joins g e v x := (mem_adj.mp (List.mem_of_getElem? hx)).2
  have hxv : x ≠ v := by
    intro hxv
    rw [hxv] at hj
    obtain ⟨l, hl, hne⟩ := hnl
    rcases hj with hj | hj <;>
    · simp only [Option.mem_def, hj, Option.some.injEq] at hl
      rw [← hl] at hne
      exact hne rfl
  rcases h with hxv' | hae | ⟨hxe, hle⟩
  · exact absurd hxv' hxv
  · have hfr := hS.2.2.2.2.2.2.2.2.2.2.2.1.2 ⟨v, arr, i⟩ (by rw [hp]; simp) e (by rw [hae]; rfl)
    exact ((hS.2.2.2.2.2.2.2.2.2.2.1 e (joins_lt hj)).mp hfr.1).1
  · have hxf : w.finished x = true := by
      rcases (hS.2.2.1 x hxn).1.mp hxe with hxon | hxf
      · have := (entry_le_of_above hS hO (above_top hS hp hxon) hve).2.1
        exact absurd (entry_inj hS hO hxe (by omega)) hxv
      · exact hxf
    refine ⟨hnl, x, hxn, (v, e), ?_, rfl⟩
    rw [looked_of_finished hS hxn hxf]
    exact adj_mem_of_joins hg hj.symm

end Stack

/-- **A step keeps the edge stack free of repeats.** -/
theorem edges_nodup_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hT : OpenTaken (g := g) w) : (step g w).edges.Nodup := by
  have hnd : w.edges.Nodup := hS.2.2.2.2.2.2.2.2.2.1
  have hE := hS.2.2.2.2.2.2.2.2.2.2.1
  rcases stack_step_moves (g := g) w with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨⟨hxv, hae, -, hlt⟩, h⟩ | ⟨⟨hxv, hae, h0⟩, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, -, -, -, h⟩
  all_goals rw [h]
  · exact hnd
  · exact hnd
  · exact hnd
  · exact hnd
  · have hj := (mem_adj.mp (List.mem_of_getElem? hx)).2
    exact List.nodup_cons.mpr ⟨fun hm => stack_not_taken_push hS hO hT hp hx hxv hae hlt
      ((hE e (joins_lt hj)).mp hm).1, hnd⟩
  · have hj := (mem_adj.mp (List.mem_of_getElem? hx)).2
    have hlt : w.entry x < w.entry v := by
      have := (top_facts hS hp).2.1
      omega
    exact List.nodup_cons.mpr ⟨fun hm => stack_not_taken_push hS hO hT hp hx hxv hae hlt
      ((hE e (joins_lt hj)).mp hm).1, hnd⟩
  · have huv : u ≠ v := not_mem_rest hS hp (fr := ⟨u, a, j⟩) List.mem_cons_self
    rw [stack_finishUnder_edges _ _ _ huv]
    split_ifs
    · rw [stack_popBlock_eq]
      exact hnd.sublist (List.drop_sublist _ _)
    · exact hnd
  · rw [(stack_finishRoot_fields _ _).2.1]
    exact hnd

/-- **A step keeps the stack's contents**: exactly the links taken and in no block emitted. -/
theorem edges_iff_step (hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (_hT : OpenTaken (g := g) w) : ∀ f < g.links.length,
    f ∈ (step g w).edges ↔ Taken (g := g) (step g w) f ∧ f ∉ (step g w).blocks.flatten := by
  have hnd : w.edges.Nodup := hS.2.2.2.2.2.2.2.2.2.1
  have hE := hS.2.2.2.2.2.2.2.2.2.2.1
  rcases stack_step_moves (g := g) w with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨hc, h⟩ | ⟨⟨hxv, hae, -, hlt⟩, h⟩ | ⟨⟨hxv, hae, h0⟩, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, -, -, -, h⟩
  all_goals rw [h]
  · intro f hf
    rw [stack_taken_congr (w₁ := w) (w₂ := newRoot w) rfl]
    exact hE f hf
  · intro f hf
    rw [stack_taken_congr (w₁ := w) (w₂ := { w with next := w.next + 1 }) rfl]
    exact hE f hf
  · exact hE
  · intro f hf
    rw [stack_taken_tick hS hp hx]
    refine (hE f hf).trans ⟨fun ⟨ht, hb⟩ => ⟨Or.inl ht, hb⟩, ?_⟩
    rintro ⟨ht | ⟨hfe, hnl⟩, hb⟩
    · exact ⟨ht, hb⟩
    · exact ⟨hfe ▸ stack_taken_skip hS hO hg hp hx hc hnl, hb⟩
  all_goals first
    | (have hlt' : w.entry x < w.entry v := by
          have := (top_facts hS hp).2.1
          omega
       have hj := (mem_adj.mp (List.mem_of_getElem? hx)).2
       have hnl : NonLoop g e := nonLoop_of_joins hj (Ne.symm hxv)
       have hnb := stack_not_mem_blocks_push hS hO hp hx hlt'
       intro f hf
       change f ∈ e :: w.edges ↔ Taken (g := g) (tick w v arr i rest) f ∧ f ∉ w.blocks.flatten
       rw [List.mem_cons, hE f hf, stack_taken_tick hS hp hx]
       constructor
       · rintro (rfl | ⟨ht, hb⟩)
         · exact ⟨Or.inr ⟨rfl, hnl⟩, hnb⟩
         · exact ⟨Or.inl ht, hb⟩
       · rintro ⟨ht | ⟨hfe, -⟩, hb⟩
         · exact Or.inr ⟨ht, hb⟩
         · exact Or.inl hfe)
    | skip
  · have huv : u ≠ v := not_mem_rest hS hp (fr := ⟨u, a, j⟩) List.mem_cons_self
    have ht : (finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty).taken =
        w.taken := by
      have := congrArg Walk.taken
        (core_finishUnder (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty)
      exact this
    intro f hf
    rw [stack_finishUnder_edges _ _ _ huv, stack_finishUnder_blocks _ _ _ huv, stack_taken_congr ht]
    split_ifs
    · rw [stack_popBlock_eq]
      simp only [pop]
      have hsplit := List.take_append_drop (w.edges.idxOf e + 1) w.edges
      have hnd' := hsplit.symm ▸ hnd
      rw [List.nodup_append] at hnd'
      rw [List.flatten_append, List.mem_append, List.flatten_singleton]
      constructor
      · intro hd
        obtain ⟨ht, hb⟩ := (hE f hf).mp (List.mem_of_mem_drop hd)
        exact ⟨ht, fun hm => hm.elim hb (fun hm => hnd'.2.2 f hm f hd rfl)⟩
      · rintro ⟨ht, hb⟩
        have hm := (hE f hf).mpr ⟨ht, fun h => hb (Or.inl h)⟩
        rw [← hsplit, List.mem_append] at hm
        exact hm.resolve_left (fun h => hb (Or.inr h))
    · exact hE f hf
  · have ht : (finishRoot (pop w v rest) v).taken = w.taken := by
      have := congrArg Walk.taken (core_finishRoot (pop w v rest) v)
      exact this
    intro f hf
    rw [(stack_finishRoot_fields _ _).2.1, (stack_finishRoot_fields _ _).2.2, stack_taken_congr ht]
    exact hE f hf

/-! ## The stack's order -/

theorem stack_deepEntry_eq {W : Walk} {f p q : ℕ} (hl : g.links[f]? = some (p, q)) :
    deepEntry (g := g) W f = max (W.entry p) (W.entry q) := by
  simp [deepEntry, hl]

theorem stack_deepEntry_joins {W : Walk} {f p q : ℕ} (h : Joins g f p q) :
    deepEntry (g := g) W f = max (W.entry p) (W.entry q) := by
  rcases h with h | h
  · exact stack_deepEntry_eq h
  · rw [stack_deepEntry_eq h, max_comm]

theorem stack_deepEntry_congr {W₁ W₂ : Walk} (he : W₂.entry = W₁.entry) :
    deepEntry (g := g) W₂ = deepEntry (g := g) W₁ := by
  funext f
  simp only [deepEntry, he]

theorem stack_getD_eq {l : List ℕ} {j : ℕ} (h : j < l.length) : l.getD j 0 = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The stack's order is kept when the stack and the entry numbers are, and every frame's vertex
and arrival link were a frame's before. -/
theorem stack_frames {W₁ W₂ : Walk} (h : StackOk (g := g) W₁) (he : W₂.edges = W₁.edges)
    (hent : W₂.entry = W₁.entry)
    (hfr : ∀ fr ∈ W₂.path, ∃ fr' ∈ W₁.path, fr'.vertex = fr.vertex ∧ fr'.arrival = fr.arrival) :
    StackOk (g := g) W₂ := by
  refine ⟨he ▸ h.1, fun fr hfr' a ha => ?_⟩
  obtain ⟨fr0, h0, hpl, har⟩ := hfr fr hfr'
  have := h.2 fr0 h0 a (har ▸ ha)
  rw [he, stack_deepEntry_congr hent, hent, ← hpl]
  exact this

/-- A frame's split of the stack survives a push of a link entered no earlier than its vertex. -/
theorem stack_push_cond {E : List ℕ} {e a t : ℕ} {D D₀ : ℕ → ℕ}
    (hold : a ∈ E ∧ ∀ j < E.length, (j < E.idxOf a → t ≤ D₀ (E.getD j 0)) ∧
      (E.idxOf a < j → D₀ (E.getD j 0) < t))
    (hae : e ≠ a) (hD : ∀ f ∈ E, D f = D₀ f) (htop : t ≤ D e) :
    a ∈ e :: E ∧ ∀ j < (e :: E).length, (j < (e :: E).idxOf a → t ≤ D ((e :: E).getD j 0)) ∧
      ((e :: E).idxOf a < j → D ((e :: E).getD j 0) < t) := by
  refine ⟨List.mem_cons_of_mem _ hold.1, fun j hj => ?_⟩
  rw [List.idxOf_cons_ne _ hae]
  rcases j with _ | j
  · rw [List.getD_cons_zero]
    exact ⟨fun _ => htop, fun h => absurd h (Nat.not_lt_zero _)⟩
  · rw [List.getD_cons_succ]
    rw [List.length_cons] at hj
    have hm : E.getD j 0 ∈ E := by
      rw [stack_getD_eq (by omega)]
      exact List.getElem_mem _
    rw [hD _ hm]
    have := hold.2 j (by omega)
    exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩

/-- A new frame's arrival link pushed on top splits the stack below it. -/
theorem stack_push_top {E : List ℕ} {e t : ℕ} {D : ℕ → ℕ} (hE : ∀ f ∈ E, D f < t) :
    e ∈ e :: E ∧ ∀ j < (e :: E).length, (j < (e :: E).idxOf e → t ≤ D ((e :: E).getD j 0)) ∧
      ((e :: E).idxOf e < j → D ((e :: E).getD j 0) < t) := by
  refine ⟨List.mem_cons_self, fun j hj => ?_⟩
  rw [List.idxOf_cons_self]
  rcases j with _ | j
  · exact ⟨fun h => absurd h (Nat.lt_irrefl 0), fun h => absurd h (Nat.lt_irrefl 0)⟩
  · rw [List.getD_cons_succ]
    rw [List.length_cons] at hj
    refine ⟨fun h => absurd h (Nat.not_lt_zero _), fun _ => hE _ ?_⟩
    rw [stack_getD_eq (by omega)]
    exact List.getElem_mem _

theorem stack_idxOf_lt_of_mem_take {a : ℕ} :
    ∀ (m : ℕ) (l : List ℕ), a ∈ l.take m → l.idxOf a < m
  | 0, l, h => by simp at h
  | m + 1, [], h => by simp at h
  | m + 1, x :: l, h => by
    rw [List.take_succ_cons, List.mem_cons] at h
    by_cases hxa : x = a
    · rw [hxa, List.idxOf_cons_self]
      omega
    · rw [List.idxOf_cons_ne _ hxa]
      have := stack_idxOf_lt_of_mem_take m l (h.resolve_left (Ne.symm hxa))
      omega

theorem stack_idxOf_drop {a : ℕ} : ∀ (m : ℕ) (l : List ℕ), m ≤ l.length → a ∉ l.take m →
    (l.drop m).idxOf a + m = l.idxOf a
  | 0, l, _, _ => by simp
  | m + 1, [], h, _ => by simp at h
  | m + 1, x :: l, h, ha => by
    rw [List.take_succ_cons, List.mem_cons, not_or] at ha
    rw [List.drop_succ_cons, List.idxOf_cons_ne _ (fun h => ha.1 h.symm)]
    have := stack_idxOf_drop m l (by simp at h; omega) ha.2
    omega

/-- A frame's split of the stack survives popping links above its arrival link. -/
theorem stack_pop_cond {E : List ℕ} {a t m : ℕ} {D : ℕ → ℕ}
    (hold : a ∈ E ∧ ∀ j < E.length, (j < E.idxOf a → t ≤ D (E.getD j 0)) ∧
      (E.idxOf a < j → D (E.getD j 0) < t))
    (hm : m ≤ E.idxOf a) :
    a ∈ E.drop m ∧ ∀ j < (E.drop m).length,
      (j < (E.drop m).idxOf a → t ≤ D ((E.drop m).getD j 0)) ∧
      ((E.drop m).idxOf a < j → D ((E.drop m).getD j 0) < t) := by
  have hlt : E.idxOf a < E.length := List.idxOf_lt_length_of_mem hold.1
  have hnt : a ∉ E.take m := fun h => by
    have := stack_idxOf_lt_of_mem_take m E h
    omega
  have hidx := stack_idxOf_drop m E (by omega) hnt
  have hmem : a ∈ E.drop m := by
    have := hold.1
    rw [← List.take_append_drop m E, List.mem_append] at this
    exact this.resolve_left hnt
  refine ⟨hmem, fun j hj => ?_⟩
  rw [List.length_drop] at hj
  have hg : (E.drop m).getD j 0 = E.getD (m + j) 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [hg]
  have := hold.2 (m + j) (by omega)
  exact ⟨fun h => this.1 (by omega), fun h => this.2 (by omega)⟩

section StackOrder

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
variable {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame} {x e : ℕ}

theorem stack_tick_frames (hp : w.path = ⟨v, arr, i⟩ :: rest) {fr : Frame} {k : ℕ}
    (hfr : fr ∈ (⟨v, arr, k⟩ :: rest : List Frame)) :
    ∃ fr' ∈ w.path, fr'.vertex = fr.vertex ∧ fr'.arrival = fr.arrival := by
  rcases List.mem_cons.mp hfr with rfl | hfr
  · exact ⟨⟨v, arr, i⟩, by rw [hp]; exact List.mem_cons_self, rfl, rfl⟩
  · exact ⟨fr, by rw [hp]; exact List.mem_cons_of_mem _ hfr, rfl, rfl⟩

include hS in
/-- Both ends of a link on the stack are entered. -/
theorem stack_ends_entered {f p q : ℕ} (hf : f ∈ w.edges) (hj : Joins g f p q) :
    w.entry p ≠ 0 ∧ w.entry q ≠ 0 := by
  obtain ⟨⟨-, y, hy, s, hs, hse⟩, -⟩ :=
    (hS.2.2.2.2.2.2.2.2.2.2.1 f (hS.2.2.2.2.2.2.2.2.2.2.2.1.1 f hf)).mp hf
  have hjs : Joins g f y s.1 := hse ▸ joins_of_adj_mem (List.mem_of_mem_take hs)
  have hye : w.entry y ≠ 0 := fun h0 => by
    have := ((hS.2.2.1 y hy).2.2.2 h0).1
    simp [looked, this] at hs
  have hse' := (hS.2.2.2.2.2.1 y hy s hs).1
  rcases Joins.ends hjs hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact ⟨hye, hse'⟩
  · rw [h1, h2]
    exact ⟨hse', hye⟩

include hS hO in
/-- A vertex's arrival link has the vertex as its deeper end. -/
theorem stack_deepEntry_arrival {y a : ℕ} (h : w.arrival y = some a) :
    deepEntry (g := g) w a = w.entry y := by
  obtain ⟨-, -, -, -, hlt, hj⟩ := hangs hS hO y (by simp [h])
  rw [stack_deepEntry_joins (hj a (by simp [h]))]
  exact max_eq_right hlt.le

include hS hO in
theorem stack_linkBack (W : Walk) (hT : OpenTaken (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e)) (hxv : x ≠ v)
    (hae : arr ≠ some e) (hlt : w.entry x < w.entry v) (hWe : W.edges = e :: w.edges)
    (hWn : W.entry = w.entry) (hWp : W.path = ⟨v, arr, i + 1⟩ :: rest) :
    StackOk (g := g) W := by
  have hK := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hj : Joins g e v x := (mem_adj.mp (List.mem_of_getElem? hx)).2
  have hne : e ∉ w.edges := fun hm => stack_not_taken_push hS hO hT hp hx hxv hae hlt
    ((hS.2.2.2.2.2.2.2.2.2.2.1 e (joins_lt hj)).mp hm).1
  refine ⟨fun f hf => ?_, fun fr hfr a ha => ?_⟩
  · rw [hWe, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact joins_lt hj
    · exact hK.1 f hf
  · obtain ⟨fr0, h0, hpl, har⟩ := stack_tick_frames hp (by rw [hWp] at hfr; exact hfr)
    have hold := hK.2 fr0 h0 a (har ▸ ha)
    rw [hpl] at hold
    rw [hWe, stack_deepEntry_congr hWn, hWn]
    refine stack_push_cond hold (fun h => hne (h ▸ hold.1)) (fun _ _ => rfl) ?_
    rw [stack_deepEntry_joins hj]
    have := (entry_le_of_above hS hO (above_top hS hp ((onPath_iff _).mpr ⟨fr0, h0, hpl⟩))
      (top_facts hS hp).2.1).2.1
    exact this.trans (le_max_left _ _)

include hS hO in
theorem stack_descend (W : Walk) (hT : OpenTaken (g := g) w)
    (hp : w.path = ⟨v, arr, i⟩ :: rest) (hx : (g.adj v)[i]? = some (x, e)) (hxv : x ≠ v)
    (hae : arr ≠ some e) (h0 : w.entry x = 0) (hWe : W.edges = e :: w.edges)
    (hWn : W.entry = Function.update w.entry x (w.time + 1))
    (hWp : W.path = ⟨x, some e, 0⟩ :: ⟨v, arr, i + 1⟩ :: rest) : StackOk (g := g) W := by
  have hK := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hj : Joins g e v x := (mem_adj.mp (List.mem_of_getElem? hx)).2
  have hve := (top_facts hS hp).2.1
  have hlt : w.entry x < w.entry v := by omega
  have hne : e ∉ w.edges := fun hm => stack_not_taken_push hS hO hT hp hx hxv hae hlt
    ((hS.2.2.2.2.2.2.2.2.2.2.1 e (joins_lt hj)).mp hm).1
  have hD : ∀ f ∈ w.edges, deepEntry (g := g) W f = deepEntry (g := g) w f := by
    intro f hf
    have hfl := hK.1 f hf
    rcases hl : g.links[f]? with _ | ⟨p, q⟩
    · rw [List.getElem?_eq_none_iff] at hl
      omega
    obtain ⟨hpe, hqe⟩ := stack_ends_entered hS hf (Or.inl hl)
    have hpx : p ≠ x := fun h => hpe (h ▸ h0)
    have hqx : q ≠ x := fun h => hqe (h ▸ h0)
    rw [stack_deepEntry_eq hl, stack_deepEntry_eq hl, hWn, Function.update_of_ne hpx,
      Function.update_of_ne hqx]
  have hle : ∀ f, deepEntry (g := g) w f ≤ w.time := by
    intro f
    unfold deepEntry
    split
    · exact max_le (entry_le_time hS hO _) (entry_le_time hS hO _)
    · omega
  refine ⟨fun f hf => ?_, fun fr hfr a ha => ?_⟩
  · rw [hWe, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact joins_lt hj
    · exact hK.1 f hf
  rw [hWp] at hfr
  rw [hWe]
  rcases List.mem_cons.mp hfr with rfl | hfr
  · rw [show a = e from (Option.some.inj ha).symm]
    refine stack_push_top (fun f hf => ?_)
    change _ < W.entry x
    rw [hD f hf, hWn, Function.update_self]
    exact Nat.lt_succ_of_le (hle f)
  · obtain ⟨fr0, h0f, hpl, har⟩ := stack_tick_frames hp hfr
    have hold := hK.2 fr0 h0f a (har ▸ ha)
    rw [hpl] at hold
    have hfe : w.entry fr.vertex ≠ 0 := hpl ▸ (hS.2.1.2.2.2 fr0 h0f).2.1
    have hfx : fr.vertex ≠ x := fun h => hfe (h ▸ h0)
    rw [hWn, Function.update_of_ne hfx]
    refine stack_push_cond hold (fun h => hne (h ▸ hold.1)) hD ?_
    rw [stack_deepEntry_joins hj, hWn, Function.update_self]
    have := entry_le_time hS hO fr.vertex
    exact this.trans ((Nat.le_succ _).trans (le_max_right _ _))

include hS hO in
theorem stack_pop (W : Walk) {e : ℕ} (hp : w.path = ⟨v, some e, i⟩ :: rest)
    (hWe : W.edges = (popBlock e w.edges).2) (hWn : W.entry = w.entry) (hWp : W.path = rest) :
    StackOk (g := g) W := by
  have hK := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [stack_popBlock_eq] at hWe
  refine ⟨fun f hf => hK.1 f (by rw [hWe] at hf; exact List.mem_of_mem_drop hf),
    fun fr hfr a ha => ?_⟩
  rw [hWp] at hfr
  rw [hWe, stack_deepEntry_congr hWn, hWn]
  have hfr' : fr ∈ w.path := by
    rw [hp]
    exact List.mem_cons_of_mem _ hfr
  have hold := hK.2 fr hfr' a ha
  have hv := hK.2 ⟨v, some e, i⟩ (by rw [hp]; exact List.mem_cons_self) e rfl
  obtain ⟨-, hfe, hfa, -, -⟩ := hS.2.1.2.2.2 fr hfr'
  have hfv : fr.vertex ≠ v := not_mem_rest hS hp hfr
  have hlt : w.entry fr.vertex < w.entry v :=
    (entry_le_of_above hS hO (above_top hS hp ((onPath_iff _).mpr ⟨fr, hfr', rfl⟩))
      (top_facts hS hp).2.1).2.2 hfv
  have hda : deepEntry (g := g) w a = w.entry fr.vertex :=
    stack_deepEntry_arrival hS hO (hfa.trans (Option.mem_def.mp ha))
  have hde : deepEntry (g := g) w e = w.entry v :=
    stack_deepEntry_arrival hS hO (top_facts hS hp).2.2.1
  have hae : a ≠ e := fun h => by
    rw [h, hde] at hda
    exact hfv (entry_inj hS hO hfe (by omega))
  refine stack_pop_cond hold ?_
  by_contra hle
  have hidx : w.edges.idxOf a < w.edges.idxOf e :=
    lt_of_le_of_ne (by omega) (fun h => hae ((List.idxOf_inj hold.1).mp h))
  have := (hv.2 (w.edges.idxOf a) (List.idxOf_lt_length_of_mem hold.1)).1 hidx
  rw [stack_getD_eq (List.idxOf_lt_length_of_mem hold.1), List.getElem_idxOf] at this
  change w.entry v ≤ deepEntry (g := g) w a at this
  omega

end StackOrder

/-- **A step keeps the stack's order**: every open vertex's arrival link on the stack, with the
links entered no earlier than its vertex above it and the others below. -/
theorem stackOk_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (hT : OpenTaken (g := g) w) : StackOk (g := g) (step g w) := by
  have hK := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rcases stack_step_moves (g := g) w with ⟨hp, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨-, h⟩ | ⟨⟨hxv, hae, -, hlt⟩, h⟩ | ⟨⟨hxv, hae, h0⟩, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, hp, -, -, h⟩
  all_goals rw [h]
  · refine ⟨hK.1, fun fr hfr a ha => ?_⟩
    simp only [newRoot, enter, hp, List.mem_singleton] at hfr
    rw [hfr] at ha
    simp at ha
  · exact stack_frames hK rfl rfl (fun fr hfr => ⟨fr, hfr, rfl, rfl⟩)
  · exact hK
  · exact stack_frames hK rfl rfl (fun fr hfr => stack_tick_frames hp hfr)
  · exact stack_linkBack hS hO _ hT hp hx hxv hae hlt rfl rfl rfl
  · exact stack_descend hS hO _ hT hp hx hxv hae h0 rfl rfl rfl
  · have huv : u ≠ v := not_mem_rest hS hp (fr := ⟨u, a, j⟩) List.mem_cons_self
    set W := finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty with hW
    have hWp : W.path = ⟨u, a, j⟩ :: above := by
      have := congrArg Walk.path
        (core_finishUnder (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty)
      exact this
    have hWn : W.entry = w.entry := by
      have := congrArg Walk.entry
        (core_finishUnder (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty)
      exact this
    by_cases hc : (pop w v (⟨u, a, j⟩ :: above)).entry u ≤ (pop w v (⟨u, a, j⟩ :: above)).low v
    · exact stack_pop hS hO W hp ((stack_finishUnder_edges _ _ _ huv).trans (ite_eq_left hc))
        hWn hWp
    · refine stack_frames hK ((stack_finishUnder_edges _ _ _ huv).trans (ite_eq_right hc)) hWn
        (fun fr hfr => ⟨fr, ?_, rfl, rfl⟩)
      rw [hWp] at hfr
      rw [hp]
      exact List.mem_cons_of_mem _ hfr
  · have hWp : (finishRoot (pop w v rest) v).path = rest := by
      have := congrArg Walk.path (core_finishRoot (pop w v rest) v)
      exact this
    have hWn : (finishRoot (pop w v rest) v).entry = w.entry := by
      have := congrArg Walk.entry (core_finishRoot (pop w v rest) v)
      exact this
    refine stack_frames hK (stack_finishRoot_fields _ _).2.1 hWn (fun fr hfr => ⟨fr, ?_, rfl, rfl⟩)
    rw [hWp] at hfr
    rw [hp]
    exact List.mem_cons_of_mem _ hfr

end Walk

end AlgoDesign.Graphs.Blocks
