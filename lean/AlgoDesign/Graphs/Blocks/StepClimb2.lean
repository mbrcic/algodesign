/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.StepClimb

/-!
# Bridges, cut vertices and blocks: one step keeps the climb-back numbers

A step keeps every entered vertex's climb-back number equal to the earliest entry number its
explored subtree reaches (`climb_step`). Entering a vertex adds a vertex whose subtree is itself and
which has taken nothing; taking a row entry adds one reading to the current vertex's subtree only,
since the current vertex is open; finishing a vertex adds the vertices below it to the subtree of
the vertex it hangs from, whose climb-back number takes the finished vertex's.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Walk

variable {g : Graph}

/-! ## Reading the explored subtree -/

theorem climb_explored_congr {W w : Walk} (ha : W.arrival = w.arrival) (hu : W.up = w.up)
    (hf : W.finished = w.finished) : Explored (g := g) W = Explored (g := g) w := by
  funext y z
  unfold Explored
  rw [chain_congr ha hu, hf, ha, hu]

/-- A walk's climb-back reading is read off the fields it looks at. -/
theorem climb_congr {W w : Walk} (he : W.entry = w.entry) (ha : W.arrival = w.arrival)
    (hu : W.up = w.up) (hf : W.finished = w.finished) (ht : W.taken = w.taken) :
    climb (g := g) W = climb (g := g) w := by
  funext y
  refine eq_of_forall_le_iff fun m => ?_
  rw [le_climb_iff, le_climb_iff, climb_explored_congr ha hu hf, he, ha]
  simp only [looked, ht]

theorem climb_explored_iff {W : Walk} (hanc : ∀ a b, Anc (g := g) W a b ↔ Above W a b)
    (y z : ℕ) : Explored (g := g) W y z ↔
      z = y ∨ ∃ c, Above W c z ∧ W.finished c = true ∧ W.arrival c ≠ none ∧ W.up c = y := by
  unfold Explored
  constructor
  · rintro (h | ⟨c, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, (hanc c z).mp hc, h⟩
  · rintro (h | ⟨c, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, (hanc c z).mpr hc, h⟩

/-- Away from a new vertex, the tree after entering it is the old one. -/
theorem climb_above_of_upd {W w : Walk} {x' u : ℕ} {arr : Option ℕ}
    (hWa : W.arrival = Function.update w.arrival x' arr) (hWu : W.up = Function.update w.up x' u)
    (hup : ∀ z, w.arrival z ≠ none → w.up z ≠ x') {c z : ℕ} (h : Above W c z) (hz : z ≠ x') :
    Above w c z ∧ c ≠ x' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨Above.refl w _, hz⟩
  | @head b d hbd _ ih =>
    obtain ⟨h1, hdx⟩ := ih
    obtain ⟨hda, hdb⟩ := hbd
    rw [hWa, Function.update_of_ne hdx] at hda
    rw [hWu, Function.update_of_ne hdx] at hdb
    subst hdb
    exact ⟨(Above.up hda).trans h1, hup d hda⟩

theorem climb_above_upd {W w : Walk} {x' u : ℕ} {arr : Option ℕ}
    (hWa : W.arrival = Function.update w.arrival x' arr) (hWu : W.up = Function.update w.up x' u)
    (hx : w.arrival x' = none) {c z : ℕ} (h : Above w c z) : Above W c z := by
  induction h with
  | refl => exact Above.refl W _
  | @tail b d _ hbd ih =>
    obtain ⟨hd, rfl⟩ := hbd
    have hdx : d ≠ x' := fun h => hd (h ▸ hx)
    have h1 : W.arrival d ≠ none := by
      rw [hWa, Function.update_of_ne hdx]
      exact hd
    have h2 : W.up d = w.up d := by rw [hWu, Function.update_of_ne hdx]
    exact ih.trans (h2 ▸ Above.up h1)

section Climb

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)

include hS hO in
/-- Only an open vertex's own subtree holds it. -/
theorem climb_explored_open {y v : ℕ} (hv : w.onPath v = true)
    (h : Explored (g := g) w y v) : y = v := by
  rcases h with h | ⟨c, hc, hf, -, -⟩
  · exact h.symm
  · exfalso
    have hcv := (anc_iff hS hO c v).mp hc
    have hcon := onPath_of_above hS hcv hv
    exact (hS.2.2.1 c (entry_of_onPath hS hcon).1).2.1 ⟨hcon, hf⟩

include hS hO in
/-- The current vertex's explored subtree is everything below it. -/
theorem climb_explored_top {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame}
    (hp : w.path = ⟨v, arr, i⟩ :: rest) {z : ℕ} (h : Above w v z) :
    Explored (g := g) w v z := by
  by_cases hzv : z = v
  · exact Or.inl hzv
  · obtain ⟨c, hcz, hca, hcu⟩ := exists_child_of_above h (Ne.symm hzv)
    obtain ⟨hcn, hce, -, -, hlt, -⟩ := hangs hS hO c hca
    have hcf : w.finished c = true := by
      rcases (hS.2.2.1 c hcn).1.mp hce with hcon | hcf
      · exfalso
        have := (entry_le_of_above hS hO (above_top hS hp hcon) (top_facts hS hp).2.1).2.1
        rw [hcu] at hlt
        omega
      · exact hcf
    exact Or.inr ⟨c, (anc_iff hS hO c z).mpr hcz, hcf, hca, hcu⟩

include hS hO in
/-- **Entering a vertex**: its climb-back reading is its own entry number, and every other entered
vertex's reading is unchanged, as long as the new readings lead only to the new vertex. -/
theorem climb_enter {W : Walk} {x' u : ℕ} {arr : Option ℕ} (hx0 : w.entry x' = 0)
    (hWe : W.entry = Function.update w.entry x' (w.time + 1))
    (hWa : W.arrival = Function.update w.arrival x' arr)
    (hWu : W.up = Function.update w.up x' u) (hWf : W.finished = w.finished)
    (hWt : W.taken x' = 0) (hu : arr = none ∨ u ≠ x')
    (hanc : ∀ a b, Anc (g := g) W a b ↔ Above W a b)
    (hold : ∀ z, ∀ s ∈ looked (g := g) w z, s ∈ looked (g := g) W z)
    (hnew : ∀ z, ∀ s ∈ looked (g := g) W z, s ∈ looked (g := g) w z ∨ s.1 = x') :
    climb (g := g) W x' = w.time + 1 ∧
      ∀ y, y ≠ x' → w.entry y ≠ 0 → climb (g := g) W y = climb (g := g) w y := by
  have hup := climb_up_ne_of_zero hS hO hx0
  have hxs : w.taken x' = 0 ∧ w.arrival x' = none ∧ w.finished x' = false := by
    by_cases hxn : x' < g.n
    · obtain ⟨h1, -, -, h4⟩ := hS.2.2.1 x' hxn
      refine ⟨(h4 hx0).1, (h4 hx0).2, ?_⟩
      by_contra hf
      exact (h1.mpr (Or.inr (by simpa using hf))) hx0
    · obtain ⟨-, -, h3, h4, h5⟩ := hO x' (by omega)
      exact ⟨h4, h5, h3⟩
  have hlw : looked (g := g) w x' = [] := by simp [looked, hxs.1]
  have hlW : looked (g := g) W x' = [] := by simp [looked, hWt]
  have hEx : ∀ y z, y ≠ x' → z ≠ x' →
      (Explored (g := g) W y z ↔ Explored (g := g) w y z) := by
    intro y z hy hz
    rw [climb_explored_iff hanc, climb_explored_iff (anc_iff hS hO), hWf]
    constructor
    · rintro (h | ⟨c, hc, hf, ha, hcu⟩)
      · exact Or.inl h
      · obtain ⟨hc', hcx⟩ := climb_above_of_upd hWa hWu hup hc hz
        rw [hWa, Function.update_of_ne hcx] at ha
        rw [hWu, Function.update_of_ne hcx] at hcu
        exact Or.inr ⟨c, hc', hf, ha, hcu⟩
    · rintro (h | ⟨c, hc, hf, ha, hcu⟩)
      · exact Or.inl h
      · have hcx : c ≠ x' := fun h => by
          rw [h, hxs.2.2] at hf
          exact Bool.false_ne_true hf
        refine Or.inr ⟨c, climb_above_upd hWa hWu hxs.2.1 hc, hf, ?_, ?_⟩
        · rw [hWa, Function.update_of_ne hcx]
          exact ha
        · rw [hWu, Function.update_of_ne hcx]
          exact hcu
  have hEx' : ∀ z, Explored (g := g) W x' z → z = x' := by
    intro z h
    rw [climb_explored_iff hanc] at h
    rcases h with h | ⟨c, -, -, ha, hcu⟩
    · exact h
    · exfalso
      by_cases hcx : c = x'
      · rw [hcx, hWa, Function.update_self] at ha
        rw [hcx, hWu, Function.update_self] at hcu
        rcases hu with hu | hu
        · exact ha hu
        · exact hu hcu
      · rw [hWa, Function.update_of_ne hcx] at ha
        rw [hWu, Function.update_of_ne hcx] at hcu
        exact hup c ha hcu
  refine ⟨eq_of_forall_le_iff fun m => ?_, fun y hy hye => eq_of_forall_le_iff fun m => ?_⟩
  · rw [le_climb_iff, hWe, Function.update_self]
    refine ⟨fun h => h.1, fun h => ⟨h, fun z _ hz s hs => ?_⟩⟩
    rw [hEx' z hz, hlW] at hs
    simp at hs
  · rw [le_climb_iff, le_climb_iff, hWe, Function.update_of_ne hy]
    have hyt : w.entry y ≤ w.time := entry_le_time hS hO y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun z hz hex s hs hsa => ?_⟩
      have hzx : z ≠ x' := fun h => by
        rw [h, hlw] at hs
        simp at hs
      have hs1 : s.1 ≠ x' := fun h => (hS.2.2.2.2.2.1 z hz s hs).1 (h ▸ hx0)
      have := h2 z hz ((hEx y z hy hzx).mpr hex) s (hold z s hs)
        (by rw [hWa, Function.update_of_ne hzx]; exact hsa)
      rwa [Function.update_of_ne hs1] at this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun z hz hex s hs hsa => ?_⟩
      have hzx : z ≠ x' := fun h => by
        rw [h, hlW] at hs
        simp at hs
      rw [hWa, Function.update_of_ne hzx] at hsa
      rcases hnew z s hs with hs' | hs1
      · have hs1 : s.1 ≠ x' := fun h => (hS.2.2.2.2.2.1 z hz s hs').1 (h ▸ hx0)
        rw [Function.update_of_ne hs1]
        exact h2 z hz ((hEx y z hy hzx).mp hex) s hs' hsa
      · rw [hs1, Function.update_self]
        omega

include hS hO in
/-- **Taking a row entry** of the current vertex `v` adds one reading, to `v`'s subtree only. -/
theorem climb_tick {W : Walk} {v x e : ℕ} (hv : w.onPath v = true)
    (hWe : W.entry = w.entry) (hWa : W.arrival = w.arrival) (hWu : W.up = w.up)
    (hWf : W.finished = w.finished)
    (hold : ∀ z, ∀ s ∈ looked (g := g) w z, s ∈ looked (g := g) W z)
    (hnew : ∀ z, ∀ s ∈ looked (g := g) W z, s ∈ looked (g := g) w z ∨ (z = v ∧ s = (x, e)))
    (hin : (x, e) ∈ looked (g := g) W v) (y m : ℕ) :
    m ≤ climb (g := g) W y ↔
      m ≤ climb (g := g) w y ∧ (y = v → w.arrival v ≠ some e → m ≤ w.entry x) := by
  rw [le_climb_iff, le_climb_iff, climb_explored_congr hWa hWu hWf, hWe, hWa]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun z hz hex s hs hsa => h2 z hz hex s (hold z s hs) hsa⟩, fun hyv hva => ?_⟩
    exact h2 v (entry_of_onPath hS hv).1 (Or.inl hyv.symm) (x, e) hin hva
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun z hz hex s hs hsa => ?_⟩
    rcases hnew z s hs with hs' | ⟨hzv, hse⟩
    · exact h2 z hz hex s hs' hsa
    · rw [hzv] at hex hsa
      rw [hse] at hsa ⊢
      exact h3 (climb_explored_open hS hO hv hex) hsa

include hS hO in
/-- **Finishing `v` under `u`**: `u`'s subtree gains the vertices below `v`; nothing else
changes. -/
theorem climb_finishUnder {W : Walk} {v e i u j : ℕ} {a : Option ℕ} {above : List Frame}
    (hp : w.path = ⟨v, some e, i⟩ :: ⟨u, a, j⟩ :: above)
    (hWe : W.entry = w.entry) (hWa : W.arrival = w.arrival) (hWu : W.up = w.up)
    (hWf : W.finished = Function.update w.finished v true) (hWt : W.taken = w.taken) :
    (∀ y, y ≠ u → climb (g := g) W y = climb (g := g) w y) ∧
      ∀ m, m ≤ climb (g := g) W u ↔ m ≤ climb (g := g) w u ∧ m ≤ climb (g := g) w v := by
  obtain ⟨-, -, hva, -, -, -⟩ := top_facts hS hp
  have hch := hS.2.1.2.1
  rw [hp, List.isChain_cons_cons] at hch
  have hvu : w.up v = u := hch.1.2.1
  have hue : w.entry u < w.entry v := hch.1.2.2
  have hlook : ∀ z, looked (g := g) W z = looked (g := g) w z := fun z => by
    simp only [looked, hWt]
  have hEx : ∀ y z, Explored (g := g) W y z ↔
      Explored (g := g) w y z ∨ (y = u ∧ Above w v z) := by
    intro y z
    unfold Explored
    rw [chain_congr hWa hWu, hWf, hWa, hWu]
    constructor
    · rintro (h | ⟨c, hc, hf, hca, hcu⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hcv : c = v
        · rw [hcv] at hc hcu
          exact Or.inr ⟨hcu.symm.trans hvu, (anc_iff hS hO v z).mp hc⟩
        · rw [Function.update_of_ne hcv] at hf
          exact Or.inl (Or.inr ⟨c, hc, hf, hca, hcu⟩)
    · rintro ((h | ⟨c, hc, hf, hca, hcu⟩) | ⟨hyu, hvz⟩)
      · exact Or.inl h
      · refine Or.inr ⟨c, hc, ?_, hca, hcu⟩
        by_cases hcv : c = v
        · rw [hcv, Function.update_self]
        · rw [Function.update_of_ne hcv]
          exact hf
      · exact Or.inr ⟨v, (anc_iff hS hO v z).mpr hvz, by simp, by rw [hva]; simp,
          hvu.trans hyu.symm⟩
  refine ⟨fun y hyu => eq_of_forall_le_iff fun m => ?_, fun m => ?_⟩
  · have hE' : ∀ z, Explored (g := g) W y z ↔ Explored (g := g) w y z := fun z =>
      (hEx y z).trans (or_iff_left fun h => hyu h.1)
    rw [le_climb_iff, le_climb_iff, hWe, hWa]
    simp only [hE', hlook]
  · rw [le_climb_iff, le_climb_iff, le_climb_iff, hWe, hWa]
    simp only [hlook]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun z hz hex => h2 z hz ((hEx u z).mpr (Or.inl hex))⟩,
        ⟨by omega, fun z hz hex => h2 z hz ((hEx u z).mpr
          (Or.inr ⟨rfl, above_of_explored hS hO hex⟩))⟩⟩
    · rintro ⟨⟨h1, h2⟩, -, h3⟩
      refine ⟨h1, fun z hz hex => ?_⟩
      rcases (hEx u z).mp hex with hex | ⟨-, hvz⟩
      · exact h2 z hz hex
      · exact h3 z hz (climb_explored_top hS hO hp hvz)

end Climb

/-- **Finishing a root** changes no explored subtree. -/
theorem climb_finishRoot {W w : Walk} {v : ℕ} (hva : w.arrival v = none)
    (hWe : W.entry = w.entry) (hWa : W.arrival = w.arrival) (hWu : W.up = w.up)
    (hWf : W.finished = Function.update w.finished v true) (hWt : W.taken = w.taken) (y : ℕ) :
    climb (g := g) W y = climb (g := g) w y := by
  have hE : ∀ z, Explored (g := g) W y z ↔ Explored (g := g) w y z := by
    intro z
    unfold Explored
    rw [chain_congr hWa hWu, hWf, hWa, hWu]
    refine or_congr_right (exists_congr fun c => and_congr_right fun _ => ?_)
    by_cases hcv : c = v
    · rw [hcv, hva]
      simp
    · rw [Function.update_of_ne hcv]
  refine eq_of_forall_le_iff fun m => ?_
  rw [le_climb_iff, le_climb_iff, hWe, hWa]
  simp only [hE, looked, hWt]

/-! ## One step -/

section Step

variable {w : Walk} (hS : Shape (g := g) w) (hO : Outside (g := g) w)
variable {v : ℕ} {arr : Option ℕ} {i : ℕ} {rest : List Frame} {x e : ℕ}

include hS in
/-- The rows after taking an entry: the current vertex's row gains the entry, no other changes. -/
theorem climb_looked_tick (hp : w.path = ⟨v, arr, i⟩ :: rest)
    (hx : (g.adj v)[i]? = some (x, e)) :
    (∀ z, ∀ s ∈ looked (g := g) w z, s ∈ looked (g := g) (tick w v arr i rest) z) ∧
      (x, e) ∈ looked (g := g) (tick w v arr i rest) v := by
  have hlv : looked (g := g) (tick w v arr i rest) v = looked (g := g) w v ++ [(x, e)] := by
    simp only [looked, tick, Function.update_self, List.take_add_one, hx, Option.toList_some,
      (top_facts hS hp).2.2.2.1]
  refine ⟨fun z s hs => ?_, by rw [hlv]; simp⟩
  by_cases hzv : z = v
  · rw [hzv] at hs ⊢
    rw [hlv]
    exact List.mem_append_left _ hs
  · simpa [looked, tick, Function.update_of_ne hzv] using hs

end Step

variable {w : Walk}

/-- **A step keeps the climb-back numbers**: each entered vertex's number is the earliest entry
number its explored subtree reaches by one taken row entry, never by the link a vertex arrived
by. -/
theorem climb_step (_hg : g.WellFormed) (hS : Shape (g := g) w) (hO : Outside (g := g) w)
    (_hT : OpenTaken (g := g) w) : ClimbBackIsEarliest (step g w) := by
  obtain ⟨hgw, hC⟩ := hS.2.2.2.2.2.2.2.2.1
  unfold ClimbBackIsEarliest at hC ⊢
  rw [hgw] at hC
  rw [step_g, hgw]
  have hcl : ∀ y, climb (g := g) w y ≤ w.entry y := fun y => ((le_climb_iff w y _).mp le_rfl).1
  rcases stack_step_moves (g := g) w with ⟨-, hn, h0, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ |
    ⟨v, arr, i, rest, x, e, hp, hx, ⟨hc, h⟩ | ⟨⟨hxv, hae, -, -⟩, h⟩ | ⟨⟨hxv, hae, h0⟩, h⟩⟩ |
    ⟨v, e, i, u, a, j, above, hp, -, h⟩ | ⟨v, arr, i, rest, hp, -, hr, h⟩
  all_goals rw [h]
  · have key := climb_enter hS hO (W := newRoot w) (u := w.next) (arr := none) h0 rfl rfl rfl
      rfl ((hS.2.2.1 w.next hn).2.2.2 h0).1 (Or.inl rfl) (anc_iff_newRoot hS hO h0)
      (fun _ _ hs => hs) (fun _ _ hs => Or.inl hs)
    intro y hy hye
    by_cases hyr : y = w.next
    · rw [hyr, key.1]
      simp [newRoot, enter]
    · have hye' : w.entry y ≠ 0 := by simpa [newRoot, enter, Function.update_of_ne hyr] using hye
      rw [key.2 y hyr hye']
      simp only [newRoot, enter, Function.update_of_ne hyr]
      exact hC y hy hye'
  · intro y hy hye
    rw [climb_congr (W := { w with next := w.next + 1 }) (w := w) rfl rfl rfl rfl rfl]
    exact hC y hy hye
  · exact hC
  · obtain ⟨hold, hin⟩ := climb_looked_tick hS hp hx
    obtain ⟨-, hve, hva, -, -, hvon⟩ := top_facts hS hp
    intro y hy hye
    refine (hC y hy hye).trans (eq_of_forall_le_iff fun m => ?_).symm
    rw [climb_tick (W := tick w v arr i rest) hS hO hvon rfl rfl rfl rfl hold
      (fun z s hs => mem_looked_tick hS hp hx hs) hin y m]
    refine ⟨fun h => h.1, fun h => ⟨h, fun hyv hav => ?_⟩⟩
    rw [hyv] at h
    have := hcl v
    rcases hc with hc | hc | ⟨-, hc⟩
    · rw [hc]
      omega
    · exact absurd (hva.trans hc) hav
    · omega
  · obtain ⟨hold, hin⟩ := climb_looked_tick hS hp hx
    obtain ⟨-, -, hva, -, -, hvon⟩ := top_facts hS hp
    intro y hy hye
    have hct := climb_tick (W := { tick w v arr i rest with
        edges := e :: w.edges, low := Function.update w.low v (min (w.low v) (w.entry x)) })
      hS hO hvon rfl rfl rfl rfl
      hold (fun z s hs => mem_looked_tick hS hp hx hs) hin y
    refine eq_of_forall_le_iff fun m => ?_
    rw [hct m]
    change m ≤ Function.update w.low v (min (w.low v) (w.entry x)) y ↔ _
    by_cases hyv : y = v
    · rw [hyv, Function.update_self, hC v (top_facts hS hp).1 (top_facts hS hp).2.1, le_min_iff]
      exact ⟨fun h => ⟨h.1, fun _ _ => h.2⟩, fun h => ⟨h.1, h.2 rfl (by rw [hva]; exact hae)⟩⟩
    · rw [Function.update_of_ne hyv, hC y hy hye]
      exact ⟨fun h => ⟨h, fun h' => absurd h' hyv⟩, fun h => h.1⟩
  · obtain ⟨hold, -⟩ := climb_looked_tick hS hp hx
    have htx : w.taken x = 0 :=
      ((hS.2.2.1 x (mem_adj.mp (List.mem_of_getElem? hx)).1).2.2.2 h0).1
    have key := climb_enter hS hO
      (W := { descend w v arr i rest x e with edges := e :: w.edges }) (u := v) (arr := some e)
      h0 rfl rfl rfl rfl
      (by
        change Function.update w.taken v (i + 1) x = 0
        rw [Function.update_of_ne hxv]
        exact htx)
      (Or.inr (Ne.symm hxv))
      (fun a b => (Iff.of_eq (congrFun (congrFun
        (anc_congr (w := descend w v arr i rest x e)
          (w' := { descend w v arr i rest x e with edges := e :: w.edges }) rfl rfl) a) b)).trans
        (anc_iff_descend hS hO hp h0 a b))
      hold
      (fun z s hs => (mem_looked_tick hS hp hx hs).imp id fun h => by rw [h.2])
    intro y hy hye
    by_cases hyx : y = x
    · rw [hyx, key.1]
      change Function.update w.low x (w.time + 1) x = _
      rw [Function.update_self]
    · have hye' : w.entry y ≠ 0 := by
        change Function.update w.entry x (w.time + 1) y ≠ 0 at hye
        rwa [Function.update_of_ne hyx] at hye
      rw [key.2 y hyx hye']
      change Function.update w.low x (w.time + 1) y = _
      rw [Function.update_of_ne hyx]
      exact hC y hy hye'
  · set W := finishUnder g (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty with hW
    have hcore := core_finishUnder (g := g) (pop w v (⟨u, a, j⟩ :: above)) u v e above.isEmpty
    have hWe : W.entry = w.entry := by
      have := congrArg Walk.entry hcore
      exact this
    have hWa : W.arrival = w.arrival := by
      have := congrArg Walk.arrival hcore
      exact this
    have hWu : W.up = w.up := by
      have := congrArg Walk.up hcore
      exact this
    have hWf : W.finished = Function.update w.finished v true := by
      have := congrArg Walk.finished hcore
      exact this
    have hWt : W.taken = w.taken := by
      have := congrArg Walk.taken hcore
      exact this
    have key := climb_finishUnder hS hO hp hWe hWa hWu hWf hWt
    have hufr := hS.2.1.2.2.2 ⟨u, a, j⟩ (by rw [hp]; simp)
    obtain ⟨hvn, hve, -⟩ := top_facts hS hp
    intro y hy hye
    rw [hWe] at hye
    rw [hW, stack_finishUnder_low]
    change Function.update w.low u (min (w.low u) (w.low v)) y = _
    by_cases hyu : y = u
    · rw [hyu, Function.update_self, hC u hufr.1 hufr.2.1, hC v hvn hve]
      exact eq_of_forall_le_iff fun m => by rw [le_min_iff, key.2 m]
    · rw [Function.update_of_ne hyu, ← hW, key.1 y hyu]
      exact hC y hy hye
  · have hva : w.arrival v = none := by
      rw [(top_facts hS hp).2.2.1]
      rcases hr with hr | hr
      · have := hS.2.1.2.2.1 ⟨v, arr, i⟩ (by rw [hp, hr]; rfl)
        exact this
      · exact hr
    have hcore := core_finishRoot (pop w v rest) v
    have hWe : (finishRoot (pop w v rest) v).entry = w.entry := by
      have := congrArg Walk.entry hcore
      exact this
    have hWa : (finishRoot (pop w v rest) v).arrival = w.arrival := by
      have := congrArg Walk.arrival hcore
      exact this
    have hWu : (finishRoot (pop w v rest) v).up = w.up := by
      have := congrArg Walk.up hcore
      exact this
    have hWf : (finishRoot (pop w v rest) v).finished = Function.update w.finished v true := by
      have := congrArg Walk.finished hcore
      exact this
    have hWt : (finishRoot (pop w v rest) v).taken = w.taken := by
      have := congrArg Walk.taken hcore
      exact this
    intro y hy hye
    rw [hWe] at hye
    rw [(stack_finishRoot_fields _ _).1, climb_finishRoot hva hWe hWa hWu hWf hWt]
    exact hC y hy hye

end Walk

end AlgoDesign.Graphs.Blocks
