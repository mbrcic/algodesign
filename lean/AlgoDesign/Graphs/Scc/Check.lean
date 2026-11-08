/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Basic

/-!
# Strong components: the checker, sound and complete

`check_eq_none_iff`: on a well-formed graph, the three checks pass exactly when the grouping is
the strong components. Check 2 gives that a group's members reach each other; check 3 that vertices
reaching each other share a group, since otherwise the two paths, read as paths between groups,
would close a cycle in the graph of groups. Back the other way, a path between two members of a
strong component never leaves it (Tarjan–Zwick 2024, Lemma 3.1), so the searches staying inside
the group find every member; and the graph of groups of the strong components has no cycle
(`quotientAcyclic_of_isScc`).

On the way: a vertex reaches another exactly when its group reaches the other's in the graph of
groups (`reaches_iff_quotient`), and dropping repeated arrows from the graph of groups changes no
reachability (`quotient_reaches_iff_raw`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

open Relation

variable {g : Digraph} {c : List ℕ}

theorem mem_inside {next : ℕ → List ℕ} {i v w : ℕ} :
    w ∈ inside c i next v ↔ w ∈ next v ∧ gid c w = i := by
  simp [inside]

/-! ## Group ids -/

theorem lt_numGroups_of_mem {i : ℕ} (h : i ∈ c) : i < numGroups c := by
  induction c with
  | nil => simp at h
  | cons j c ih =>
    simp only [numGroups, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem gid_mem {v : ℕ} (hv : v < c.length) : gid c v ∈ c := by
  simp [gid, List.getElem?_eq_getElem hv]

theorem gid_lt {v : ℕ} (hv : v < c.length) : gid c v < numGroups c :=
  lt_numGroups_of_mem (gid_mem hv)

/-- The first vertex in group `i` is a vertex, and in group `i`. -/
theorem idxOf_spec {i : ℕ} (h : i ∈ c) : c.idxOf i < c.length ∧ gid c (c.idxOf i) = i := by
  have hlt := List.idxOf_lt_length_iff.mpr h
  exact ⟨hlt, by simp [gid, List.getElem?_eq_getElem hlt, List.getElem_idxOf]⟩

theorem checkPartition_iff : checkPartition g c = true ↔ IsPartition g c := by
  simp [checkPartition, IsPartition]

/-! ## The graph of groups -/

theorem mem_quotient_arrows {a : ℕ × ℕ} :
    a ∈ (quotient g c).arrows ↔
      ∃ x y, g.Arrow x y ∧ gid c x ≠ gid c y ∧ a = (gid c x, gid c y) := by
  simp only [quotient, quotientArrows, List.mem_dedup, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.exists, Digraph.Arrow]
  constructor
  · rintro ⟨x, y, ⟨h, hne⟩, rfl⟩
    exact ⟨x, y, h, hne, rfl⟩
  · rintro ⟨x, y, h, hne, rfl⟩
    exact ⟨x, y, ⟨h, hne⟩, rfl⟩

/-- **Dropping repeated arrows changes no reachability** in the graph of groups: it has an arrow
exactly where the arrows between different groups, repeats kept, have one. -/
theorem quotient_arrow_iff_raw {a b : ℕ} :
    (quotient g c).Arrow a b ↔ (a, b) ∈ quotientArrows g c := by
  simp [Digraph.Arrow, quotient]

theorem quotient_reaches_iff_raw {a b : ℕ} :
    (quotient g c).Reaches a b ↔ ReflTransGen (fun x y => (x, y) ∈ quotientArrows g c) a b := by
  unfold Digraph.Reaches
  have : (quotient g c).Arrow = fun x y => (x, y) ∈ quotientArrows g c := by
    funext x y
    exact propext quotient_arrow_iff_raw
  rw [this]

/-- The graph of groups joins groups of the grouping. -/
theorem quotient_wellFormed (hg : g.WellFormed) (hc : c.length = g.n) :
    (quotient g c).WellFormed := by
  intro a ha
  obtain ⟨x, y, h, -, rfl⟩ := mem_quotient_arrows.mp ha
  have := hg _ h
  exact ⟨gid_lt (by simp_all), gid_lt (by simp_all)⟩

/-- **A path between vertices is a path between their groups.** -/
theorem quotient_reaches_of_reaches {u v : ℕ} (h : g.Reaches u v) :
    (quotient g c).Reaches (gid c u) (gid c v) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b d _ hbd ih =>
    by_cases hne : gid c b = gid c d
    · rwa [← hne]
    · exact ih.tail (mem_quotient_arrows.mpr ⟨b, d, hbd, hne, rfl⟩)

/-- The part of `IsSccPartition` that speaks of reaching. -/
def SameIffMutual (g : Digraph) (c : List ℕ) : Prop :=
  ∀ u < g.n, ∀ v < g.n, (gid c u = gid c v ↔ Mutual g u v)

/-- With the strong components, a path between groups is a path between any of their members. -/
theorem reaches_of_quotient_reaches (hg : g.WellFormed) (hs : SameIffMutual g c) {a b : ℕ}
    (h : (quotient g c).Reaches a b) :
    ∀ u < g.n, gid c u = a → ∀ v < g.n, gid c v = b → g.Reaches u v := by
  induction h with
  | refl =>
    intro u hu hua v hv hvb
    exact ((hs u hu v hv).mp (hua.trans hvb.symm)).1
  | @tail b' d _ hbd ih =>
    intro u hu hua v hv hvd
    obtain ⟨x, y, hxy, -, he⟩ := mem_quotient_arrows.mp hbd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hx := (hg _ hxy).1
    have hy := (hg _ hxy).2
    have hux := ih u hu hua x hx rfl
    have hyv := ((hs y hy v hv).mp hvd.symm).1
    exact (hux.tail hxy).trans hyv

/-- **A vertex reaches another exactly when its group reaches the other's group**, for the strong
components of a well-formed graph. -/
theorem reaches_iff_quotient (hg : g.WellFormed) (hs : IsSccPartition g c) {u v : ℕ}
    (hu : u < g.n) (hv : v < g.n) :
    g.Reaches u v ↔ (quotient g c).Reaches (gid c u) (gid c v) :=
  ⟨quotient_reaches_of_reaches, fun h => reaches_of_quotient_reaches hg hs.2 h u hu rfl v hv rfl⟩

/-- **The graph of groups of the strong components has no cycle.** -/
theorem quotientAcyclic_of_isScc (hg : g.WellFormed) (hs : IsSccPartition g c) :
    QuotientAcyclic g c := by
  intro a ha hback
  obtain ⟨x, y, hxy, hne, rfl⟩ := mem_quotient_arrows.mp ha
  have hx := (hg _ hxy).1
  have hy := (hg _ hxy).2
  have hyx := reaches_of_quotient_reaches hg hs.2 hback y hy rfl x hx rfl
  exact hne ((hs.2 x hx y hy).mpr ⟨ReflTransGen.single hxy, hyx⟩)

/-- Ids in topological order leave no cycle in the graph of groups. -/
theorem quotientAcyclic_of_idsTopological (h : IdsTopological g c) : QuotientAcyclic g c := by
  have hle : ∀ {a b}, (quotient g c).Reaches a b → a ≤ b := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hbd ih => exact ih.trans (h _ hbd).le
  intro a ha hback
  exact absurd (hle hback) (not_le.mpr (h a ha))

/-! ## Check 3 -/

theorem checkAcyclic_iff (hg : g.WellFormed) (hc : c.length = g.n) :
    checkAcyclic g c = true ↔ QuotientAcyclic g c := by
  have hq := quotient_wellFormed hg hc
  simp only [checkAcyclic, List.all_eq_true, decide_eq_true_eq, QuotientAcyclic]
  refine forall₂_congr fun a ha => ?_
  rw [mem_reachFrom_forward hq (hq a ha).2]

/-- **Check 3 works**: with the grouping a partition, if the graph of groups has no cycle, vertices
that reach each other share a group. -/
theorem same_of_mutual (hac : QuotientAcyclic g c) {u v : ℕ} (h : Mutual g u v) :
    gid c u = gid c v := by
  by_contra hne
  have huv := quotient_reaches_of_reaches (c := c) h.1
  have hvu := quotient_reaches_of_reaches (c := c) h.2
  rcases ReflTransGen.cases_head huv with heq | ⟨b, hab, hbv⟩
  · exact hne heq
  · exact hac _ hab (hbv.trans hvu)

/-! ## Check 2 -/

/-- A search staying inside a group follows arrows. -/
theorem reaches_of_inside {i a b : ℕ}
    (h : ReflTransGen (fun x y => y ∈ inside c i (forward g) x) a b) : g.Reaches a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hst ih => exact ih.tail (mem_forward.mp (mem_inside.mp hst).1).2

/-- A backward search staying inside a group follows arrows backward. -/
theorem reaches_of_inside_backward {i a b : ℕ}
    (h : ReflTransGen (fun x y => y ∈ inside c i (backward g) x) a b) : g.Reaches b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hst ih => exact ReflTransGen.head (mem_backward.mp (mem_inside.mp hst).1).2 ih

/-- **A path inside a strong component** (Tarjan–Zwick 2024, Lemma 3.1): from `r` to a vertex `b`
that reaches back to `r`, a path stays among the vertices of `r`'s group. -/
theorem inside_of_mutual (hg : g.WellFormed) (hs : SameIffMutual g c) {r : ℕ} (hr : r < g.n)
    {b : ℕ} (hrb : g.Reaches r b) (hbr : g.Reaches b r) :
    ReflTransGen (fun x y => y ∈ inside c (gid c r) (forward g) x) r b := by
  induction hrb with
  | refl => exact ReflTransGen.refl
  | @tail b d hrb' hbd ih =>
    have hd := (hg _ hbd).2
    refine (ih (ReflTransGen.head hbd hbr)).tail (mem_inside.mpr ⟨mem_forward.mpr ⟨hd, hbd⟩, ?_⟩)
    exact ((hs d hd r hr).mpr ⟨hbr, hrb'.tail hbd⟩)

/-- The same, backward: from a vertex `a` that `r` reaches and that reaches `r`, the backward search
from `r` staying inside the group finds `a`. -/
theorem inside_backward_of_mutual (hg : g.WellFormed) (hs : SameIffMutual g c) {r : ℕ}
    (hr : r < g.n) {a : ℕ} (har : g.Reaches a r) (hra : g.Reaches r a) :
    ReflTransGen (fun x y => y ∈ inside c (gid c r) (backward g) x) r a := by
  induction har using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | @head a a' haa' ha'r ih =>
    have ha := (hg _ haa').1
    refine (ih (hra.tail haa')).tail (mem_inside.mpr ⟨mem_backward.mpr ⟨ha, haa'⟩, ?_⟩)
    exact ((hs a ha r hr).mpr ⟨ha'r.head haa', hra⟩)

theorem steps_lt {i : ℕ} {next : ℕ → List ℕ} (h : ∀ a, ∀ b ∈ next a, b < g.n) :
    ∀ a, ∀ b ∈ inside c i next a, b < g.n :=
  fun a b hb => h a b (mem_inside.mp hb).1

theorem forward_lt : ∀ a, ∀ b ∈ forward g a, b < g.n := fun _ _ hb => (mem_forward.mp hb).1

theorem backward_lt : ∀ a, ∀ b ∈ backward g a, b < g.n := fun _ _ hb => (mem_backward.mp hb).1

/-- **Check 2 works**: with the grouping a partition, if check 2 passes, two vertices sharing a
group reach each other, both through the group's first member. -/
theorem mutual_of_checkStrong (hp : IsPartition g c) (h : checkStrong g c = true) {u v : ℕ}
    (hu : u < g.n) (hv : v < g.n) (huv : gid c u = gid c v) : Mutual g u v := by
  simp only [checkStrong, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true] at h
  have hi := gid_lt (c := c) (hp.1 ▸ hu)
  obtain ⟨hrl, -⟩ := idxOf_spec (hp.2 _ hi)
  rw [hp.1] at hrl
  have key : ∀ w < g.n, gid c w = gid c u →
      g.Reaches (c.idxOf (gid c u)) w ∧ g.Reaches w (c.idxOf (gid c u)) := by
    intro w hw hwu
    rcases h _ hi w hw with hne | ⟨hfw, hbw⟩
    · exact absurd hwu hne
    · exact ⟨reaches_of_inside ((mem_reachFrom_iff (steps_lt forward_lt) hrl).mp hfw),
        reaches_of_inside_backward ((mem_reachFrom_iff (steps_lt backward_lt) hrl).mp hbw)⟩
  obtain ⟨hru, hur⟩ := key u hu rfl
  obtain ⟨hrv, hvr⟩ := key v hv huv.symm
  exact ⟨hur.trans hrv, hvr.trans hru⟩

/-- **Check 2 passes on the strong components.** -/
theorem checkStrong_of_isScc (hg : g.WellFormed) (hs : IsSccPartition g c) :
    checkStrong g c = true := by
  simp only [checkStrong, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true]
  intro i hi v hv
  by_cases hvi : gid c v = i
  · right
    obtain ⟨hrl, hri⟩ := idxOf_spec (hs.1.2 _ hi)
    rw [hs.1.1] at hrl
    have hm := (hs.2 _ hrl v hv).mp (hri.trans hvi.symm)
    have hf := inside_of_mutual hg hs.2 hrl hm.1 hm.2
    have hb := inside_backward_of_mutual hg hs.2 hrl hm.2 hm.1
    rw [hri] at hf hb
    exact ⟨(mem_reachFrom_iff (steps_lt forward_lt) hrl).mpr hf,
      (mem_reachFrom_iff (steps_lt backward_lt) hrl).mpr hb⟩
  · exact Or.inl hvi

/-! ## The three checks together -/

theorem check_eq_none_iff_and :
    check g c = none ↔
      checkPartition g c = true ∧ checkStrong g c = true ∧ checkAcyclic g c = true := by
  unfold check
  cases checkPartition g c <;> cases checkStrong g c <;> cases checkAcyclic g c <;> simp

/-- **The checker is sound and complete**: on a well-formed graph, the three checks pass exactly
when the grouping is the strong components. -/
theorem check_eq_none_iff (hg : g.WellFormed) : check g c = none ↔ IsSccPartition g c := by
  rw [check_eq_none_iff_and, checkPartition_iff]
  constructor
  · rintro ⟨hp, hs, ha⟩
    have hac := (checkAcyclic_iff hg hp.1).mp ha
    exact ⟨hp, fun u hu v hv =>
      ⟨mutual_of_checkStrong hp hs hu hv, fun hm => same_of_mutual hac hm⟩⟩
  · intro hs
    exact ⟨hs.1, checkStrong_of_isScc hg hs,
      (checkAcyclic_iff hg hs.1.1).mpr (quotientAcyclic_of_isScc hg hs)⟩

/-- The checker as a yes-or-no answer: all three checks pass. -/
def checkComponents (g : Digraph) (c : List ℕ) : Bool := (check g c).isNone

/-- **The checker is sound and complete**, as a yes-or-no answer. -/
theorem checkComponents_iff (hg : g.WellFormed) :
    checkComponents g c = true ↔ IsSccPartition g c := by
  rw [← check_eq_none_iff hg, checkComponents, Option.isNone_iff_eq_none]

/-- The same, with the graph of groups' lack of a cycle named: the checks pass exactly when the
grouping is the strong components and the graph of groups has no cycle. -/
theorem check_eq_none_iff' (hg : g.WellFormed) :
    check g c = none ↔ IsSccPartition g c ∧ QuotientAcyclic g c :=
  (check_eq_none_iff hg).trans ⟨fun h => ⟨h, quotientAcyclic_of_isScc hg h⟩, fun h => h.1⟩

end AlgoDesign.Graphs.Scc
