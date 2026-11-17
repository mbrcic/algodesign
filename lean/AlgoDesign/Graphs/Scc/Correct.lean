/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkStop
public import AlgoDesign.Graphs.Scc.Check

/-!
# Algorithm T is right

`algorithmTPromise`: on a well-formed graph, Algorithm T's groups are the strong components, their
ids are in topological order, its member lists agree with them, and each lists its members in
postorder (Tarjan–Zwick 2024, Theorem 3.10 for the groups, Theorem 3.5 for their order, p. 10 for
the members in postorder).

At the end of the walk, whether it stopped early or not (`ends_final`), every vertex is in a group
out, each group out is a whole strong component (box invariant 3), and a group out reaches only
groups out no later, so
an arrow between two groups goes from a later group to an earlier one, whose id `k - 1 - e` is
larger. Each group's members are a sublist of the vertices in the order they finished, which is
`finishOrder` (`final_finished`, `finishOrder_of_stop`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

theorem numGroups_le {c : List ℕ} {k : ℕ} (h : ∀ i ∈ c, i < k) : numGroups c ≤ k := by
  induction c with
  | nil => simp [numGroups]
  | cons j c ih =>
    simp only [numGroups, List.foldr_cons] at ih ⊢
    have := h j List.mem_cons_self
    have := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    omega

theorem gid_map {n : ℕ} (f : ℕ → ℕ) {v : ℕ} (hv : v < n) :
    gid ((List.range n).map f) v = f v := by
  simp [gid, hv]

section Final

variable (hg : g.WellFormed)
include hg

theorem final_mem_group {v : ℕ} (hv : v < g.n) :
    ∃ h : (final g).emitted v < (final g).groups.length,
      v ∈ (final g).groups[(final g).emitted v] := by
  have h := ends_final hg
  obtain ⟨m, hm, hvm⟩ := List.mem_flatten.1 ((ends_final hg).out v hv)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
  have := h.grp_idx i hi v hvm
  subst this
  exact ⟨hi, hvm⟩

theorem final_mutual_iff {u v : ℕ} (hu : u < g.n) (hv : v < g.n) :
    Mutual g u v ↔ (final g).emitted u = (final g).emitted v := by
  have h := ends_final hg
  obtain ⟨hu', hum⟩ := final_mem_group hg hu
  obtain ⟨hv', hvm⟩ := final_mem_group hg hv
  have hgrp := h.valid.2.2.2
  have hfg : (final g).g = g := by simp [final, start]
  rw [hfg] at hgrp
  constructor
  · intro huv
    have : u ∈ (final g).groups[(final g).emitted v] :=
      (hgrp _ (List.getElem_mem hv') v hvm u hu).2 huv
    exact h.grp_idx _ hv' u this
  · intro he
    have : u ∈ (final g).groups[(final g).emitted v] := by
      simp only [← he]
      exact hum
    exact (hgrp _ (List.getElem_mem hv') v hvm u hu).1 this

theorem final_member_lt {m : List ℕ} (hm : m ∈ (final g).groups) {v : ℕ} (hv : v ∈ m) :
    v < g.n := by
  exact (ends_final hg).lt_n m hm v hv

theorem final_emitted_lt {v : ℕ} (hv : v < g.n) :
    (final g).emitted v < (final g).groups.length :=
  (final_mem_group hg hv).1

omit hg in
theorem gid_algorithmT {v : ℕ} (hv : v < g.n) :
    gid (algorithmT g).groupOf v = (final g).groups.length - 1 - (final g).emitted v := by
  unfold algorithmT read
  exact gid_map _ hv

theorem mem_algorithmT_groupOf {i : ℕ} :
    i ∈ (algorithmT g).groupOf ↔ i < (final g).groups.length := by
  have h := ends_final hg
  unfold algorithmT read
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have := final_emitted_lt hg hv
    omega
  · intro hi
    set k := (final g).groups.length
    have he : k - 1 - i < k := by omega
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (h.grp_ne _ (List.getElem_mem he))
    have hvn := final_member_lt hg (List.getElem_mem he) hv
    refine ⟨v, hvn, ?_⟩
    rw [h.grp_idx _ he v hv]
    omega

theorem numGroups_algorithmT : numGroups (algorithmT g).groupOf = (final g).groups.length := by
  refine le_antisymm (numGroups_le fun i hi => (mem_algorithmT_groupOf hg).1 hi) ?_
  rcases Nat.eq_zero_or_pos (final g).groups.length with h0 | hpos
  · omega
  · have := lt_numGroups_of_mem ((mem_algorithmT_groupOf hg).2 (Nat.sub_lt hpos one_pos))
    omega

/-- **Algorithm T's groups are the strong components.** -/
theorem isSccPartition_algorithmT : IsSccPartition g (algorithmT g).groupOf := by
  refine ⟨⟨by simp [algorithmT, read], fun i hi => ?_⟩, fun u hu v hv => ?_⟩
  · rw [numGroups_algorithmT hg] at hi
    exact (mem_algorithmT_groupOf hg).2 hi
  · rw [gid_algorithmT hu, gid_algorithmT hv, final_mutual_iff hg hu hv]
    have := final_emitted_lt hg hu
    have := final_emitted_lt hg hv
    omega

/-- **Algorithm T's ids are in topological order** (Tarjan–Zwick Theorem 3.5). -/
theorem idsTopological_algorithmT : IdsTopological g (algorithmT g).groupOf := by
  intro a ha
  obtain ⟨x, y, hxy, hne, rfl⟩ := mem_quotient_arrows.1 ha
  have h := ends_final hg
  have hx : x < g.n := (hg _ hxy).1
  have hy : y < g.n := (hg _ hxy).2
  dsimp only
  rw [gid_algorithmT hx, gid_algorithmT hy] at hne ⊢
  have hle := (h.out_closed x (h.out x hx) y (reaches_of_arrow hxy)).2
  have := final_emitted_lt hg hx
  have := final_emitted_lt hg hy
  omega

/-- **Algorithm T's member lists agree with its groups.** -/
theorem membersAgree_algorithmT : MembersAgree g (algorithmT g) := by
  have h := ends_final hg
  set k := (final g).groups.length
  have hgr : (algorithmT g).groups = (final g).groups.reverse := rfl
  refine ⟨by rw [numGroups_algorithmT hg, hgr, List.length_reverse], fun i hi => ?_,
    fun v hv => ?_⟩
  · rw [hgr, List.length_reverse] at hi
    have hi' : k - 1 - i < k := by omega
    have he : (algorithmT g).groups[i] = (final g).groups[k - 1 - i] := by
      simp only [hgr, List.getElem_reverse]
      rfl
    rw [he]
    refine ⟨h.grp_nodup _ (List.getElem_mem hi'), fun v hv => ?_⟩
    have hvn := final_member_lt hg (List.getElem_mem hi') hv
    refine ⟨hvn, ?_⟩
    rw [gid_algorithmT hvn, h.grp_idx _ hi' v hv]
    omega
  · rw [gid_algorithmT hv, hgr]
    obtain ⟨he, hvm⟩ := final_mem_group hg hv
    have hlt : k - 1 - (final g).emitted v < (final g).groups.reverse.length := by
      rw [List.length_reverse]
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.getElem_reverse]
    convert hvm using 2
    have hk : k = (final g).groups.length := rfl
    omega

/-- **Algorithm T lists each group's members in postorder** (Tarjan–Zwick p. 10). -/
theorem membersInPostorder_algorithmT : MembersInPostorder g (algorithmT g) := by
  intro m hm
  have hm' : m ∈ (final g).groups := List.mem_reverse.1 hm
  exact (ends_final hg).grp_sub m hm'

end Final

end AlgorithmT

/-- **Algorithm T's promise**, proved: on a well-formed graph, its groups are the strong
components with ids in topological order, its member lists agree with them, and each lists its
members in postorder. -/
theorem algorithmTPromise : AlgorithmTPromise := fun _ hg =>
  ⟨AlgorithmT.isSccPartition_algorithmT hg, AlgorithmT.idsTopological_algorithmT hg,
    AlgorithmT.membersAgree_algorithmT hg, AlgorithmT.membersInPostorder_algorithmT hg⟩

end AlgoDesign.Graphs.Scc
