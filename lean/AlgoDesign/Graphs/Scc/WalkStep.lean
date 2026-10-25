/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkLeader

/-!
# Algorithm T: every move keeps the invariant

`inv_step`: on a well-formed graph, one move of the walk (a step without the stop when done)
keeps `Inv`, case by case: entering a
root or a vertex an arrow leads to (`inv_previsit`), moving the outer loop on, coming back over an
arrow at once (`inv_retreat`), finishing a vertex that does not lead (`inv_finish_follower`), and
finishing a leader, whose group comes out (`inv_finish_leader`). A root that finishes always
leads. So every state of every run of moves from the start keeps `Inv` (`inv_run`), and with it
the box's three invariants (`valid_runMove`). The stop when done is `Scc/WalkStop.lean`.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-- A root that has looked at its whole row leads: no member of its component was entered
before it. -/
theorem Inv.lead_of_root (hg : g.WellFormed) {w : Walk} (h : Inv g w) {v i : ℕ}
    (hs : w.path = [(v, i)]) (hi : (g.out v)[i]? = none) : w.lead v = true := by
  rw [h.lead_iff_first hs hi hg]
  intro u hu huv
  have hvp : v ∈ vertices w := by simp [vertices, hs]
  obtain ⟨q, hq, -, hqu⟩ := h.gray_min v hvp u hu huv
  simp only [vertices, hs, List.map_cons, List.map_nil, List.mem_singleton] at hq
  exact hq ▸ hqu

theorem with_retreats_nil {w x : Walk} (hx : x.retreats = w.retreats) :
    { x with retreats := w.retreats ++ [] } = x := by
  rw [List.append_nil, ← hx]

/-- **One move keeps the invariant.** -/
theorem inv_step (hg : g.WellFormed) {w : Walk} (h : Inv g w) : Inv g (move g w) := by
  rcases hs : w.path with _ | ⟨⟨v, i⟩, rest⟩
  · -- no current vertex: the outer loop
    obtain ⟨gw, t, lo, le, pa, fo, gr, em, ne, pr, fi, re⟩ := w
    simp only at hs
    subst hs
    simp only [move]
    split_ifs with hn hl
    · have h0 : pr ne = 0 := (h.low_zero _).1 hl
      exact inv_previsit hg h (P := []) (x := ne) (by simp [vertices]) trivial
        (by simp [vertices]) h0 hn
    · refine { h with roots := fun r hr => ?_ }
      by_cases hrn : r < ne
      · exact h.roots r hrn
      · have : r = ne := by simp at hr; omega
        subst this
        exact (h.low_zero _).not.1 hl
    · exact h
  · have hf := h.frames
    rw [hs] at hf
    have hvp : v ∈ vertices w := by simp [vertices, hs]
    rcases hi : (g.out v)[i]? with _ | ⟨x, id⟩
    · -- the row is done: `v` finishes
      have hv0 := h.path_entered hvp
      rcases rest with _ | ⟨⟨u, j⟩, rest'⟩
      · have hl := h.lead_of_root hg hs hi
        have := inv_finish_leader hg h hs hi hl [] (by simp) trivial
        simp only [move, hs, hi]
        rwa [with_retreats_nil (by rw [postvisit_of_lead (by exact hl)])] at this
      · simp only [move, hs, hi]
        by_cases hl : w.lead v = true
        · have hup : u ∈ vertices w := by simp [vertices, hs]
          have hu0 := h.path_entered hup
          have hpv := postvisit_of_lead (g := g) (w := { w with path := (u, j) :: rest' })
            (v := v) hl
          rw [retreat_eq_of_not_lt]
          · have := inv_finish_leader hg h hs hi hl [(u, v)] (by simp) (by
              have := hf.2.2.pop (log := w.retreats)
              simpa using this)
            rwa [hpv] at this ⊢
          · rw [hpv]
            dsimp only
            have hvin : v ∈ (popFollowers w.low (w.low v) w.followers).1.reverse ++ [v] := by simp
            simp only [hvin, ↓reduceIte]
            split_ifs
            · exact lt_irrefl _
            · exact Nat.not_lt.2 (h.low_lt_done hu0 (h.not_out_of_path hup)).le
        · exact inv_finish_follower hg h hs hi (by simpa using hl)
    · -- an arrow to look at
      have hxn : x < g.n := lt_of_out hi
      simp only [move, hs, hi]
      split_ifs with hl
      · have h0 : w.pre x = 0 := (h.low_zero x).1 hl
        refine inv_previsit hg h (P := (v, i + 1) :: rest) ?_ ?_ ?_ h0 hxn
        · simp [vertices, hs]
        · refine ⟨Nat.succ_pos _, (List.getElem?_eq_some_iff.1 hi).1, by simp [hi], hf.2.1, ?_⟩
          exact hf.2.2
        · intro p hp
          exact (h.reach p hp v (h.path_entered hvp) (h.pre_le_top hs hp)).tail (arrow_of_out hi)
      · exact inv_retreat h hs hi ((h.low_zero x).not.1 hl)

/-- **Every state of a run of moves keeps the invariant.** -/
theorem inv_run (hg : g.WellFormed) : ∀ (k : ℕ) {w : Walk}, Inv g w → Inv g (runMove g k w)
  | 0, _, h => h
  | k + 1, _, h => inv_run hg k (inv_step hg h)

/-- **Every state of the moves from the start keeps the box's three invariants.** -/
theorem valid_runMove (hg : g.WellFormed) (k : ℕ) : Valid (runMove g k (start g)) :=
  (inv_run hg k (inv_start g)).valid

end AlgorithmT

end AlgoDesign.Graphs.Scc
