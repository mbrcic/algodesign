/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkFuel

/-!
# Algorithm T walks the depth-first walk of `finishOrder`

`final_finished`: on a well-formed graph, the vertices finish in Algorithm T's walk in the order
`finishOrder` gives, the order of the depth-first walk with roots `0` upward (`Scc/Spec.lean`).
Inside one root's walk the two walks take the same steps (`sim_step`): the same frames, the same
vertices entered and finished. Algorithm T's walk from a root comes back to an empty path within
fewer steps than one walk's fuel, since its bound on the steps left falls at every step
(`exists_path_nil`); after that a further step of the depth-first walk changes nothing. Algorithm
T's outer loop then moves to the next root, as `finishOrder`'s fold does.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-- The depth-first walk's state matches Algorithm T's: the same vertices entered, frames and
vertices finished. -/
structure Sim (w : Walk) (s : Dfs) : Prop where
  seen : ∀ v, s.seen v = true ↔ w.pre v ≠ 0
  stack : s.stack = w.path
  finished : s.finished = w.finished

theorem postvisit_finished (w : Walk) (v : ℕ) :
    (postvisit g w v).finished = w.finished ++ [v] := by
  unfold postvisit; dsimp only; split <;> rfl

theorem run_add (w : Walk) : ∀ a b, runMove g (a + b) w = runMove g b (runMove g a w)
  | 0, b => by simp [runMove]
  | a + 1, b => by
    rw [Nat.add_right_comm]
    exact run_add (move g w) a b

theorem dfs_run_add (rows : ℕ → List (ℕ × ℕ)) :
    ∀ (a b : ℕ) (s : Dfs), Dfs.run rows (a + b) s = Dfs.run rows b (Dfs.run rows a s)
  | 0, b, s => by simp [Dfs.run]
  | a + 1, b, s => by
    rw [Nat.add_right_comm]
    exact dfs_run_add rows a b (Dfs.step rows s)

theorem dfs_run_nil (rows : ℕ → List (ℕ × ℕ)) {s : Dfs} (hs : s.stack = []) :
    ∀ k, Dfs.run rows k s = s
  | 0 => rfl
  | k + 1 => by
    have : Dfs.step rows s = s := by simp [Dfs.step, hs]
    simp only [Dfs.run, this, dfs_run_nil rows hs k]

/-- **One step inside a root's walk is one step of the depth-first walk.** -/
theorem sim_step {w : Walk} {s : Dfs} (h : Inv g w) (hsim : Sim w s) (hne : w.path ≠ []) :
    Sim (move g w) (Dfs.step g.out s) := by
  rcases hs : w.path with _ | ⟨⟨v, i⟩, rest⟩
  · exact absurd hs hne
  have hst : s.stack = (v, i) :: rest := by rw [hsim.stack, hs]
  rcases hi : (g.out v)[i]? with _ | ⟨x, id⟩
  · have hD : Dfs.step g.out s = { s with stack := rest, finished := s.finished ++ [v] } := by
      simp [Dfs.step, hst, hi]
    rw [hD]
    simp only [move, hs, hi]
    rcases rest with _ | ⟨⟨u, j⟩, rest'⟩
    · exact ⟨by simpa [postvisit_pre] using hsim.seen, by simp [postvisit_path],
        by simp [postvisit_finished, hsim.finished]⟩
    · exact ⟨by simpa [postvisit_pre] using hsim.seen, by simp [postvisit_path],
        by simp [postvisit_finished, hsim.finished]⟩
  · simp only [move, hs, hi]
    by_cases hx : w.pre x = 0
    · have hl : w.low x = 0 := (h.low_zero x).2 hx
      have hseen : s.seen x = false := by
        by_contra hne'
        exact ((hsim.seen x).1 (by simpa using hne')) hx
      have hD : Dfs.step g.out s =
          { s with seen := Function.update s.seen x true, stack := (x, 0) :: (v, i + 1) :: rest,
                   entered := s.entered ++ [x] } := by
        simp [Dfs.step, hst, hi, hseen]
      rw [hD]
      simp only [hl, ↓reduceIte]
      refine ⟨fun y => ?_, by simp, by simp [hsim.finished]⟩
      by_cases hyx : y = x
      · subst hyx
        simp
      · simp [Function.update_of_ne hyx, hsim.seen y]
    · have hl : w.low x ≠ 0 := (h.low_zero x).not.2 hx
      have hseen : s.seen x = true := (hsim.seen x).2 hx
      have hD : Dfs.step g.out s = { s with stack := (v, i + 1) :: rest } := by
        simp [Dfs.step, hst, hi, hseen]
      rw [hD]
      simp only [hl, ↓reduceIte]
      exact ⟨by simpa using hsim.seen, by simp, by simp [hsim.finished]⟩

/-- Steps inside a root's walk match step for step. -/
theorem sim_run (hg : g.WellFormed) : ∀ (k : ℕ) {w : Walk} {s : Dfs}, Inv g w → Sim w s →
    (∀ j < k, (runMove g j w).path ≠ []) → Sim (runMove g k w) (Dfs.run g.out k s)
  | 0, _, _, _, hsim, _ => hsim
  | k + 1, w, s, h, hsim, hne => by
    simp only [runMove, Dfs.run]
    exact sim_run hg k (inv_step hg h) (sim_step h hsim (hne 0 (Nat.succ_pos _)))
      fun j hj => hne (j + 1) (by omega)

/-- What a root's walk has left: the vertices not entered and the frames. -/
def innerWork (g : Digraph) (w : Walk) : ℕ := unenteredWork g w + frameWork g w.path

theorem step_next {w : Walk} (hne : w.path ≠ []) : (move g w).next = w.next := by
  rcases hs : w.path with _ | ⟨⟨v, i⟩, rest⟩
  · exact absurd hs hne
  rcases hi : (g.out v)[i]? with _ | ⟨x, id⟩
  · simp only [move, hs, hi]
    rcases rest with _ | ⟨⟨u, j⟩, rest'⟩
    · simp [postvisit_next]
    · simp [postvisit_next]
  · simp only [move, hs, hi]
    split_ifs <;> simp

/-- **A root's walk comes back to an empty path**, within its work left. -/
theorem exists_path_nil (hg : g.WellFormed) : ∀ (k : ℕ) {w : Walk}, Inv g w → innerWork g w ≤ k →
    ∃ j ≤ k, (runMove g j w).path = [] ∧ ∀ j' < j, (runMove g j' w).path ≠ []
  | k, w, h, hk => by
    by_cases hp : w.path = []
    · exact ⟨0, Nat.zero_le _, hp, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
    · have hlt := potential_step_lt h fun hd => hp hd.1
      have hnx := step_next (g := g) hp
      unfold potential at hlt
      rw [hnx] at hlt
      cases k with
      | zero =>
        exfalso
        unfold innerWork at hk
        omega
      | succ k =>
        obtain ⟨j, hj, hjp, hjne⟩ := exists_path_nil hg k (inv_step hg h) (by
          unfold innerWork at hk ⊢
          omega)
        refine ⟨j + 1, by omega, hjp, fun j' hj' => ?_⟩
        cases j' with
        | zero => exact hp
        | succ j' => exact hjne j' (by omega)

theorem innerWork_previsit_root {w : Walk} (hp : w.path = []) {r : ℕ} (hr : r < g.n)
    (h0 : w.pre r = 0) : innerWork g (previsit w r) < fuel g := by
  have hU := unenteredWork_previsit (g := g) (w := w) hr h0 []
  have hw : ({ w with path := [] } : Walk) = w := by rw [← hp]
  rw [hw] at hU
  have hle : unenteredWork g w ≤
      ((List.range g.n).map fun v => (g.out v).length).sum + 2 * g.n := by
    unfold unenteredWork
    have : ∀ l : List ℕ, (l.map fun v => if w.pre v = 0 then (g.out v).length + 2 else 0).sum ≤
        (l.map fun v => (g.out v).length).sum + 2 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        split_ifs <;> omega
    simpa using this (List.range g.n)
  have hs := sum_out_length_le (g := g)
  unfold innerWork fuel
  simp only [previsit_path, hp, frameWork, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

theorem dfs_seen_step (rows : ℕ → List (ℕ × ℕ)) {s : Dfs} {v : ℕ} (h : s.seen v = true) :
    (Dfs.step rows s).seen v = true := by
  unfold Dfs.step
  split
  · exact h
  · split
    · split
      · exact h
      · rename_i y _ _ _
        by_cases hvy : v = y
        · subst hvy
          simp
        · simp [Function.update_of_ne hvy, h]
    · exact h

theorem dfs_seen_run (rows : ℕ → List (ℕ × ℕ)) :
    ∀ (k : ℕ) {s : Dfs} {v : ℕ}, s.seen v = true → (Dfs.run rows k s).seen v = true
  | 0, _, _, h => h
  | k + 1, _, _, h => dfs_seen_run rows k (dfs_seen_step rows h)

theorem step_root_entered {w : Walk} (hp : w.path = []) (hn : w.next < g.n)
    (hl : w.low w.next ≠ 0) : move g w = { w with next := w.next + 1 } := by
  simp [move, hp, hn, hl]

/-- **Algorithm T's walk follows `finishOrder`'s fold, root by root.** -/
theorem exists_run_roots (hg : g.WellFormed) : ∀ r ≤ g.n, ∃ k,
    (runMove g k (start g)).path = [] ∧ (runMove g k (start g)).next = r ∧
      Sim (runMove g k (start g)) ((List.range r).foldl (Dfs.visit g.out (fuel g)) Dfs.init)
  | 0, _ => ⟨0, rfl, rfl, ⟨fun v => by simp [runMove, start, Dfs.init], rfl, rfl⟩⟩
  | r + 1, hr => by
    obtain ⟨k, hp, hn, hsim⟩ := exists_run_roots hg r (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w := runMove g k (start g) with hw
    have h : Inv g w := inv_run hg k (inv_start g)
    set s := (List.range r).foldl (Dfs.visit g.out (fuel g)) Dfs.init
    have hrn : r < g.n := by omega
    by_cases h0 : w.pre r = 0
    · -- a new root: its walk, then the outer loop moves on
      have hseen : s.seen r = false := by
        by_contra hne
        exact ((hsim.seen r).1 (by simpa using hne)) h0
      have hl : w.low r = 0 := (h.low_zero r).2 h0
      have hstep : move g w = previsit w r := by
        simp [move, hp, hn, hrn, hl]
      set w0 := previsit w r
      set s0 : Dfs :=
        { s with seen := Function.update s.seen r true, stack := [(r, 0)],
                 entered := s.entered ++ [r] }
      have h0' : Inv g w0 := by rw [← hstep]; exact inv_step hg h
      have hsim0 : Sim w0 s0 := by
        refine ⟨fun y => ?_, by simp [w0, s0, hp], by simp [w0, s0, hsim.finished]⟩
        by_cases hyr : y = r
        · subst hyr
          simp [w0, s0]
        · simp [w0, s0, Function.update_of_ne hyr, hsim.seen y]
      obtain ⟨j, hj, hjp, hjne⟩ := exists_path_nil hg _ h0' le_rfl
      have hjf : j < fuel g := lt_of_le_of_lt hj (innerWork_previsit_root hp hrn h0)
      have hsimj := sim_run hg j h0' hsim0 hjne
      have hvisit : Dfs.visit g.out (fuel g) s r = Dfs.run g.out j s0 := by
        simp only [Dfs.visit, hseen]
        rw [show fuel g = j + (fuel g - j) by omega, dfs_run_add]
        exact dfs_run_nil _ (by rw [hsimj.stack, hjp]) _
      set w1 := runMove g j w0
      have h1 : Inv g w1 := inv_run hg j h0'
      have hn1 : w1.next = r := by
        have : ∀ j' ≤ j, (runMove g j' w0).next = r := by
          intro j' hj'
          induction j' with
          | zero => simp [runMove, w0, hn]
          | succ j' ih =>
            rw [run_add, show runMove g 1 (runMove g j' w0) = move g (runMove g j' w0) from rfl,
              step_next (hjne j' (by omega)), ih (by omega)]
        exact this j le_rfl
      have hr1 : w1.pre r ≠ 0 :=
        (hsimj.seen r).1 (dfs_seen_run _ j (by simp [s0]))
      have hstep1 : move g w1 = { w1 with next := w1.next + 1 } :=
        step_root_entered (by rw [← hsimj.stack]; exact (by rw [hsimj.stack, hjp]))
          (by rw [hn1]; exact hrn) (by rw [hn1]; exact (h1.low_zero r).not.2 hr1)
      have hrun : runMove g (k + 1 + j + 1) (start g) = move g w1 := by
        rw [run_add (start g) (k + 1 + j) 1, run_add (start g) (k + 1) j,
          run_add (start g) k 1]
        simp only [runMove, ← hw, hstep]
        rfl
      refine ⟨k + 1 + j + 1, ?_, ?_, ?_⟩
      · rw [hrun, hstep1]
        exact hjp
      · rw [hrun, hstep1]
        simp [hn1]
      · rw [hrun, hstep1, hvisit]
        exact ⟨hsimj.seen, hsimj.stack, hsimj.finished⟩
    · -- an entered root: the outer loop moves on
      have hl : w.low r ≠ 0 := (h.low_zero r).not.2 h0
      have hseen : s.seen r = true := (hsim.seen r).2 h0
      have hstep : move g w = { w with next := w.next + 1 } :=
        step_root_entered hp (by rw [hn]; exact hrn) (by rw [hn]; exact hl)
      refine ⟨k + 1, ?_, ?_, ?_⟩
      · rw [run_add, show runMove g 1 w = move g w from rfl, hstep]
        exact hp
      · rw [run_add, show runMove g 1 w = move g w from rfl, hstep]
        simp [hn]
      · rw [run_add, show runMove g 1 w = move g w from rfl, hstep]
        simp only [Dfs.visit, hseen, ↓reduceIte]
        exact ⟨hsim.seen, hsim.stack, hsim.finished⟩

/-- **The vertices finish in `finishOrder`.** -/
theorem final_finished (hg : g.WellFormed) : (finalMove g).finished = finishOrder g := by
  obtain ⟨k, hp, hn, hsim⟩ := exists_run_roots hg g.n le_rfl
  obtain ⟨hp', hn'⟩ := final_done hg
  have hfin : runMove g k (start g) = finalMove g := by
    rcases le_total k (steps g) with hk | hk
    · unfold finalMove
      rw [show steps g = k + (steps g - k) by omega, run_add, run_of_done hp (by omega)]
    · rw [show k = steps g + (k - steps g) by omega, run_add]
      exact run_of_done hp' hn' _
  rw [← hfin, ← hsim.finished]
  rfl

end AlgorithmT

end AlgoDesign.Graphs.Scc
