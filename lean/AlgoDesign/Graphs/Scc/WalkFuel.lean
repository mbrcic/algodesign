/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.WalkStep

/-!
# Algorithm T: `3 n + m` moves finish the walk

A bound on the steps left (`potential`): each vertex not yet entered may still cost its whole row,
its entry and its finish; each frame its arrows not yet looked at and its finish; the outer loop
one step per root not yet passed. Every step that does not stand at the end lowers it
(`potential_step_lt`), and at the start it is at most `3 n + m`, since the rows together hold at
most `m` arrows (`sum_out_length_le`). So the moves run for `steps g` stand at the end: no current
vertex and every root passed (`final_done`), every vertex entered and finished, and every group out
(`final_out`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

open Relation

variable {g : Digraph}

/-! ## The rows hold at most `m` arrows -/

theorem length_filter_le_one {α : Type*} {p : α → Prop} [DecidablePred p] :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, p x → p y → x = y) → (l.filter p).length ≤ 1
  | [], _, _ => by simp
  | a :: l, hnd, hu => by
    rw [List.filter_cons]
    split_ifs with ha
    · have : l.filter p = [] := List.filter_eq_nil_iff.2 fun y hy hpy => by
        have := hu a List.mem_cons_self y (List.mem_cons_of_mem _ hy) (by simpa using ha)
          (by simpa using hpy)
        exact (List.nodup_cons.1 hnd).1 (this ▸ hy)
      simp [this]
    · exact length_filter_le_one (List.nodup_cons.1 hnd).2
        fun x hx y hy => hu x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

theorem sum_map_ite_eq_countP {β : Type*} (q : β → Bool) :
    ∀ J : List β, (J.map fun j => if q j then 1 else 0).sum = J.countP q
  | [] => rfl
  | j :: J => by
    rw [List.map_cons, List.sum_cons, sum_map_ite_eq_countP q J, List.countP_cons]
    omega

/-- Counting by disjoint properties counts each element at most once. -/
theorem sum_countP_le {α β : Type*} (J : List β) (p : β → α → Bool) :
    ∀ l : List α, (∀ a ∈ l, (J.filter fun j => p j a).length ≤ 1) →
      (J.map fun j => l.countP (p j)).sum ≤ l.length
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_countP_le J p l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have ha := h a List.mem_cons_self
    have key : (J.map fun j => (a :: l).countP (p j)) =
        J.map fun j => l.countP (p j) + if p j a then 1 else 0 :=
      List.map_congr_left fun j _ => List.countP_cons
    rw [key, List.sum_map_add, sum_map_ite_eq_countP (fun j => p j a),
      List.countP_eq_length_filter, List.length_cons]
    omega

theorem out_length_eq (v : ℕ) :
    (g.out v).length =
      ((List.range g.n).map fun w =>
        (List.range g.arrows.length).countP fun i => g.arrows[i]? = some (v, w)).sum := by
  simp only [Digraph.out, List.length_flatMap, List.length_map, Digraph.idsBetween,
    List.countP_eq_length_filter]

/-- **The rows hold at most `m` arrows.** -/
theorem sum_out_length_le :
    ((List.range g.n).map fun v => (g.out v).length).sum ≤ g.arrows.length := by
  simp only [out_length_eq]
  set L := List.range g.arrows.length
  -- an arrow is counted by its tail, and within its tail by its head
  have hinner : ∀ v, ((List.range g.n).map fun w =>
      L.countP fun i => g.arrows[i]? = some (v, w)).sum ≤
        L.countP fun i => (g.arrows[i]?).map Prod.fst = some v := by
    intro v
    have := sum_countP_le (List.range g.n) (fun w i => decide (g.arrows[i]? = some (v, w)))
      (L.filter fun i => (g.arrows[i]?).map Prod.fst = some v) fun i _ =>
        length_filter_le_one List.nodup_range fun x _ y _ hx hy => by
          have hx' : g.arrows[i]? = some (v, x) := by simpa using hx
          have hy' : g.arrows[i]? = some (v, y) := by simpa using hy
          rw [hx'] at hy'
          have hy := hy'
          simp only [Option.some.injEq, Prod.mk.injEq] at hy
          exact hy.2
    rw [List.countP_eq_length_filter]
    refine le_trans (le_of_eq ?_) this
    congr 1
    refine List.map_congr_left fun w _ => ?_
    rw [List.countP_filter]
    exact List.countP_congr fun i _ => by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h => ⟨h, by rw [h]; rfl⟩, fun h => h.1⟩
  refine le_trans (List.sum_le_sum fun v _ => hinner v) ?_
  refine (sum_countP_le (List.range g.n)
    (fun v i => decide ((g.arrows[i]?).map Prod.fst = some v)) L
    fun i _ => length_filter_le_one List.nodup_range fun x _ y _ hx hy => ?_).trans
      (by simp [L])
  have hx' : (g.arrows[i]?).map Prod.fst = some x := by simpa using hx
  have hy' : (g.arrows[i]?).map Prod.fst = some y := by simpa using hy
  rw [hx'] at hy'
  exact Option.some.inj hy'

/-! ## The bound on the steps left -/

/-- What the vertices not yet entered may still cost: each its row, its entry and its finish. -/
def unenteredWork (g : Digraph) (w : Walk) : ℕ :=
  ((List.range g.n).map fun v => if w.pre v = 0 then (g.out v).length + 2 else 0).sum

/-- What the frames have left to do: for each, the arrows of its row not yet looked at, and its
finish. -/
def frameWork (g : Digraph) (path : List (ℕ × ℕ)) : ℕ :=
  (path.map fun f => (g.out f.1).length + 1 - f.2).sum

/-- **A bound on the steps left.** -/
def potential (g : Digraph) (w : Walk) : ℕ :=
  unenteredWork g w + frameWork g w.path + (g.n - w.next)

theorem sum_map_update {f f' : ℕ → ℕ} {x : ℕ} (hf : ∀ y, y ≠ x → f' y = f y) :
    ∀ l : List ℕ, l.Nodup → x ∈ l → (l.map f').sum + f x = (l.map f).sum + f' x
  | [], _, hx => absurd hx List.not_mem_nil
  | a :: l, hnd, hx => by
    simp only [List.map_cons, List.sum_cons]
    by_cases hax : a = x
    · subst hax
      have hal : a ∉ l := (List.nodup_cons.1 hnd).1
      have : (l.map f').sum = (l.map f).sum :=
        congrArg List.sum (List.map_congr_left fun y hy => hf y fun he => hal (he ▸ hy))
      omega
    · have := sum_map_update hf l (List.nodup_cons.1 hnd).2 (by simpa [Ne.symm hax] using hx)
      rw [hf a hax]
      omega

theorem unenteredWork_previsit {w : Walk} {x : ℕ} (hx : x < g.n) (h0 : w.pre x = 0)
    (P : List (ℕ × ℕ)) :
    unenteredWork g (previsit { w with path := P } x) + ((g.out x).length + 2) =
      unenteredWork g w := by
  unfold unenteredWork
  rw [previsit_pre]
  have := sum_map_update (f := fun v => if w.pre v = 0 then (g.out v).length + 2 else 0)
    (f' := fun v => if Function.update w.pre x (w.time + 1) v = 0 then
      (g.out v).length + 2 else 0) (x := x) (fun y hy => by simp [Function.update_of_ne hy])
    (List.range g.n) List.nodup_range (List.mem_range.2 hx)
  simp only [h0, ↓reduceIte, Function.update_self, Nat.add_one_ne_zero, add_zero] at this
  exact this

theorem postvisit_path (w : Walk) (v : ℕ) : (postvisit g w v).path = w.path := by
  unfold postvisit; dsimp only; split <;> rfl

theorem postvisit_pre (w : Walk) (v : ℕ) : (postvisit g w v).pre = w.pre := by
  unfold postvisit; dsimp only; split <;> rfl

theorem postvisit_next (w : Walk) (v : ℕ) : (postvisit g w v).next = w.next := by
  unfold postvisit; dsimp only; split <;> rfl

theorem unenteredWork_congr {w w' : Walk} (h : w'.pre = w.pre) :
    unenteredWork g w' = unenteredWork g w := by
  unfold unenteredWork
  rw [h]

theorem frameWork_cons (f : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    frameWork g (f :: P) = (g.out f.1).length + 1 - f.2 + frameWork g P := by
  simp [frameWork]

/-- **Every step short of the end lowers the bound.** -/
theorem potential_step_lt {w : Walk} (h : Inv g w) (hne : ¬ (w.path = [] ∧ g.n ≤ w.next)) :
    potential g (move g w) < potential g w := by
  rcases hs : w.path with _ | ⟨⟨v, i⟩, rest⟩
  · obtain ⟨gw, t, lo, le, pa, fo, gr, em, ne, pr, fi, re⟩ := w
    simp only at hs
    subst hs
    have hn : ne < g.n := by
      simp only [true_and] at hne
      omega
    simp only [move, hn, ↓reduceIte]
    split_ifs with hl
    · have h0 : pr ne = 0 := (h.low_zero _).1 hl
      have hU := unenteredWork_previsit (g := g)
        (w := ⟨gw, t, lo, le, [], fo, gr, em, ne, pr, fi, re⟩) hn h0 []
      unfold potential
      rw [previsit_path, frameWork_cons, previsit_next]
      simp only [frameWork, List.map_nil, List.sum_nil] at hU ⊢
      omega
    · unfold potential
      simp only [unenteredWork, frameWork]
      omega
  · have hf := h.frames
    rw [hs] at hf
    have hle := hf.le_length
    have hF0 : frameWork g w.path = (g.out v).length + 1 - i + frameWork g rest := by
      rw [hs, frameWork_cons]
    rcases hi : (g.out v)[i]? with _ | ⟨x, id⟩
    · have hil : (g.out v).length ≤ i := List.getElem?_eq_none_iff.1 hi
      have hw2 : ∀ w2 : Walk, w2.pre = w.pre → w2.path = rest → w2.next = w.next →
          potential g w2 < potential g w := by
        intro w2 hp hpa hne'
        unfold potential
        rw [unenteredWork_congr hp, hpa, hne', hF0]
        omega
      simp only [move, hs, hi]
      rcases rest with _ | ⟨⟨u, j⟩, rest'⟩
      · exact hw2 _ (by rw [postvisit_pre]) (by rw [postvisit_path]) (by rw [postvisit_next])
      · exact hw2 _ (by rw [retreat_pre, postvisit_pre]) (by rw [retreat_path, postvisit_path])
          (by rw [retreat_next, postvisit_next])
    · have hil : i < (g.out v).length := (List.getElem?_eq_some_iff.1 hi).1
      have hxn : x < g.n := lt_of_out hi
      simp only [move, hs, hi]
      split_ifs with hl
      · have h0 : w.pre x = 0 := (h.low_zero x).1 hl
        have hU := unenteredWork_previsit (w := w) hxn h0 ((v, i + 1) :: rest)
        unfold potential
        rw [previsit_path, frameWork_cons, frameWork_cons, previsit_next, hF0]
        dsimp only
        omega
      · unfold potential
        have hU0 : unenteredWork g { w with path := (v, i + 1) :: rest } = unenteredWork g w :=
          unenteredWork_congr rfl
        rw [unenteredWork_congr (retreat_pre _ _ _), retreat_path, retreat_next, hF0,
          frameWork_cons, hU0]
        dsimp only
        omega

/-- At the end, a step changes nothing. -/
theorem step_of_done {w : Walk} (hp : w.path = []) (hn : g.n ≤ w.next) : move g w = w := by
  simp [move, hp, Nat.not_lt.2 hn]

theorem run_of_done {w : Walk} (hp : w.path = []) (hn : g.n ≤ w.next) :
    ∀ k, runMove g k w = w
  | 0 => rfl
  | k + 1 => by simp only [runMove, step_of_done hp hn, run_of_done hp hn k]

/-- **Enough fuel reaches the end**: run with at least the bound on the steps left, the walk has
no current vertex and has passed every root. -/
theorem run_done (hg : g.WellFormed) : ∀ (k : ℕ) {w : Walk}, Inv g w → potential g w ≤ k →
    (runMove g k w).path = [] ∧ g.n ≤ (runMove g k w).next
  | 0, w, h, hp => by
    simp only [runMove]
    rcases hs : w.path with _ | ⟨⟨v, i⟩, rest⟩
    · unfold potential at hp
      exact ⟨rfl, by omega⟩
    · have hf := h.frames
      rw [hs] at hf
      have := hf.le_length
      unfold potential frameWork at hp
      rw [hs] at hp
      simp only [List.map_cons, List.sum_cons] at hp
      omega
  | k + 1, w, h, hp => by
    by_cases hd : w.path = [] ∧ g.n ≤ w.next
    · rw [run_of_done hd.1 hd.2]
      exact hd
    · simp only [runMove]
      exact run_done hg k (inv_step hg h) (by have := potential_step_lt h hd; omega)

theorem potential_start_le : potential g (start g) ≤ steps g := by
  have hs := sum_out_length_le (g := g)
  have hu : unenteredWork g (start g) =
      ((List.range g.n).map fun v => (g.out v).length).sum + 2 * g.n := by
    unfold unenteredWork
    simp only [start, ↓reduceIte]
    rw [List.sum_map_add]
    simp [mul_comm]
  unfold potential steps
  rw [hu]
  simp [frameWork, start]
  omega

/-- **The walk run for `steps g` stands at the end**: no current vertex, every root passed. -/
theorem final_done (hg : g.WellFormed) : (finalMove g).path = [] ∧ g.n ≤ (finalMove g).next :=
  run_done hg _ (inv_start g) potential_start_le

theorem inv_final (hg : g.WellFormed) : Inv g (finalMove g) := inv_run hg _ (inv_start g)

/-- **At the end every vertex is in a group out.** -/
theorem final_out (hg : g.WellFormed) {v : ℕ} (hv : v < g.n) :
    v ∈ (finalMove g).groups.flatten := by
  have h := inv_final hg
  obtain ⟨hp, hn⟩ := final_done hg
  have hv0 := h.roots v (by omega)
  have hvf : v ∈ (finalMove g).finished := by
    rcases (h.entered v).1 hv0 with hvp | hvf
    · simp [vertices, hp] at hvp
    · exact hvf
  by_contra ho
  obtain ⟨q, hq, -⟩ := h.open_gray v hvf ho
  simp [vertices, hp] at hq

end AlgorithmT

end AlgoDesign.Graphs.Scc
