/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.BellmanFord.Decide
public import AlgoDesign.Paths.Dijkstra.Walk
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Card

/-! # Cheapest paths with negative arrows: facts about paths

The facts the rounds' proofs share: how a path grows by one arrow and joins another, how a path
that passes no vertex twice comes apart at a vertex it passes, and why, when no negative cycle
is reached, some path that passes no vertex twice costs no more than any path. -/

@[expose] public section

namespace AlgoDesign.Paths

open AlgoDesign.Graphs

namespace Network

variable {N : Network}

/-! ## Paths -/

theorem visits_append (u : ℕ) (p q : List ℕ) :
    N.visits u (p ++ q) = N.visits u p ++ q.map N.target := by
  simp [visits]

theorem pathCost_singleton (i : ℕ) : N.pathCost [i] = N.arrowCost i := by
  simp [pathCost]

theorem isWalk_nil_iff {s v : ℕ} : N.IsWalk s [] v ↔ v = s := by
  simp [IsWalk, ends, eq_comm]

theorem isWalk_nil (s : ℕ) : N.IsWalk s [] s := isWalk_nil_iff.2 rfl

/-- **A path grows by one arrow.** -/
theorem IsWalk.snoc {s : ℕ} {p : List ℕ} {x i w : ℕ} (hp : N.IsWalk s p x)
    (hi : N.g.arrows[i]? = some (x, w)) : N.IsWalk s (p ++ [i]) w :=
  ends_append_singleton.2 ⟨x, hp, hi⟩

/-- **A path comes apart at its last arrow.** -/
theorem IsWalk.eq_snoc {s : ℕ} {p : List ℕ} {w : ℕ} (hp : N.IsWalk s p w) (hne : p ≠ []) :
    ∃ q i x, p = q ++ [i] ∧ N.IsWalk s q x ∧ N.g.arrows[i]? = some (x, w) := by
  obtain ⟨q, i, rfl⟩ := List.eq_nil_or_concat p |>.resolve_left hne
  rw [List.concat_eq_append] at hp ⊢
  obtain ⟨x, hx, hi⟩ := ends_append_singleton.1 hp
  exact ⟨q, i, x, rfl, hx, hi⟩

/-- Two paths, the second from where the first ends, make one. -/
theorem IsWalk.append {s x v : ℕ} {p q : List ℕ} (hp : N.IsWalk s p x) (hq : N.IsWalk x q v) :
    N.IsWalk s (p ++ q) v := by
  unfold IsWalk at *
  rw [ends_append, hp]
  exact hq

/-- A path from a vertex of a well-formed network ends at one. -/
theorem IsWalk.lt {s : ℕ} {p : List ℕ} {v : ℕ} (hN : N.WellFormed) (hs : s < N.g.n)
    (hp : N.IsWalk s p v) : v < N.g.n := by
  rcases eq_or_ne p [] with rfl | hne
  · rw [isWalk_nil_iff.1 hp]; exact hs
  · obtain ⟨q, i, x, -, -, hi⟩ := hp.eq_snoc hne
    exact (hN.1 _ (List.mem_of_getElem? hi)).2

theorem IsWalk.reaches {s : ℕ} {p : List ℕ} {v : ℕ} (hp : N.IsWalk s p v) : N.g.Reaches s v :=
  reaches_of_ends hp

/-- Every vertex `s` reaches has a path from `s`. -/
theorem exists_isWalk_of_reaches {s v : ℕ} (h : N.g.Reaches s v) : ∃ p, N.IsWalk s p v := by
  induction h with
  | refl => exact ⟨[], isWalk_nil s⟩
  | tail _ hab ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hab
    exact ⟨p ++ [i], hp.snoc hi⟩

/-! ## Paths that pass no vertex twice -/

/-- A path that passes no vertex twice, in a well-formed network, has fewer arrows than the
network has vertices. -/
theorem IsPath.length_lt {s : ℕ} {p : List ℕ} {v : ℕ} (hN : N.WellFormed) (hs : s < N.g.n)
    (hp : N.IsPath s p v) : p.length < N.g.n := by
  have h := hp.2.length_le_of_subset (fun y hy => List.mem_range.2 (hp.lt_of_mem hN hs hy))
  simp only [visits, List.length_cons, List.length_map, List.length_range] at h
  omega

/-- **A path that passes no vertex twice comes apart at a vertex it passes**: such a path to that
vertex, then a path on from it that passes no vertex twice. -/
theorem IsPath.split_at {s v : ℕ} :
    ∀ {p : List ℕ} {w : ℕ}, N.IsPath s p w → v ∈ N.visits s p →
      ∃ q r, p = q ++ r ∧ N.IsPath s q v ∧ N.IsWalk v r w ∧ (N.visits v r).Nodup := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro w hp hv
    simp only [visits, List.map_nil, List.mem_singleton] at hv
    subst hv
    rw [isPath_nil_iff.1 hp]
    exact ⟨[], [], rfl, isPath_nil _, isWalk_nil _, by simp [visits]⟩
  | append_singleton p i ih =>
    intro w hp hv
    obtain ⟨q, j, x, hqj, hq, hi, hw, hvis⟩ := hp.eq_snoc (by simp)
    obtain ⟨rfl, hij⟩ := List.append_inj' hqj rfl
    obtain rfl : i = j := by simpa using hij
    by_cases hvw : v = w
    · subst hvw
      exact ⟨p ++ [i], [], by simp, hp, isWalk_nil _, by simp [visits]⟩
    · have hv' : v ∈ N.visits s p := by
        rw [hvis] at hv
        rcases List.mem_append.1 hv with h | h
        · exact h
        · exact absurd (List.mem_singleton.1 h) hvw
      obtain ⟨q, r, rfl, hq', hr, hnd⟩ := ih hq hv'
      refine ⟨q, r ++ [i], by simp, hq', hr.snoc hi, ?_⟩
      rw [visits_append, List.map_singleton, target_eq hi, List.nodup_append]
      refine ⟨hnd, List.nodup_singleton w, fun a ha b hb => ?_⟩
      rw [List.mem_singleton.1 hb]
      rintro rfl
      apply hw
      rw [visits_append]
      rcases List.mem_cons.1 ha with h | h
      · rw [h]; exact List.mem_append_left _ hq'.mem_visits
      · exact List.mem_append_right _ h

end Network

namespace BellmanFord

open Network
open Dijkstra (LeadsBack)

variable {N : Network} {s : ℕ}

/-- **Without a negative cycle that the start reaches, some path that passes no vertex twice
costs no more than any path**: a path that comes back to a vertex has a cycle there, which is
not negative, and leaving it out leaves a cheaper or equal path. -/
theorem exists_path_le (hno : ¬ ∃ c, CycleBelowZero N s c) :
    ∀ {p : List ℕ} {v : ℕ}, N.IsWalk s p v → ∃ q, N.IsPath s q v ∧ N.pathCost q ≤ N.pathCost p := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro v hp
    rw [isWalk_nil_iff.1 hp]
    exact ⟨[], isPath_nil s, le_rfl⟩
  | append_singleton p i ih =>
    intro v hp
    obtain ⟨x, hx, hi⟩ := ends_append_singleton.1 hp
    obtain ⟨q, hq, hc⟩ := ih hx
    have hcost : N.pathCost (p ++ [i]) = N.pathCost p + N.arrowCost i := by
      rw [pathCost_append, pathCost_singleton]
    by_cases hv : v ∈ N.visits s q
    · obtain ⟨q₁, r, rfl, hq₁, hr, hnd⟩ := hq.split_at hv
      have hcyc : N.IsCycle v (r ++ [i]) := by
        refine ⟨by simp, hr.snoc hi, ?_⟩
        rw [visits_append, List.map_singleton, target_eq hi, List.dropLast_concat]
        exact hnd
      have h0 : ¬ N.pathCost (r ++ [i]) < 0 := fun h =>
        hno ⟨_, v, r ++ [i], hcyc, rfl, h, hq₁.isWalk.reaches⟩
      rw [pathCost_append, pathCost_singleton] at h0
      rw [pathCost_append] at hc
      exact ⟨q₁, hq₁, by rw [hcost]; linarith⟩
    · refine ⟨q ++ [i], (hq.snoc hi hv).1, ?_⟩
      rw [hcost, pathCost_append, pathCost_singleton]
      linarith

/-! ## Following the records back -/

section Trail

variable (prev : ℕ → Option ℕ)

theorem mem_trail {x v : ℕ} : ∀ {k}, v ∈ trail prev x k ↔ ∃ t ≤ k, (stepBack prev)^[t] x = v
  | 0 => by simp [trail, eq_comm]
  | k + 1 => by
    rw [trail, List.mem_cons, mem_trail]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨k + 1, le_rfl, h.symm⟩
      · exact ⟨t, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_or_ge t (k + 1) with h' | h'
      · exact Or.inr ⟨t, by omega, h⟩
      · obtain rfl : t = k + 1 := by omega
        exact Or.inl h.symm

theorem trail_ne_nil (x : ℕ) : ∀ k, trail prev x k ≠ []
  | 0 => by simp [trail]
  | _ + 1 => by simp [trail]

theorem head_trail (x : ℕ) : ∀ k, (trail prev x k).head? = some ((stepBack prev)^[k] x)
  | 0 => rfl
  | _ + 1 => rfl

theorem getLast_trail (x : ℕ) : ∀ k, (trail prev x k).getLast (trail_ne_nil prev x k) = x
  | 0 => rfl
  | k + 1 => by
    simp only [trail]
    rw [List.getLast_cons (trail_ne_nil prev x k)]
    exact getLast_trail x k

theorem isChain_trail {x : ℕ} :
    ∀ {k}, (∀ t < k, prev ((stepBack prev)^[t] x) ≠ none) →
      (trail prev x k).IsChain fun a b => prev b = some a
  | 0, _ => by simp [trail]
  | k + 1, h => by
    have ih := isChain_trail (k := k) fun t ht => h t (by omega)
    cases k with
    | zero =>
      simp only [trail]
      refine List.isChain_pair.2 ?_
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 (h 0 (by omega))
      simp only [Function.iterate_zero, id_eq] at hu
      rw [show (stepBack prev)^[0 + 1] x = stepBack prev x from rfl, stepBack_of_some prev hu, hu]
    | succ k =>
      simp only [trail] at ih ⊢
      refine List.isChain_cons_cons.2 ⟨?_, ih⟩
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 (h (k + 1) (by omega))
      rw [Function.iterate_succ_apply' _ (k + 1), stepBack_of_some prev hu, hu]

theorem nodup_trail {x : ℕ} :
    ∀ {k}, (∀ i j, i < j → j ≤ k → (stepBack prev)^[i] x ≠ (stepBack prev)^[j] x) →
      (trail prev x k).Nodup
  | 0, _ => by simp [trail]
  | k + 1, h => by
    rw [trail, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_trail fun i j hij hj => h i j hij (by omega)⟩
    obtain ⟨t, ht, he⟩ := (mem_trail prev).1 hm
    exact h t (k + 1) (by omega) le_rfl he

theorem iterate_shift {g : ℕ → ℕ} {x : ℕ} {i j : ℕ} (h : g^[i] x = g^[j] x) (m : ℕ) :
    g^[m + i] x = g^[m + j] x := by
  rw [Function.iterate_add_apply, Function.iterate_add_apply, h]

end Trail

variable {N : Network} {s : ℕ}

/-! ## Costs along the records -/

/-- **Arrows along the records**: a list of vertices each recording the one before it gives a path
along them whose cost, added to the first vertex's, is at most the last vertex's. -/
theorem walk_of_chain {st : State} (hP : PreviousArrowFits st) :
    ∀ (l : List ℕ) (a : ℕ), (∀ v ∈ a :: l, v < st.net.g.n) →
      (a :: l).IsChain (fun a b => st.prev b = some a) →
      ∃ p, st.net.IsWalk a p ((a :: l).getLast (by simp)) ∧ st.net.visits a p = a :: l ∧
        ∀ da ∈ st.cost a, ∃ db ∈ st.cost ((a :: l).getLast (by simp)), da + st.net.pathCost p ≤ db
  | [], a, _, _ => ⟨[], isWalk_nil a, by simp [visits], fun da hda => ⟨da, hda, by simp [pathCost]⟩⟩
  | b :: l, a, hlt, hc => by
    obtain ⟨hab, hc'⟩ := List.isChain_cons_cons.1 hc
    obtain ⟨p, hp, hvis, hcost⟩ := walk_of_chain hP l b (fun v hv => hlt v (by simp [hv])) hc'
    obtain ⟨i, -, hi, da, hda, db, hdb, hle⟩ := hP b (hlt b (by simp)) a hab
    refine ⟨i :: p, ?_, ?_, fun da' hda' => ?_⟩
    · simp only [IsWalk, ends, hi, ite_true, List.getLast_cons_cons]
      exact hp
    · simp only [visits, List.map_cons] at hvis ⊢
      rw [target_eq hi, ← hvis]
    · rw [Option.mem_unique hda' hda]
      obtain ⟨dc, hdc, hle'⟩ := hcost db hdb
      rw [List.getLast_cons_cons]
      have hsum : st.net.pathCost (i :: p) = st.net.arrowCost i + st.net.pathCost p := by
        simp [pathCost]
      rw [hsum]
      exact ⟨dc, hdc, by linarith⟩

/-- A chain stays a chain under a relation that each of its steps implies. -/
theorem isChain_imp_of_mem {R S : ℕ → ℕ → Prop} :
    ∀ {l : List ℕ}, (∀ x y, y ∈ l → R x y → S x y) → l.IsChain R → l.IsChain S
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: l, h, hc => by
    obtain ⟨hab, hc'⟩ := List.isChain_cons_cons.1 hc
    exact List.isChain_cons_cons.2 ⟨h a b (by simp) hab,
      isChain_imp_of_mem (fun x y hy => h x y (by simp [hy])) hc'⟩

/-- **Arrows along a chain that fit some costs**: a list of vertices, each joined to the next by an
arrow whose cost, added to the cost `f` gives the first, is at most what `f` gives the next, and
below it when the first is `w`, gives a path along them whose cost, added to the first vertex's, is
at most the last vertex's, and below it when the path leaves `w`. -/
theorem walk_of_fits (f : ℕ → ℤ) (w : ℕ) :
    ∀ (l : List ℕ) (a : ℕ), (a :: l).IsChain (fun x y => ∃ j, N.g.arrows[j]? = some (x, y) ∧
      f x + N.arrowCost j ≤ f y ∧ (x = w → f x + N.arrowCost j < f y)) →
      ∃ p, N.IsWalk a p ((a :: l).getLast (by simp)) ∧ N.visits a p = a :: l ∧
        f a + N.pathCost p ≤ f ((a :: l).getLast (by simp)) ∧
          (w ∈ (a :: l).dropLast → f a + N.pathCost p < f ((a :: l).getLast (by simp)))
  | [], a, _ => ⟨[], isWalk_nil a, by simp [visits], by simp [pathCost], by simp⟩
  | b :: l, a, hc => by
    obtain ⟨⟨j, hj, hle, hlt⟩, hc'⟩ := List.isChain_cons_cons.1 hc
    obtain ⟨p, hp, hvis, hcost, hstrict⟩ := walk_of_fits f w l b hc'
    have hsum : N.pathCost (j :: p) = N.arrowCost j + N.pathCost p := by simp [pathCost]
    refine ⟨j :: p, ?_, ?_, ?_, fun hw => ?_⟩
    · simp only [IsWalk, ends, hj, ite_true, List.getLast_cons_cons]
      exact hp
    · simp only [visits, List.map_cons] at hvis ⊢
      rw [target_eq hj, ← hvis]
    · rw [List.getLast_cons_cons, hsum]; linarith
    · rw [List.getLast_cons_cons, hsum]
      rw [List.dropLast_cons_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · linarith [hlt rfl]
      · linarith [hstrict hw]

/-! ## Where the records lead -/

/-- Following the records back from a vertex of the graph stays among the vertices. -/
theorem iterate_stepBack_lt {st : State} (hN : st.net.WellFormed) (hP : PreviousArrowFits st)
    {x : ℕ} (hx : x < st.net.g.n) : ∀ t, (stepBack st.prev)^[t] x < st.net.g.n
  | 0 => hx
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    have ih := iterate_stepBack_lt hN hP hx t
    cases hu : st.prev ((stepBack st.prev)^[t] x) with
    | none => simpa [stepBack, hu] using ih
    | some u =>
      rw [stepBack_of_some _ hu]
      obtain ⟨i, -, hi, -⟩ := hP _ ih u hu
      exact (hN.1 _ (List.mem_of_getElem? hi)).1

/-- Following the records back from a vertex with a cost, while each records one, meets only
vertices with costs. -/
theorem cost_iterate_ne_none {st : State} (hP : PreviousArrowFits st) (hN : st.net.WellFormed)
    {x : ℕ} (hx : x < st.net.g.n) (hcx : st.cost x ≠ none) :
    ∀ t, (∀ t' < t, st.prev ((stepBack st.prev)^[t'] x) ≠ none) →
      st.cost ((stepBack st.prev)^[t] x) ≠ none
  | 0, _ => hcx
  | t + 1, h => by
    rw [Function.iterate_succ_apply']
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 (h t (by omega))
    rw [stepBack_of_some _ hu]
    obtain ⟨i, -, -, du, hdu, -⟩ := hP _ (iterate_stepBack_lt hN hP hx t) u hu
    rw [Option.mem_def] at hdu
    simp [hdu]

/-- **Records that run out lead back to the start along a path**: when following the records back
from `x` meets a vertex that records none, the vertices met, turned around, are a path from the
start to `x` that the records lead back along, costing at most `x`'s cost. -/
theorem path_of_none {st : State} (hN : N.WellFormed) (hn : st.net = N) (hsrc : st.source = s)
    (hV : Valid st ∧ WellFormed st) {x : ℕ} (hx : x < N.g.n) (hcx : st.cost x ≠ none)
    (h : ∃ t, st.prev ((stepBack st.prev)^[t] x) = none) :
    ∃ p, N.IsPath s p x ∧ LeadsBack st.prev s (N.visits s p) ∧
      ∀ dx ∈ st.cost x, N.pathCost p ≤ dx := by
  classical
  subst hn hsrc
  set N := st.net with hNdef
  set s := st.source with hsdef
  obtain ⟨-, -, hP, -, hS⟩ := hV
  set g := stepBack st.prev
  have hmin : ∀ t < Nat.find h, st.prev (g^[t] x) ≠ none := fun t ht => Nat.find_min h ht
  have hnone : st.prev (g^[Nat.find h] x) = none := Nat.find_spec h
  set t₀ := Nat.find h
  have hlt := iterate_stepBack_lt hN hP hx t₀
  have hcost := cost_iterate_ne_none hP hN hx hcx t₀ hmin
  have hs := hS _ hlt hnone
  obtain ⟨hhs, hs⟩ : g^[t₀] x = s ∧ st.cost s = some 0 := by
    split_ifs at hs with he
    · exact ⟨he, (show g^[t₀] x = s from he) ▸ hs⟩
    · exact absurd hs hcost
  have hchain := isChain_trail st.prev hmin
  have hnd : (trail st.prev x t₀).Nodup := by
    refine nodup_trail st.prev fun i j hij hj heq => ?_
    have := iterate_shift heq (t₀ - j)
    rw [show t₀ - j + j = t₀ by omega] at this
    exact hmin _ (by omega) (this ▸ hnone)
  have hL : trail st.prev x t₀ = s :: (trail st.prev x t₀).tail := by
    have := head_trail st.prev x t₀
    rw [hhs] at this
    exact (List.eq_cons_of_mem_head? this)
  have hall : ∀ v ∈ s :: (trail st.prev x t₀).tail, v < N.g.n := by
    rw [← hL]
    intro v hv
    obtain ⟨t, -, rfl⟩ := (mem_trail st.prev).1 hv
    exact iterate_stepBack_lt hN hP hx t
  rw [hL] at hchain hnd
  obtain ⟨p, hp, hvis, hc⟩ := walk_of_chain hP _ s hall hchain
  have hlast : (s :: (trail st.prev x t₀).tail).getLast (by simp) = x := by
    simp_rw [← hL]; exact getLast_trail st.prev x t₀
  rw [hlast] at hp hc
  refine ⟨p, ⟨hp, hvis ▸ hnd⟩, ⟨?_, hvis ▸ hchain⟩, fun dx hdx => ?_⟩
  · rw [← hhs]; exact hnone
  · obtain ⟨db, hdb, hle⟩ := hc 0 hs
    rw [Option.mem_unique hdx hdb]
    linarith

/-- Following the records from `y` until it comes back, when `d₀` steps first bring it back. -/
theorem collect_eq (prev : ℕ → Option ℕ) {y d₀ : ℕ}
    (hback : (stepBack prev)^[d₀] y = y)
    (hfirst : ∀ d, 0 < d → d < d₀ → (stepBack prev)^[d] y ≠ y) :
    ∀ f a, a < d₀ → d₀ - a ≤ f →
      ((stepBack prev)^[a] y :: collect prev y f ((stepBack prev)^[a] y)).reverse =
        trail prev ((stepBack prev)^[a] y) (d₀ - a)
  | 0, a, ha, hf => by omega
  | f + 1, a, ha, hf => by
    have hga : stepBack prev ((stepBack prev)^[a] y) = (stepBack prev)^[a + 1] y :=
      (Function.iterate_succ_apply' _ _ _).symm
    simp only [collect]
    rw [hga]
    split_ifs with hy
    · have : a + 1 = d₀ := by
        by_contra hne
        exact hfirst (a + 1) (by omega) (by omega) hy
      rw [show d₀ - a = 0 + 1 by omega, trail_succ', trail, hga, hy]
      simp
    · have ih := collect_eq prev hback hfirst f (a + 1)
        (by by_contra; exact hy (by rw [show a + 1 = d₀ by omega]; exact hback)) (by omega)
      rw [List.reverse_cons, ih, show d₀ - a = d₀ - (a + 1) + 1 by
        by_contra; exact hy (by rw [show a + 1 = d₀ by omega]; exact hback),
        trail_succ', hga]

/-- **Records that never run out end on a negative cycle that the start reaches**: following them
back `n` steps from `x` reaches a vertex on a cycle of records, and the cycle `cycleFrom`
collects is below zero. -/
theorem cycle_of_defined {st : State} (hN : N.WellFormed) (hn : st.net = N)
    (hsrc : st.source = s) (hV : Valid st ∧ WellFormed st) {x : ℕ} (hx : x < N.g.n)
    (hcx : st.cost x ≠ none) (h : ∀ t, st.prev ((stepBack st.prev)^[t] x) ≠ none) :
    CycleBelowZero N s (cycleFrom st.prev N.g.n x) := by
  classical
  subst hn hsrc
  set N := st.net with hNdef
  set s := st.source with hsdef
  obtain ⟨hC, -, hP, hR, -⟩ := hV
  set g := stepBack st.prev
  set n := N.g.n
  have hlt := iterate_stepBack_lt hN hP hx
  -- two of the first `n + 1` vertices met are the same
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (n + 1)) (t := Finset.range n) (f := fun t => g^[t] x)
    (by simp) (fun t _ => by simpa using hlt t)
  simp only [Finset.mem_range] at hi hj
  have hper : ∃ d, 0 < d ∧ d ≤ n ∧ g^[d] (g^[n] x) = g^[n] x := by
    rcases Nat.lt_or_gt_of_ne hij with hij | hij
    · refine ⟨j - i, by omega, by omega, ?_⟩
      have := iterate_shift heq (n - i)
      rw [show n - i + i = n by omega, show n - i + j = (j - i) + n by omega,
        Function.iterate_add_apply] at this
      exact this.symm
    · refine ⟨i - j, by omega, by omega, ?_⟩
      have := iterate_shift heq.symm (n - j)
      rw [show n - j + j = n by omega, show n - j + i = (i - j) + n by omega,
        Function.iterate_add_apply] at this
      exact this.symm
  set y := g^[n] x
  have hex : ∃ d, 0 < d ∧ g^[d] y = y := by
    obtain ⟨d, h0, -, hd⟩ := hper; exact ⟨d, h0, hd⟩
  set d₀ := Nat.find hex
  obtain ⟨hd₀, hback⟩ : 0 < d₀ ∧ g^[d₀] y = y := Nat.find_spec hex
  have hfirst : ∀ d, 0 < d → d < d₀ → g^[d] y ≠ y := fun d h0 hd hy =>
    Nat.find_min hex hd ⟨h0, hy⟩
  have hd₀n : d₀ ≤ n := by
    obtain ⟨d, h0, hdn, hd⟩ := hper; exact le_trans (Nat.find_min' hex ⟨h0, hd⟩) hdn
  have hyit : ∀ t, g^[t] y = g^[t + n] x := fun t => (Function.iterate_add_apply _ _ _ _).symm
  have hdef : ∀ t, st.prev (g^[t] y) ≠ none := fun t => by rw [hyit]; exact h _
  have hcost : ∀ t, st.cost (g^[t] y) ≠ none := fun t => by
    rw [hyit]; exact cost_iterate_ne_none hP hN hx hcx _ fun t' _ => h t'
  -- the answer is the cycle of records through `y`
  have hans : cycleFrom st.prev n x = trail st.prev y d₀ := by
    have := collect_eq st.prev hback hfirst n 0 hd₀ (by omega)
    simpa [cycleFrom] using this
  obtain ⟨d', hd'⟩ : ∃ d', d₀ = d' + 1 := ⟨d₀ - 1, by omega⟩
  have hall : ∀ v ∈ trail st.prev y d₀, v < n := by
    intro v hv
    obtain ⟨t, -, rfl⟩ := (mem_trail st.prev).1 hv
    rw [hyit]; exact hlt _
  have hnd : (trail st.prev y d₀).dropLast.Nodup := by
    rw [hd', trail_succ', List.dropLast_concat]
    refine nodup_trail st.prev fun a b hab hb he => ?_
    rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply] at he
    have := iterate_shift he (d₀ - (b + 1))
    rw [show d₀ - (b + 1) + (b + 1) = d₀ by omega, hback] at this
    exact hfirst _ (by omega) (by omega) this
  have hhead : (trail st.prev y d₀).head? = some y := by
    rw [head_trail, hback]
  have hclose : RecordsClose N st.prev (trail st.prev y d₀) := by
    refine ⟨hall, isChain_trail st.prev fun t _ => hdef t, ?_, ?_, hnd⟩
    · rw [hd', trail]; cases d' <;> simp [trail]
    · rw [hhead, List.getLast?_eq_getLast_of_ne_nil (trail_ne_nil st.prev y d₀),
        getLast_trail]
  obtain ⟨v, p, hp, hvis, hneg⟩ := hR _ hclose
  obtain rfl : v = y := by
    have := congrArg List.head? hvis
    rw [hhead] at this
    simpa [visits] using this
  refine ⟨y, p, ⟨?_, hp, ?_⟩, by rw [hvis, hans], hneg, ?_⟩
  · rintro rfl
    have := congrArg List.length hvis
    rw [hd'] at this
    simp only [visits, List.map_nil, List.length_cons, List.length_nil, trail] at this
    exact trail_ne_nil st.prev y d' (List.length_eq_zero_iff.1 (by omega))
  · rw [hvis]; exact hnd
  · obtain ⟨dy, hdy⟩ := Option.ne_none_iff_exists'.1 (hcost 0)
    obtain ⟨q, hq, -⟩ := (hC y (hall y (by rw [← hvis]; simp [visits]))).1 dy hdy
    exact hq.reaches

end BellmanFord

end AlgoDesign.Paths
