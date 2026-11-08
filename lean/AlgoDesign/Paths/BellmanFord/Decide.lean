/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.BellmanFord.Spec
public import AlgoDesign.Paths.Dijkstra.Basic
public import AlgoDesign.Graphs.Scc.Reach

/-! # Cheapest paths with negative arrows: deciding the definitions

The pieces of `WellFormed`, `Valid` with `WellFormed`, and `CycleBelowZero` decide on a concrete
network, so `decide` checks small cases and a separate Lean–Rust check evaluates them. A question
about every path of at most `k` arrows decides through `arrowLists`, every list of at most `k`
arrow ids, or through `walkCosts`, the costs of those paths to each vertex.

The box's invariant speaks of some path, of any length; alone it does not decide that way. With
`PathWithinTries`, which bounds that path by the arrows tried, it does: `Valid` and `WellFormed`
decide together through `valid_iff`. -/

@[expose] public section

namespace AlgoDesign.Paths

namespace Network

variable {N : Network}

theorem ends_append (u : ℕ) (p q : List ℕ) :
    N.ends u (p ++ q) = (N.ends u p).bind (N.ends · q) := by
  induction p generalizing u with
  | nil => simp [ends]
  | cons j p ih =>
    simp only [List.cons_append, ends]
    cases h : N.g.arrows[j]? with
    | none => simp
    | some a =>
      obtain ⟨a, b⟩ := a
      by_cases hab : a = u
      · simp [hab, ih]
      · simp [hab]

/-- An arrow id of the network is the arrow from its `source` to its `target`. -/
theorem getElem?_arrows {i : ℕ} (hi : i < N.g.arrows.length) :
    N.g.arrows[i]? = some (N.source i, N.target i) := by
  simp [source, target, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

end Network

namespace BellmanFord

open Network

/-- Every list of at most `k` arrow ids. -/
def arrowLists (N : Network) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => [] :: (List.range N.g.arrows.length).flatMap fun i => (arrowLists N k).map (i :: ·)

variable {N : Network}

theorem mem_arrowLists {p : List ℕ} :
    ∀ {k}, p ∈ arrowLists N k ↔ p.length ≤ k ∧ ∀ i ∈ p, i < N.g.arrows.length
  | 0 => by cases p <;> simp [arrowLists]
  | k + 1 => by
    cases p with
    | nil => simp [arrowLists]
    | cons i p =>
      simp only [arrowLists, List.mem_cons, reduceCtorEq, List.mem_flatMap, List.mem_range,
        List.mem_map, List.cons.injEq, false_or, List.length_cons, add_le_add_iff_right,
        forall_eq_or_imp]
      constructor
      · rintro ⟨j, hj, q, hq, rfl, rfl⟩
        exact ⟨(mem_arrowLists.1 hq).1, hj, (mem_arrowLists.1 hq).2⟩
      · rintro ⟨hl, hi, hp⟩
        exact ⟨i, hi, p, mem_arrowLists.2 ⟨hl, hp⟩, rfl, rfl⟩

theorem exists_walk_iff {u v k : ℕ} {P : List ℕ → Prop} :
    (∃ p, N.IsWalk u p v ∧ p.length ≤ k ∧ P p) ↔ ∃ p ∈ arrowLists N k, N.IsWalk u p v ∧ P p :=
  ⟨fun ⟨p, hp, hl, h⟩ => ⟨p, mem_arrowLists.2 ⟨hl, lt_of_ends hp⟩, hp, h⟩,
    fun ⟨p, hm, hp, h⟩ => ⟨p, hp, (mem_arrowLists.1 hm).1, h⟩⟩

theorem forall_walk_iff {u v k : ℕ} {P : List ℕ → Prop} :
    (∀ p, N.IsWalk u p v → p.length ≤ k → P p) ↔ ∀ p ∈ arrowLists N k, N.IsWalk u p v → P p :=
  ⟨fun h p hm hp => h p hp (mem_arrowLists.1 hm).1,
    fun h p hp hl => h p (mem_arrowLists.2 ⟨hl, lt_of_ends hp⟩) hp⟩

/-! ## The costs of the paths of at most `k` arrows -/

variable (N) in
/-- How many vertices the paths from `s` can reach: past `s` and past every arrow's ends. -/
def tableSize (s : ℕ) : ℕ := (N.g.arrows.map fun e => max e.1 e.2 + 1).foldr max (s + 1)

theorem le_foldr_max (l : List ℕ) (b : ℕ) : b ≤ l.foldr max b ∧ ∀ x ∈ l, x ≤ l.foldr max b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    exact ⟨le_max_of_le_right ih.1, le_max_left _ _,
      fun x hx => le_max_of_le_right (ih.2 x hx)⟩

theorem lt_tableSize_start (s : ℕ) : s < tableSize N s := (le_foldr_max _ _).1

theorem lt_tableSize_of_mem {s a b : ℕ} (h : (a, b) ∈ N.g.arrows) :
    a < tableSize N s ∧ b < tableSize N s := by
  have := (le_foldr_max (N.g.arrows.map fun e => max e.1 e.2 + 1) (s + 1)).2 _
    (List.mem_map.2 ⟨_, h, rfl⟩)
  simp only at this
  exact ⟨by unfold tableSize; omega, by unfold tableSize; omega⟩

variable (N) in
/-- The costs of the paths from `s` of at most `k` arrows, entry `v` for each vertex `v`. -/
def walkCosts (s : ℕ) : ℕ → List (List ℤ)
  | 0 => (List.range (tableSize N s)).map fun v => if v = s then [0] else []
  | k + 1 =>
    let t := walkCosts s k
    (List.range (tableSize N s)).map fun v => (t.getD v [] ++
      (List.range N.g.arrows.length).flatMap fun i =>
        if N.target i = v then (t.getD (N.source i) []).map (· + N.arrowCost i) else []).dedup

theorem getD_table {α : Type} (n v : ℕ) (f : ℕ → List α) :
    ((List.range n).map f).getD v [] = if v < n then f v else [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs <;> simp_all

/-- **`walkCosts` lists the costs of the paths of at most `k` arrows.** -/
theorem mem_walkCosts {s : ℕ} :
    ∀ {k v : ℕ} {d : ℤ}, d ∈ (walkCosts N s k).getD v [] ↔
      ∃ p, N.IsWalk s p v ∧ p.length ≤ k ∧ N.pathCost p = d
  | 0, v, d => by
    simp only [walkCosts, getD_table, nonpos_iff_eq_zero, List.length_eq_zero_iff]
    constructor
    · intro h
      split_ifs at h with hv hs
      · subst hs
        exact ⟨[], rfl, rfl, by simpa [pathCost, eq_comm] using h⟩
      · simp at h
      · simp at h
    · rintro ⟨p, hp, rfl, rfl⟩
      obtain rfl : v = s := by simpa [IsWalk, ends, eq_comm] using hp
      simp [lt_tableSize_start, pathCost]
  | k + 1, v, d => by
    simp only [walkCosts, getD_table]
    constructor
    · intro h
      split_ifs at h with hv
      · rcases List.mem_append.1 (List.mem_dedup.1 h) with h | h
        · obtain ⟨p, hp, hl, hc⟩ := mem_walkCosts.1 h
          exact ⟨p, hp, by omega, hc⟩
        · obtain ⟨i, hi, h⟩ := List.mem_flatMap.1 h
          rw [List.mem_range] at hi
          split_ifs at h with ht
          · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 h
            obtain ⟨q, hq, hl, hc⟩ := mem_walkCosts.1 hd'
            refine ⟨q ++ [i], ends_append_singleton.2 ⟨_, hq, ?_⟩, by simp; omega, ?_⟩
            · rw [getElem?_arrows hi, ht]
            · rw [← hc]; simp [pathCost]
          · simp at h
      · simp at h
    · rintro ⟨p, hp, hl, rfl⟩
      rcases List.eq_nil_or_concat' p with rfl | ⟨q, i, rfl⟩
      · obtain rfl : v = s := by simpa [IsWalk, ends, eq_comm] using hp
        simp only [lt_tableSize_start, ↓reduceIte, List.mem_dedup, List.mem_append]
        exact Or.inl (mem_walkCosts.2 ⟨[], hp, by simp, rfl⟩)
      · obtain ⟨x, hq, hi⟩ := ends_append_singleton.1 hp
        have hil := (List.getElem?_eq_some_iff.1 hi).1
        have hv := (lt_tableSize_of_mem (s := s) (List.mem_of_getElem? hi)).2
        rw [getElem?_arrows hil, Option.some.injEq, Prod.mk.injEq] at hi
        simp only [hv, ↓reduceIte, List.mem_dedup, List.mem_append]
        refine Or.inr (List.mem_flatMap.2 ⟨i, List.mem_range.2 hil, ?_⟩)
        simp only [hi.2, ↓reduceIte, hi.1]
        refine List.mem_map.2 ⟨N.pathCost q, mem_walkCosts.2 ⟨q, hq, ?_, rfl⟩, ?_⟩
        · simp at hl; omega
        · simp [pathCost]

/-! ## The box's invariant, over the paths of at most `k` arrows -/

/-- No path from `s` has exactly `k` arrows. -/
def NoWalkOfLength (N : Network) (s k : ℕ) : Prop :=
  ∀ p ∈ arrowLists N k, p.length = k → N.ends s p = none

/-- The box's invariant, its second half: no cost above a path of at most the rounds arrows. -/
def CheapestWithinRounds (N : Network) (s : ℕ) (st : State) : Prop :=
  ∀ v < N.g.n, ∀ d ∈ (walkCosts N s st.rounds).getD v [], AtMost (st.cost v) d

/-- Every cost is the cost of a path of at most `k` arrows. -/
def WalkCostsWithin (N : Network) (s : ℕ) (st : State) (k : ℕ) : Prop :=
  ∀ v < N.g.n, ∀ d ∈ st.cost v, d ∈ (walkCosts N s k).getD v []

instance (N : Network) (s k : ℕ) : Decidable (NoWalkOfLength N s k) := by
  unfold NoWalkOfLength; infer_instance

instance (N : Network) (s : ℕ) (st : State) : Decidable (CheapestWithinRounds N s st) := by
  unfold CheapestWithinRounds; infer_instance

instance (N : Network) (s : ℕ) (st : State) (k : ℕ) : Decidable (WalkCostsWithin N s st k) := by
  unfold WalkCostsWithin; infer_instance

/-- Where no path from `s` has `k` arrows, every path from `s` has fewer: its first `k` arrows
would be one. -/
theorem length_lt_of_noWalk {s k : ℕ} (h : NoWalkOfLength N s k) {p : List ℕ} {v : ℕ}
    (hp : N.IsWalk s p v) : p.length < k := by
  by_contra hk
  push Not at hk
  have hsplit : N.ends s p = (N.ends s (p.take k)).bind (N.ends · (p.drop k)) := by
    rw [← Network.ends_append, List.take_append_drop]
  obtain ⟨x, hx⟩ : ∃ x, N.ends s (p.take k) = some x := by
    unfold Network.IsWalk at hp
    rw [hsplit] at hp
    cases h' : N.ends s (p.take k) with
    | none => simp [h'] at hp
    | some x => exact ⟨x, rfl⟩
  have hmem : p.take k ∈ arrowLists N k :=
    mem_arrowLists.2 ⟨by simp, Network.lt_of_ends hx⟩
  have hnone := h _ hmem (by simp [hk])
  rw [hnone] at hx
  exact absurd hx (by simp)

theorem cheapestWithinRounds_iff {s : ℕ} {st : State} :
    CheapestWithinRounds N s st ↔ ∀ v < N.g.n, ∀ p, N.IsWalk s p v → p.length ≤ st.rounds →
      AtMost (st.cost v) (N.pathCost p) := by
  refine forall₂_congr fun v hv => ⟨fun h p hp hl => h _ (mem_walkCosts.2 ⟨p, hp, hl, rfl⟩),
    fun h d hd => ?_⟩
  obtain ⟨p, hp, hl, rfl⟩ := mem_walkCosts.1 hd
  exact h p hp hl

theorem pathWithinTries_iff {st : State} :
    PathWithinTries st ↔ WalkCostsWithin st.net st.source st st.tried :=
  forall₂_congr fun _ _ => forall₂_congr fun _ _ => mem_walkCosts.symm

instance decidablePathWithinTries (st : State) : Decidable (PathWithinTries st) :=
  decidable_of_iff' _ pathWithinTries_iff

/-- **Costs found among the paths of at most `k` arrows keep the box's invariant**, with its second
half. -/
theorem costIsWalkAtMostCheapest_of_within {st : State} {k : ℕ}
    (h₁ : WalkCostsWithin st.net st.source st k) (h₂ : CheapestWithinRounds st.net st.source st) :
    CostIsWalkAtMostCheapest st := by
  refine fun v hv => ⟨fun d hd => ?_, cheapestWithinRounds_iff.1 h₂ v hv⟩
  obtain ⟨p, hp, -, hc⟩ := mem_walkCosts.1 (h₁ v hv d hd)
  exact ⟨p, hp, hc⟩

/-! ## The cycles the previous vertices close -/

/-- The vertices met following the records back `k` steps from `x`, the farthest first, `x` last.
-/
def trail (prev : ℕ → Option ℕ) (x : ℕ) : ℕ → List ℕ
  | 0 => [x]
  | k + 1 => (stepBack prev)^[k + 1] x :: trail prev x k

section Trail

variable (prev : ℕ → Option ℕ)

theorem stepBack_of_some {v u : ℕ} (h : prev v = some u) : stepBack prev v = u := by
  simp [stepBack, h]

theorem trail_succ' (x : ℕ) :
    ∀ k, trail prev x (k + 1) = trail prev (stepBack prev x) k ++ [x]
  | 0 => by simp [trail]
  | k + 1 => by
    rw [trail, trail_succ' x k, trail, Function.iterate_succ_apply]
    rfl

/-- A list of vertices, each the previous vertex of the one after it, is the trail back from its
last vertex. -/
theorem eq_trail_of_isChain :
    ∀ (l : List ℕ) (x : ℕ), (l ++ [x]).IsChain (fun a b => prev b = some a) →
      l ++ [x] = trail prev x l.length := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro x _; rfl
  | append_singleton l y ih =>
    intro x h
    rw [List.isChain_append] at h
    obtain ⟨h₁, -, h₃⟩ := h
    have hy : prev x = some y := h₃ y (by simp) x (by simp)
    rw [List.length_append, List.length_singleton, trail_succ', stepBack_of_some prev hy,
      ← ih y h₁]

end Trail

/-- The lists of arrows along `c`, one arrow from each vertex to the one after it. -/
def alongLists (N : Network) : List ℕ → List (List ℕ)
  | [] => []
  | [_] => [[]]
  | a :: b :: l => ((List.range N.g.arrows.length).filter fun i =>
      N.g.arrows[i]? = some (a, b)).flatMap fun i => (alongLists N (b :: l)).map (i :: ·)

theorem mem_alongLists {p : List ℕ} :
    ∀ {a : ℕ} {l : List ℕ}, p ∈ alongLists N (a :: l) ↔
      N.ends a p = some ((a :: l).getLast (by simp)) ∧ N.visits a p = a :: l
  | a, [] => by
    cases p with
    | nil => simp [alongLists, ends, visits]
    | cons i p => simp [alongLists, visits]
  | a, b :: l => by
    cases p with
    | nil => simp [alongLists, visits]
    | cons i p =>
      simp only [alongLists, List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
        List.mem_map, List.cons.injEq, List.getLast_cons_cons]
      constructor
      · rintro ⟨j, ⟨-, hj⟩, q, hq, rfl, rfl⟩
        obtain ⟨he, hv⟩ := mem_alongLists.1 hq
        refine ⟨by simp [ends, hj, he], ?_⟩
        simp only [visits, List.map_cons, target_eq hj] at hv ⊢
        rw [hv]
      · rintro ⟨he, hv⟩
        simp only [ends] at he
        split at he
        · rename_i x y hi
          split_ifs at he with hx
          subst hx
          simp only [visits, List.map_cons, List.cons.injEq, target_eq hi] at hv
          obtain ⟨-, rfl, hv⟩ := hv
          refine ⟨i, ⟨(List.getElem?_eq_some_iff.1 hi).1, hi⟩, p, mem_alongLists.2 ⟨he, ?_⟩,
            rfl, rfl⟩
          simp [visits, hv]
        · exact absurd he (by simp)

instance (N : Network) (prev : ℕ → Option ℕ) (c : List ℕ) : Decidable (RecordsClose N prev c) := by
  unfold RecordsClose; infer_instance

/-- The cycles the previous vertices close are the trails back from a vertex that come back to it,
of at most as many steps as there are vertices. -/
theorem recordedCyclesBelowZero_iff {st : State} :
    RecordedCyclesBelowZero st ↔ ∀ v < st.net.g.n, ∀ k < st.net.g.n + 1,
      RecordsClose st.net st.prev (trail st.prev v k) →
        ∃ p ∈ alongLists st.net (trail st.prev v k), st.net.pathCost p < 0 := by
  set N := st.net
  constructor
  · intro h v _ k _ hc
    obtain ⟨w, p, hw, hvis, hneg⟩ := h _ hc
    refine ⟨p, ?_, hneg⟩
    rw [← hvis]
    refine mem_alongLists.2 ⟨?_, rfl⟩
    have hl := hc.2.2.2.1
    rw [← hvis] at hl
    simp only [visits, List.head?_cons, List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _),
      Option.some.injEq] at hl
    rw [← hl]
    exact hw
  · intro h c hc
    obtain ⟨hlt, hch, hlen, hhd, hnd⟩ := hc
    rcases List.eq_nil_or_concat' c with rfl | ⟨l, x, rfl⟩
    · simp at hlen
    have he := eq_trail_of_isChain st.prev l x hch
    have hx : x < N.g.n := hlt x (by simp)
    have hl : l.length < N.g.n + 1 := by
      have hnd' : l.Nodup := by simpa using hnd
      have := hnd'.length_le_of_subset (l₂ := List.range N.g.n)
        (fun y hy => List.mem_range.2 (hlt y (by simp [hy])))
      simp at this; omega
    have hc' : RecordsClose N st.prev (trail st.prev x l.length) := by
      rw [← he]; exact ⟨hlt, hch, hlen, hhd, hnd⟩
    obtain ⟨p, hp, hneg⟩ := h x hx _ hl hc'
    rw [← he] at hp
    obtain ⟨a, l', hal⟩ := List.exists_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil l
      (List.cons_ne_nil x []))
    rw [hal] at hp hhd
    obtain ⟨hpe, hpv⟩ := mem_alongLists.1 hp
    refine ⟨a, p, ?_, by rw [hpv, hal], hneg⟩
    simp only [List.head?_cons, List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _),
      Option.some.injEq] at hhd
    rw [← hhd] at hpe
    exact hpe

instance decidablePreviousArrowFits (st : State) : Decidable (PreviousArrowFits st) := by
  unfold PreviousArrowFits; infer_instance

instance decidableRecordedCyclesBelowZero (st : State) :
    Decidable (RecordedCyclesBelowZero st) :=
  decidable_of_iff' _ recordedCyclesBelowZero_iff

instance decidableNoPreviousKeepsStart (st : State) : Decidable (NoPreviousKeepsStart st) := by
  unfold NoPreviousKeepsStart; infer_instance

instance decidableWellFormed (st : State) : Decidable (WellFormed st) := by
  unfold WellFormed; infer_instance

/-- `Valid` and `WellFormed`, with the box's path of any length left to `PathWithinTries`, which
bounds it. -/
theorem valid_iff {st : State} :
    Valid st ∧ WellFormed st ↔ CheapestWithinRounds st.net st.source st ∧ PathWithinTries st ∧
      PreviousArrowFits st ∧ RecordedCyclesBelowZero st ∧ NoPreviousKeepsStart st := by
  constructor
  · rintro ⟨hC, hW, h⟩
    exact ⟨cheapestWithinRounds_iff.2 fun v hv => (hC v hv).2, hW, h⟩
  · rintro ⟨hC, hW, h⟩
    refine ⟨fun v hv => ⟨fun d hd => ?_, cheapestWithinRounds_iff.1 hC v hv⟩, hW, h⟩
    obtain ⟨p, hp, -, hc⟩ := hW v hv d hd
    exact ⟨p, hp, hc⟩

instance decidableValidWellFormed (st : State) : Decidable (Valid st ∧ WellFormed st) :=
  decidable_of_iff' _ valid_iff

/-- A negative cycle is among the lists of at most as many arrow ids as it has vertices. -/
theorem cycleBelowZero_iff {s : ℕ} {c : List ℕ} :
    CycleBelowZero N s c ↔ ∃ v ∈ c.head?, ∃ p ∈ arrowLists N c.length,
      N.IsCycle v p ∧ N.visits v p = c ∧ N.pathCost p < 0 ∧ N.g.Reaches s v := by
  constructor
  · rintro ⟨v, p, hp, rfl, hneg, hr⟩
    refine ⟨v, by simp [visits], p, mem_arrowLists.2 ⟨by simp [visits], lt_of_ends hp.2.1⟩,
      hp, rfl, hneg, hr⟩
  · rintro ⟨v, -, p, -, h⟩
    exact ⟨v, p, h⟩

instance decidableCycleBelowZero (N : Network) (s : ℕ) (c : List ℕ) :
    Decidable (CycleBelowZero N s c) :=
  decidable_of_iff' _ cycleBelowZero_iff

end BellmanFord

end AlgoDesign.Paths
