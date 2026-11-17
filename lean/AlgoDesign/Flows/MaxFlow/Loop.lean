/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Spec
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Max flow: the loop around a path rule

Source: the Flow chapter, "One loop, one open choice"; Ford and Fulkerson, "Maximal flow through a
network" (1956).

The loop starts from the zero flow, asks the path rule for one round at a time, applies the paths
the round added, and stops when a round adds nothing. The answer's cut is the set of vertices the
remaining capacity reaches from the source. `PathRule.contract` proves that every rule keeping
`PathRule.Promise` meets the max-flow contract; the size bound is the rule's own.
-/

@[expose] public section

namespace AlgoDesign.Flows

/-- **The total capacity**: every round adds at least one unit, and no flow carries more than this,
so it bounds the number of rounds. -/
def totalCapacity (N : Network) : ℕ := (N.ids.map N.capOf).sum

/-- At most `k` rounds from memory `m` and flow `f`: the paths each round added, and the flow at the
end. A round that adds nothing ends the loop. -/
def PathRule.runRounds (r : PathRule) (N : Network) :
    ℕ → r.Memory → Flow → List (List Augmentation) × Flow
  | 0, _, f => ([], f)
  | k + 1, m, f =>
    match r.round N m f with
    | (_, []) => ([], f)
    | (m', xs) =>
      let rest := r.runRounds N k m' (applyAll f xs)
      (xs :: rest.1, rest.2)

/-- The run of the loop on `N`: enough rounds for any rule that adds at least one unit per round. -/
def PathRule.run (r : PathRule) (N : Network) : List (List Augmentation) × Flow :=
  r.runRounds N (totalCapacity N + 1) (r.start N) (Flow.zero N)

/-- One step of the search through the remaining capacity: add every vertex an arrow with room
leads to from a vertex already in `S`. -/
def reachStep (N : Network) (f : Flow) (S : List ℕ) : List ℕ :=
  S ++ (N.ids.flatMap fun i =>
    (if N.tail i ∈ S ∧ N.head i ∉ S ∧ 0 < (ResidualArrow.along i).residualCapacity N f then
      [N.head i] else []) ++
    (if N.head i ∈ S ∧ N.tail i ∉ S ∧ 0 < (ResidualArrow.back i).residualCapacity N f then
      [N.tail i] else []))

/-- **The vertices the remaining capacity reaches from the source**, after `n` steps of the
search, which is enough for `n` vertices. -/
def reached (N : Network) (f : Flow) : List ℕ :=
  (reachStep N f)^[N.g.n] [N.source]

/-- The answer of the loop: the flow it ends with, and the vertices the last search reached. -/
def PathRule.maxFlow (r : PathRule) (N : Network) : Answer :=
  ⟨(r.run N).2, reached N (r.run N).2⟩

/-! ## The one proof

### The rounds -/

theorem PathRule.runRounds_nil (r : PathRule) (N : Network) (k : ℕ) {m m' : r.Memory}
    {f : Flow} (h : r.round N m f = (m', [])) : r.runRounds N (k + 1) m f = ([], f) := by
  simp [PathRule.runRounds, h]

theorem PathRule.runRounds_cons (r : PathRule) (N : Network) (k : ℕ) {m m' : r.Memory}
    {f : Flow} {x : Augmentation} {xs : List Augmentation} (h : r.round N m f = (m', x :: xs)) :
    r.runRounds N (k + 1) m f =
      ((x :: xs) :: (r.runRounds N k m' (applyAll f (x :: xs))).1,
        (r.runRounds N k m' (applyAll f (x :: xs))).2) := by
  simp [PathRule.runRounds, h]

theorem PathRule.runRounds_walks (r : PathRule) (N : Network) :
    ∀ k m f, (r.runRounds N k m f).2 = (r.runRounds N k m f).1.foldl applyAll f
  | 0, _, _ => rfl
  | k + 1, m, f => by
    rcases h : r.round N m f with ⟨m', _ | ⟨x, xs⟩⟩
    · simp [r.runRounds_nil N k h]
    · simp [r.runRounds_cons N k h, r.runRounds_walks N k]

/-! ### Sums over the arrows -/

theorem sum_filter_range (m : ℕ) (p : ℕ → Bool) (g : ℕ → ℕ) :
    ((((List.range m).filter p).map g).sum : ℤ) =
      ∑ i ∈ Finset.range m, if p i then (g i : ℤ) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, Finset.sum_range_succ, ← ih]
    cases h : p m <;> simp [h]

theorem Flow.on_zero (N : Network) : (Flow.zero N).on = fun _ => 0 := by
  funext i
  simp only [Flow.on, Flow.zero, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> simp

/-- What leaves `v` less what enters it, as an integer. -/
def netOut (N : Network) (f : Flow) (v : ℕ) : ℤ := (outflow N f v : ℤ) - inflow N f v

theorem netOut_eq (N : Network) (f : Flow) (v : ℕ) :
    netOut N f v = ∑ i ∈ Finset.range N.g.arrows.length,
      (f.on i : ℤ) * ((if N.tail i = v then 1 else 0) - (if N.head i = v then 1 else 0)) := by
  rw [netOut, outflow, inflow, Network.ids, sum_filter_range, sum_filter_range,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp_all

/-! ### Sending along one path -/

theorem Flow.on_modify (f : Flow) (φ : ℕ → ℕ) {i : ℕ} (hi : i < f.length) (j : ℕ) :
    Flow.on (f.modify i φ) j = if j = i then φ (f.on i) else f.on j := by
  simp only [Flow.on, List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : j = i
  · subst h
    simp [List.getElem?_eq_getElem hi]
  · rw [ite_eq_right h]
    cases f[j]? <;> simp [Ne.symm h]

/-- Changing the amount on one arrow `i` by `d` changes every vertex's net outflow by `d` at the
arrow's tail and by `-d` at its head. -/
theorem netOut_bump {N : Network} {f g : Flow} {i : ℕ} (hi : i < N.g.arrows.length) (d : ℤ)
    (hg : ∀ j, (g.on j : ℤ) = f.on j + if j = i then d else 0) (v : ℕ) :
    netOut N g v = netOut N f v +
      d * ((if N.tail i = v then 1 else 0) - (if N.head i = v then 1 else 0)) := by
  simp only [netOut_eq, hg, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp [Finset.sum_ite_eq', hi]

theorem sendOne_on_ne (x : ℕ) {f : Flow} {a : ResidualArrow} (ha : a.id < f.length) {j : ℕ}
    (hj : j ≠ a.id) : (sendOne x f a).on j = f.on j := by
  cases a with
  | along i =>
    have hi : i < f.length := ha
    have hj : j ≠ i := hj
    simp [sendOne, Flow.on_modify _ _ hi, hj]
  | back i =>
    have hi : i < f.length := ha
    have hj : j ≠ i := hj
    simp [sendOne, Flow.on_modify _ _ hi, hj]

theorem netOut_sendOne {N : Network} {f : Flow} {x : ℕ} {a : ResidualArrow}
    (hm : f.length = N.g.arrows.length) (ha : a.id < N.g.arrows.length)
    (hx : x ≤ a.residualCapacity N f) (v : ℕ) :
    netOut N (sendOne x f a) v = netOut N f v +
      x * ((if a.tail N = v then 1 else 0) - (if a.head N = v then 1 else 0)) := by
  cases a with
  | along i =>
    have ha : i < N.g.arrows.length := ha
    rw [netOut_bump (f := f) ha x (fun j => ?_) v]
    · rfl
    simp only [sendOne, Flow.on_modify f _ (show i < f.length from hm ▸ ha)]
    split_ifs <;> simp_all
  | back i =>
    have ha : i < N.g.arrows.length := ha
    have hx : x ≤ f.on i := hx
    rw [netOut_bump (f := f) ha (-x) (fun j => ?_) v]
    · simp only [ResidualArrow.tail, ResidualArrow.head]
      by_cases h1 : N.tail i = v <;> by_cases h2 : N.head i = v <;> simp [h1, h2]
    simp only [sendOne, Flow.on_modify f _ (show i < f.length from hm ▸ ha)]
    split_ifs with hj
    · subst hj
      push_cast [hx]
      ring
    · simp

theorem withinCapacity_sendOne {N : Network} {f : Flow} {x : ℕ} {a : ResidualArrow}
    (hm : f.length = N.g.arrows.length) (ha : a.id < N.g.arrows.length)
    (hx : x ≤ a.residualCapacity N f) (hc : WithinCapacity ⟨N, f⟩) :
    WithinCapacity ⟨N, sendOne x f a⟩ := by
  intro j hj
  have hcj : f.on j ≤ N.capOf j := hc j hj
  cases a with
  | along i =>
    simp only [ResidualArrow.residualCapacity] at hx
    simp only [sendOne, Flow.on_modify f _ (show i < f.length from hm ▸ ha)]
    split_ifs with h
    · subst h
      omega
    · exact hcj
  | back i =>
    simp only [sendOne, Flow.on_modify f _ (show i < f.length from hm ▸ ha)]
    split_ifs with h
    · subst h
      omega
    · exact hcj

/-- Two residual arrows of the same arrow share its two ends. -/
theorem ResidualArrow.head_of_id_eq (N : Network) {a b : ResidualArrow} (h : b.id = a.id) :
    b.head N = a.tail N ∨ b.head N = a.head N := by
  cases a <;> cases b <;> simp_all [ResidualArrow.head, ResidualArrow.tail, ResidualArrow.id]

/-- Sending `x` along a path with no repeated vertex, whose every arrow has room for `x`, keeps
every capacity and changes net outflow only at the path's two ends. -/
theorem sendPath {N : Network} (x : ℕ) :
    ∀ (p : List ResidualArrow) (u w : ℕ) (g : Flow), ends N u p = some w →
      (visits N u p).Nodup → (∀ a ∈ p, x ≤ a.residualCapacity N g) → g.length = N.g.arrows.length →
      WithinCapacity ⟨N, g⟩ →
      (p.foldl (sendOne x) g).length = N.g.arrows.length ∧
        WithinCapacity ⟨N, p.foldl (sendOne x) g⟩ ∧
        ∀ v, netOut N (p.foldl (sendOne x) g) v =
          netOut N g v + x * ((if u = v then 1 else 0) - (if w = v then 1 else 0))
  | [], u, w, g, he, _, _, hm, hc => by
    simp only [ends, Option.some.injEq] at he
    subst he
    simp [hm, hc]
  | a :: p, u, w, g, he, hn, hr, hm, hc => by
    simp only [ends] at he
    split_ifs at he with ha
    obtain ⟨ha, hu⟩ := ha
    have hn' : (visits N (a.head N) p).Nodup := (List.nodup_cons.1 hn).2
    have hu' : u ∉ visits N (a.head N) p := (List.nodup_cons.1 hn).1
    have hmid : a.head N ∉ p.map (·.head N) := (List.nodup_cons.1 hn').1
    have hlen : (sendOne x g a).length = N.g.arrows.length := by
      cases a <;> simp [sendOne, hm]
    have hroom : ∀ b ∈ p, x ≤ b.residualCapacity N (sendOne x g a) := by
      intro b hb
      have hne : b.id ≠ a.id := by
        intro hid
        have hbh : b.head N ∈ p.map (·.head N) := List.mem_map_of_mem hb
        rcases ResidualArrow.head_of_id_eq N hid with e | e
        · exact hu' (by rw [← hu, ← e]; exact List.mem_cons_of_mem _ hbh)
        · exact hmid (e ▸ hbh)
      have := hr b (List.mem_cons_of_mem _ hb)
      cases b with
      | along i =>
        have hon := sendOne_on_ne x (f := g) (hm ▸ ha) (j := i) hne
        simp only [ResidualArrow.residualCapacity] at this ⊢
        rw [hon]
        exact this
      | back i =>
        have hon := sendOne_on_ne x (f := g) (hm ▸ ha) (j := i) hne
        simp only [ResidualArrow.residualCapacity] at this ⊢
        rw [hon]
        exact this
    have hx : x ≤ a.residualCapacity N g := hr a List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := sendPath x p (a.head N) w (sendOne x g a) he hn' hroom hlen
      (withinCapacity_sendOne hm ha hx hc)
    refine ⟨h1, h2, fun v => ?_⟩
    rw [List.foldl_cons, h3, netOut_sendOne hm ha hx, hu]
    ring

/-- Sending along one augmenting path, within its room, keeps a flow a flow and raises its amount
by what was sent. -/
theorem apply_isFlow {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {x : Augmentation}
    (hx : IsAugmentingPath N f x.path ∧ ∀ a ∈ x.path, x.amount ≤ a.residualCapacity N f) :
    IsFlow N (x.apply f) ∧ value N (x.apply f) = value N f + x.amount := by
  obtain ⟨⟨he, hn, -⟩, hr⟩ := hx
  obtain ⟨h1, h2, h3⟩ := sendPath x.amount x.path _ _ f he hn hr hf.2.2 hf.1
  refine ⟨⟨h2, fun v _ hs ht => ?_, h1⟩, ?_⟩
  · have e := h3 v
    have e0 : netOut N f v = 0 := by
      have := hf.2.1 v ‹_› hs ht
      simp [netOut, this]
    simp only [Augmentation.apply, netOut, ite_eq_right (Ne.symm hs), ite_eq_right (Ne.symm ht)]
      at e e0 ⊢
    omega
  · have e := h3 N.source
    rw [ite_eq_left rfl, ite_eq_right h.2.2.2.2.symm] at e
    simp only [value, Augmentation.apply]
    simp only [netOut] at e
    linarith

/-! ### A flow amount across a cut -/

theorem Network.endpoints_lt {N : Network} (h : N.WellFormed) {i : ℕ}
    (hi : i < N.g.arrows.length) : N.tail i < N.g.n ∧ N.head i < N.g.n := by
  have := h.1 N.g.arrows[i] (List.getElem_mem hi)
  simpa [Network.tail, Network.head, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    using this

/-- A flow amount is the sum, over the arrows, of what each carries out of `side` less what it
carries in, for any `side` with the source and without the sink. -/
theorem value_eq_cross {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {side : List ℕ} (hs : N.source ∈ side) (ht : N.sink ∉ side) :
    value N f = ∑ i ∈ Finset.range N.g.arrows.length, (f.on i : ℤ) *
      ((if N.tail i ∈ side then 1 else 0) - (if N.head i ∈ side then 1 else 0)) := by
  have h1 : value N f = ∑ v ∈ side.toFinset, netOut N f v := by
    rw [Finset.sum_eq_single_of_mem N.source (List.mem_toFinset.2 hs)]
    · rfl
    intro v hv hne
    by_cases hvn : v < N.g.n
    · have := hf.2.1 v hvn hne (fun e => ht (e ▸ List.mem_toFinset.1 hv))
      simp [netOut, this]
    · rw [netOut_eq]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := Network.endpoints_lt h (Finset.mem_range.1 hi)
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
  rw [h1]
  simp_rw [netOut_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq, List.mem_toFinset]

/-! ### The search through the remaining capacity -/

/-- The vertices one step of the search adds to `S`. -/
def reachNew (N : Network) (f : Flow) (S : List ℕ) : List ℕ :=
  N.ids.flatMap fun i =>
    (if N.tail i ∈ S ∧ N.head i ∉ S ∧ 0 < (ResidualArrow.along i).residualCapacity N f then
      [N.head i] else []) ++
    (if N.head i ∈ S ∧ N.tail i ∉ S ∧ 0 < (ResidualArrow.back i).residualCapacity N f then
      [N.tail i] else [])

theorem reachStep_eq (N : Network) (f : Flow) (S : List ℕ) :
    reachStep N f S = S ++ reachNew N f S := rfl

theorem mem_reachNew {N : Network} {f : Flow} {S : List ℕ} {v : ℕ} (hv : v ∈ reachNew N f S) :
    ∃ i < N.g.arrows.length,
      (N.tail i ∈ S ∧ N.head i ∉ S ∧ 0 < (ResidualArrow.along i).residualCapacity N f ∧
        v = N.head i) ∨
      (N.head i ∈ S ∧ N.tail i ∉ S ∧ 0 < (ResidualArrow.back i).residualCapacity N f ∧
        v = N.tail i) := by
  simp only [reachNew, List.mem_flatMap, Network.ids, List.mem_range, List.mem_append] at hv
  obtain ⟨i, hi, hv | hv⟩ := hv
  · split_ifs at hv with hc
    · exact ⟨i, hi, Or.inl ⟨hc.1, hc.2.1, hc.2.2, List.mem_singleton.1 hv⟩⟩
    · simp at hv
  · split_ifs at hv with hc
    · exact ⟨i, hi, Or.inr ⟨hc.1, hc.2.1, hc.2.2, List.mem_singleton.1 hv⟩⟩
    · simp at hv

theorem ends_append_one (N : Network) (a : ResidualArrow) :
    ∀ (p : List ResidualArrow) (u w : ℕ), ends N u p = some w → a.id < N.g.arrows.length →
      a.tail N = w → ends N u (p ++ [a]) = some (a.head N)
  | [], u, w, he, ha, ht => by
    simp only [ends, Option.some.injEq] at he
    subst he
    simp [ends, ha, ht]
  | b :: p, u, w, he, ha, ht => by
    simp only [ends, List.cons_append] at he ⊢
    by_cases hb : b.id < N.g.arrows.length ∧ b.tail N = u
    · rw [ite_eq_left hb] at he ⊢
      exact ends_append_one N a p _ w he ha ht
    · rw [ite_eq_right hb] at he
      cases he

theorem visits_append_one (N : Network) (u : ℕ) (p : List ResidualArrow) (a : ResidualArrow) :
    visits N u (p ++ [a]) = visits N u p ++ [a.head N] := by
  simp [visits]

/-- Every vertex the search reaches has a path from the source with room on every arrow, passing
no vertex twice and only through reached vertices. -/
theorem reached_paths (N : Network) (f : Flow) :
    ∀ k, ∀ v ∈ (reachStep N f)^[k] [N.source], ∃ p, ends N N.source p = some v ∧
      (visits N N.source p).Nodup ∧ (∀ a ∈ p, 0 < a.residualCapacity N f) ∧
      ∀ w ∈ visits N N.source p, w ∈ (reachStep N f)^[k] [N.source]
  | 0, v, hv => by
    simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hv
    subst hv
    exact ⟨[], by simp [ends], by simp [visits], by simp, by simp [visits]⟩
  | k + 1, v, hv0 => by
    rw [Function.iterate_succ_apply'] at hv0 ⊢
    have hsub : ∀ w ∈ (reachStep N f)^[k] [N.source],
        w ∈ reachStep N f ((reachStep N f)^[k] [N.source]) :=
      fun w hw => List.mem_append_left _ hw
    rcases List.mem_append.1 hv0 with hv | hv
    · obtain ⟨p, h1, h2, h3, h4⟩ := reached_paths N f k v hv
      exact ⟨p, h1, h2, h3, fun w hw => hsub w (h4 w hw)⟩
    obtain ⟨i, hi, ⟨ht, hh, hr, rfl⟩ | ⟨ht, hh, hr, rfl⟩⟩ := mem_reachNew hv
    · obtain ⟨p, h1, h2, h3, h4⟩ := reached_paths N f k _ ht
      refine ⟨p ++ [.along i], ends_append_one N (.along i) p _ _ h1 hi rfl, ?_, ?_, ?_⟩
      · rw [visits_append_one, List.nodup_append]
        refine ⟨h2, List.nodup_singleton _, ?_⟩
        simp only [List.mem_singleton]
        rintro a ha b rfl rfl
        exact hh (h4 _ ha)
      · intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · exact h3 a ha
        · rw [List.mem_singleton.1 ha]
          exact hr
      · intro w hw
        rw [visits_append_one] at hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hsub w (h4 w hw)
        · rw [List.mem_singleton.1 hw]
          exact hv0
    · obtain ⟨p, h1, h2, h3, h4⟩ := reached_paths N f k _ ht
      refine ⟨p ++ [.back i], ends_append_one N (.back i) p _ _ h1 hi rfl, ?_, ?_, ?_⟩
      · rw [visits_append_one, List.nodup_append]
        refine ⟨h2, List.nodup_singleton _, ?_⟩
        simp only [List.mem_singleton]
        rintro a ha b rfl rfl
        exact hh (h4 _ ha)
      · intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · exact h3 a ha
        · rw [List.mem_singleton.1 ha]
          exact hr
      · intro w hw
        rw [visits_append_one] at hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hsub w (h4 w hw)
        · rw [List.mem_singleton.1 hw]
          exact hv0

theorem source_mem_iterate (N : Network) (f : Flow) :
    ∀ k, N.source ∈ (reachStep N f)^[k] [N.source]
  | 0 => List.mem_singleton_self _
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact List.mem_append_left _ (source_mem_iterate N f k)

theorem iterate_lt {N : Network} (h : N.WellFormed) (f : Flow) :
    ∀ k, ∀ v ∈ (reachStep N f)^[k] [N.source], v < N.g.n
  | 0, v, hv => by
    simp only [Function.iterate_zero, id_eq, List.mem_singleton] at hv
    exact hv ▸ h.2.2.1
  | k + 1, v, hv => by
    rw [Function.iterate_succ_apply'] at hv
    rcases List.mem_append.1 hv with hv | hv
    · exact iterate_lt h f k v hv
    obtain ⟨i, hi, ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩ := mem_reachNew hv
    · exact (Network.endpoints_lt h hi).2
    · exact (Network.endpoints_lt h hi).1

/-- A step of the search that adds a vertex adds one not there before. -/
theorem card_reachStep {N : Network} {f : Flow} {S : List ℕ} (hne : reachStep N f S ≠ S) :
    S.toFinset.card + 1 ≤ (reachStep N f S).toFinset.card := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ reachNew N f S :=
    List.exists_mem_of_ne_nil _ fun hL => hne (by rw [reachStep_eq, hL, List.append_nil])
  have hvS : v ∉ S := by
    obtain ⟨i, -, ⟨-, hh, -, rfl⟩ | ⟨-, hh, -, rfl⟩⟩ := mem_reachNew hv <;> exact hh
  have hsub : insert v S.toFinset ⊆ (reachStep N f S).toFinset := by
    intro w hw
    rw [Finset.mem_insert, List.mem_toFinset] at hw
    rw [List.mem_toFinset, reachStep_eq, List.mem_append]
    rcases hw with rfl | hw
    · exact Or.inr hv
    · exact Or.inl hw
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simpa using hvS)] at this

/-- After `n` steps the search adds nothing more. -/
theorem reached_closed {N : Network} (h : N.WellFormed) (f : Flow) :
    reachNew N f (reached N f) = [] := by
  have key : ∀ k, reachStep N f ((reachStep N f)^[k] [N.source]) =
      (reachStep N f)^[k] [N.source] ∨ k + 1 ≤ ((reachStep N f)^[k] [N.source]).toFinset.card := by
    intro k
    induction k with
    | zero => right; simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with hc | hc
      · left
        rw [hc, hc]
      · by_cases hS : reachStep N f ((reachStep N f)^[k] [N.source]) =
            (reachStep N f)^[k] [N.source]
        · left
          rw [hS, hS]
        · right
          have := card_reachStep hS
          omega
  have hc : reachStep N f (reached N f) = reached N f := by
    rcases key N.g.n with hc | hc
    · exact hc
    · exfalso
      have hsub : ((reachStep N f)^[N.g.n] [N.source]).toFinset ⊆ Finset.range N.g.n :=
        fun v hv => Finset.mem_range.2 (iterate_lt h f _ v (List.mem_toFinset.1 hv))
      have := Finset.card_le_card hsub
      simp only [Finset.card_range] at this
      omega
  rw [reachStep_eq] at hc
  exact List.append_right_eq_self.1 hc

/-! ### Flows and cuts -/

/-- The loop's flow is the rounds applied in order from the zero flow. -/
theorem PathRule.run_walks (r : PathRule) (N : Network) :
    (r.run N).2 = (r.run N).1.foldl applyAll (Flow.zero N) :=
  r.runRounds_walks N _ _ _

/-- The zero flow is a flow. -/
theorem zero_isFlow (N : Network) : IsFlow N (Flow.zero N) := by
  refine ⟨fun i _ => by simp [Flow.on_zero], fun v _ _ _ => by simp [inflow, outflow, Flow.on_zero],
    by simp [WellFormed, Flow.zero]⟩

/-- Adding along paths that are augmenting in turn keeps a flow a flow, and raises its amount by
the amounts added. -/
theorem applyAll_isFlow {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {xs : List Augmentation} (hx : FitInTurn N f xs) :
    IsFlow N (applyAll f xs) ∧ value N (applyAll f xs) = value N f + (xs.map (·.amount)).sum := by
  induction xs generalizing f with
  | nil => simp [applyAll, hf]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hx
    obtain ⟨hf', hv⟩ := apply_isFlow h hf hx
    obtain ⟨h1, h2⟩ := ih hf' hxs
    refine ⟨h1, ?_⟩
    simp only [applyAll, List.foldl_cons] at h1 h2 ⊢
    rw [h2, hv]
    push_cast [List.map_cons, List.sum_cons]
    ring

/-- **No flow exceeds any cut**: a flow amount is at most the capacity of every cut with the
source on one side and the sink on the other. -/
theorem value_le_cutCapacity {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {side : List ℕ} (hs : N.source ∈ side) (ht : N.sink ∉ side) :
    value N f ≤ cutCapacity N side := by
  rw [value_eq_cross h hf hs ht, cutCapacity, Network.ids, sum_filter_range]
  refine Finset.sum_le_sum fun i hi => ?_
  have hc : f.on i ≤ N.capOf i := hf.1 i (Finset.mem_range.1 hi)
  by_cases a : N.tail i ∈ side <;> by_cases b : N.head i ∈ side <;> (simp [a, b]; try omega)

/-- **When no augmenting path is left, the reached vertices are a cut of the flow amount.** -/
theorem reached_cut {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    (hnone : ∀ p, ¬ IsAugmentingPath N f p) :
    N.source ∈ reached N f ∧ N.sink ∉ reached N f ∧
      (cutCapacity N (reached N f) : ℤ) = value N f := by
  have hs : N.source ∈ reached N f := source_mem_iterate N f _
  have ht : N.sink ∉ reached N f := fun hm => by
    obtain ⟨p, h1, h2, h3, -⟩ := reached_paths N f _ _ hm
    exact hnone p ⟨h1, h2, h3⟩
  refine ⟨hs, ht, ?_⟩
  have hnil := List.flatMap_eq_nil_iff.1 (reached_closed h f)
  rw [value_eq_cross h hf hs ht, cutCapacity, Network.ids, sum_filter_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hc : f.on i ≤ N.capOf i := hf.1 i hi'
  have hn := hnil i (List.mem_range.2 hi')
  simp only [List.append_eq_nil_iff, ResidualArrow.residualCapacity] at hn
  obtain ⟨n1, n2⟩ := hn
  by_cases a : N.tail i ∈ reached N f <;> by_cases b : N.head i ∈ reached N f <;>
    simp [a, b] at n1 n2 ⊢ <;> omega

/-! ### The loop's rounds -/

theorem value_zero (N : Network) : value N (Flow.zero N) = 0 := by
  simp [value, outflow, inflow, Flow.on_zero]

/-- No flow carries more than the total capacity. -/
theorem value_le_totalCapacity {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f) :
    value N f ≤ totalCapacity N := by
  refine (value_le_cutCapacity h hf (List.mem_singleton_self N.source)
    (fun e => h.2.2.2.2 (List.mem_singleton.1 e).symm)).trans ?_
  rw [cutCapacity, totalCapacity]
  exact_mod_cast (List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _

theorem length_le_sum_amount (xs : List Augmentation) (h : ∀ x ∈ xs, 1 ≤ x.amount) :
    xs.length ≤ (xs.map (·.amount)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

theorem PathRule.runRounds_isFlow {r : PathRule} (hr : r.Promise) {N : Network}
    (h : N.WellFormed) : ∀ k m f, IsFlow N f → ∀ j ≤ (r.runRounds N k m f).1.length,
      IsFlow N (((r.runRounds N k m f).1.take j).foldl applyAll f)
  | 0, _, f, hf, j, _ => by simp [PathRule.runRounds, hf]
  | k + 1, m, f, hf, j, hj => by
    rcases hround : r.round N m f with ⟨m', _ | ⟨x, xs⟩⟩
    · rw [r.runRounds_nil N k hround] at hj ⊢
      simp [hf]
    · rw [r.runRounds_cons N k hround] at hj ⊢
      have hfit := hr.sendsAlong N h m f hf
      rw [hround] at hfit
      dsimp only at hfit
      have hf' := (applyAll_isFlow h hf hfit).1
      cases j with
      | zero => simpa using hf
      | succ j =>
        simp only [List.take_succ_cons, List.foldl_cons]
        exact r.runRounds_isFlow hr h k m' _ hf' j (by simpa using hj)

theorem PathRule.runRounds_done {r : PathRule} (hr : r.Promise) {N : Network}
    (h : N.WellFormed) : ∀ (k : ℕ) m f, IsFlow N f → (totalCapacity N : ℤ) < value N f + k →
      ∀ p, ¬ IsAugmentingPath N (r.runRounds N k m f).2 p
  | 0, _, f, hf, hk, _ => by
    have := value_le_totalCapacity h hf
    push_cast at hk
    omega
  | k + 1, m, f, hf, hk, p => by
    rcases hround : r.round N m f with ⟨m', _ | ⟨x, xs⟩⟩
    · rw [r.runRounds_nil N k hround]
      exact hr.noneOnlyWhenDone N h m f hf (by rw [hround]) p
    · rw [r.runRounds_cons N k hround]
      have hfit := hr.sendsAlong N h m f hf
      rw [hround] at hfit
      dsimp only at hfit
      obtain ⟨hf', hv⟩ := applyAll_isFlow h hf hfit
      have h1 := hr.addsAtLeastOne N h m f hf
      rw [hround] at h1
      dsimp only at h1
      have hl := length_le_sum_amount _ h1
      simp only [List.length_cons] at hl
      refine r.runRounds_done hr h k m' _ hf' ?_ p
      rw [hv]
      simp only [Nat.cast_add, Nat.cast_one] at hk
      omega

theorem PathRule.runRounds_added {r : PathRule} (hr : r.Promise) {N : Network}
    (h : N.WellFormed) : ∀ k m f, IsFlow N f →
      ((r.runRounds N k m f).1.flatten.length : ℤ) + value N f ≤ value N (r.runRounds N k m f).2
  | 0, _, _, _ => by simp [PathRule.runRounds]
  | k + 1, m, f, hf => by
    rcases hround : r.round N m f with ⟨m', _ | ⟨x, xs⟩⟩
    · rw [r.runRounds_nil N k hround]
      simp
    · rw [r.runRounds_cons N k hround]
      have hfit := hr.sendsAlong N h m f hf
      rw [hround] at hfit
      dsimp only at hfit
      obtain ⟨hf', hv⟩ := applyAll_isFlow h hf hfit
      have h1 := hr.addsAtLeastOne N h m f hf
      rw [hround] at h1
      dsimp only at h1
      have hl := length_le_sum_amount _ h1
      have ih := r.runRounds_added hr h k m' _ hf'
      rw [hv] at ih
      simp only [List.flatten_cons, List.length_append, Nat.cast_add]
      omega

/-- Every round of the loop keeps the flow a flow, and the last round added nothing. -/
theorem PathRule.run_ends {r : PathRule} (hr : r.Promise) {N : Network} (h : N.WellFormed) :
    (∀ k ≤ (r.run N).1.length, IsFlow N (((r.run N).1.take k).foldl applyAll (Flow.zero N))) ∧
      ∀ p, ¬ IsAugmentingPath N (r.run N).2 p :=
  ⟨fun k hk => r.runRounds_isFlow hr h _ _ _ (zero_isFlow N) k hk,
    r.runRounds_done hr h (totalCapacity N + 1) (r.start N) (Flow.zero N) (zero_isFlow N)
      (by rw [value_zero]; push_cast; omega)⟩

/-- Every path the loop added carries at least one unit, so it added at most as many paths as the
amount it ends with. -/
theorem PathRule.added_le_value {r : PathRule} (hr : r.Promise) {N : Network} (h : N.WellFormed) :
    (((r.run N).1.flatten).length : ℤ) ≤ value N (r.run N).2 := by
  have := r.runRounds_added hr h (totalCapacity N + 1) (r.start N) (Flow.zero N) (zero_isFlow N)
  rw [value_zero, add_zero] at this
  exact this

/-- Added paths augmenting in turn, one list after another: the first list in turn from `f`, the
second from the flow the first leaves. -/
theorem fitInTurn_append_iff {N : Network} {ys : List Augmentation} :
    ∀ {f : Flow} {xs : List Augmentation},
      FitInTurn N f (xs ++ ys) ↔ FitInTurn N f xs ∧ FitInTurn N (applyAll f xs) ys
  | f, [] => by simp [FitInTurn, applyAll]
  | f, x :: xs => by
    simp only [List.cons_append, FitInTurn, applyAll, List.foldl_cons]
    rw [fitInTurn_append_iff]
    simp only [applyAll, and_assoc]

/-- Every path the loop's rounds add is augmenting in its turn and carries at least one unit. -/
theorem PathRule.runRounds_augments {r : PathRule} (hr : r.Promise) {N : Network}
    (h : N.WellFormed) : ∀ k m f, IsFlow N f → FitInTurn N f (r.runRounds N k m f).1.flatten ∧
      ∀ x ∈ (r.runRounds N k m f).1.flatten, 1 ≤ x.amount
  | 0, _, _, _ => by simp [PathRule.runRounds, FitInTurn]
  | k + 1, m, f, hf => by
    rcases hround : r.round N m f with ⟨m', _ | ⟨x, xs⟩⟩
    · rw [r.runRounds_nil N k hround]
      simp [FitInTurn]
    · rw [r.runRounds_cons N k hround]
      have hfit := hr.sendsAlong N h m f hf
      have h1 := hr.addsAtLeastOne N h m f hf
      rw [hround] at hfit h1
      dsimp only at hfit h1
      have hf' := (applyAll_isFlow h hf hfit).1
      obtain ⟨ih1, ih2⟩ := r.runRounds_augments hr h k m' _ hf'
      simp only [List.flatten_cons, List.mem_append]
      exact ⟨fitInTurn_append_iff.2 ⟨hfit, ih1⟩, fun y hy => hy.elim (h1 y) (ih2 y)⟩

/-- The library's procedures for a path rule that keeps the promise. -/
def PathRule.ops (r : PathRule) (hr : r.Promise) : Ops where
  maxFlow := r.maxFlow
  rounds N := (r.run N).1
  Valid := Valid
  walks N := r.run_walks N
  startValid N _ := ⟨(zero_isFlow N).1, (zero_isFlow N).2.1⟩
  roundsKeep _ h k hk := ⟨((r.run_ends hr h).1 k hk).1, ((r.run_ends hr h).1 k hk).2.1⟩
  augments _ h := r.runRounds_augments hr h _ _ _ (zero_isFlow _)

/-- **The template's theorem**: a path rule that keeps the promise, and whose rounds add a number of
paths bounded by the network's size, meets the max-flow contract. -/
theorem PathRule.contract {r : PathRule} (hr : r.Promise) (hb : (r.ops hr).BoundSetBySize) :
    Contract (r.ops hr) := by
  have hflow : ∀ N : Network, N.WellFormed → IsFlow N (r.run N).2 := fun N h => by
    have := (r.run_ends hr h).1 _ le_rfl
    rwa [List.take_length, ← r.run_walks] at this
  refine ⟨⟨fun N h => hflow N h, fun N h => reached_cut h (hflow N h) (r.run_ends hr h).2,
    fun N h g hg => ?_⟩, fun _ => Iff.rfl, ⟨fun N h => r.added_le_value hr h, hb⟩⟩
  have hcut := reached_cut h (hflow N h) (r.run_ends hr h).2
  exact (value_le_cutCapacity h hg hcut.1 hcut.2.1).trans hcut.2.2.le

end AlgoDesign.Flows
