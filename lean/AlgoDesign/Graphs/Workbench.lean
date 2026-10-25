/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Workbench.Spec
public import AlgoDesign.Graphs.Workbench.Decide
public import Mathlib.Data.Finset.Card

/-! The design project's contract is in `Workbench/Spec.lean`; this file imports it and proves
that one candidate, `reference`, meets it (`reference_contract`).

The reference is written to be read and proved, not to be fast. It keeps one thing for each task:
a chain of waits from a task in a knot to it, or nothing (`Chains`). It starts with a chain of one
at every task in a knot, and spreads chains along the arrows between unfinished tasks: an arrow
whose tail has a chain and whose head has none gives the head its tail's chain, extended by the
head (`follow`). One sweep follows every arrow; `n + 1` sweeps leave nothing to spread
(`closed_chainsFrom`), since each sweep that changes something gives one more task a chain. Whether
a task is in a knot is worked out the same way, spreading from the task itself (`knotted_iff`).

Its own invariants, the bottom half of its box, are `Analysis.Valid`: every chain kept is a real
chain of waits from a knot (`ChainsReal`), every task in a knot has one (`KnotsStart`), and a chain
passes along every wait between unfinished tasks (`ChainsSpread`). `Valid` alone gives the blocked
tasks and the answers to "why" (`isSome_chain_iff`); `valid_build` shows the reference keeps it.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Workbench

open Digraph

/-! ## Spreading chains along arrows -/

/-- For each task, the chain of waits kept for it, or nothing. -/
abbrev Chains := ℕ → Option (List ℕ)

/-- Follow the arrow `e`: if its head has no chain yet, it gets its tail's chain, extended by the
head. -/
def follow (r : Chains) (e : ℕ × ℕ) : Chains :=
  fun x => if x = e.2 ∧ r x = none then (r e.1).map (· ++ [e.2]) else r x

/-- One sweep: follow every arrow of `es`, in order. -/
def sweep (es : List (ℕ × ℕ)) (r : Chains) : Chains := es.foldl follow r

/-- **Spread the chains** `r` along the arrows of `h`, for `h.n + 1` sweeps. -/
def chainsFrom (h : Digraph) (r : Chains) : Chains := (sweep h.arrows)^[h.n + 1] r

/-- A chain once kept is kept as it is. -/
theorem follow_of_some {r : Chains} {e : ℕ × ℕ} {x : ℕ} {p : List ℕ} (h : r x = some p) :
    follow r e x = some p := by
  simp [follow, h]

theorem sweep_of_some {es : List (ℕ × ℕ)} {r : Chains} {x : ℕ} {p : List ℕ}
    (h : r x = some p) : sweep es r x = some p := by
  induction es generalizing r with
  | nil => exact h
  | cons e es ih => exact ih (follow_of_some h)

theorem iterate_sweep_of_some {es : List (ℕ × ℕ)} {r : Chains} {x : ℕ} {p : List ℕ}
    (h : r x = some p) : ∀ k, (sweep es)^[k] r x = some p
  | 0 => h
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact sweep_of_some (iterate_sweep_of_some h k)

theorem chainsFrom_of_some {h : Digraph} {r : Chains} {x : ℕ} {p : List ℕ}
    (hx : r x = some p) : chainsFrom h r x = some p :=
  iterate_sweep_of_some hx _

/-- After a sweep, the head of every arrow whose tail had a chain has one. -/
theorem isSome_sweep_head {es : List (ℕ × ℕ)} {r : Chains} {e : ℕ × ℕ} (he : e ∈ es)
    (h1 : (r e.1).isSome) : (sweep es r e.2).isSome := by
  induction es generalizing r with
  | nil => cases he
  | cons e' es ih =>
    rcases List.mem_cons.1 he with rfl | he
    · have hs : (follow r e e.2).isSome := by
        by_cases hn : r e.2 = none
        · simpa [follow, hn] using h1
        · simpa [follow, hn] using Option.ne_none_iff_isSome.1 hn
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
      change (sweep es (follow r e) e.2).isSome
      rw [sweep_of_some hp]; rfl
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h1
      exact ih he (by rw [follow_of_some hp]; rfl)

/-- Every chain kept has the property `Good`. -/
def Inv (Good : ℕ → List ℕ → Prop) (r : Chains) : Prop := ∀ x p, r x = some p → Good x p

theorem inv_follow {Good : ℕ → List ℕ → Prop} {r : Chains} {e : ℕ × ℕ}
    (hstep : ∀ q, Good e.1 q → Good e.2 (q ++ [e.2])) (h : Inv Good r) :
    Inv Good (follow r e) := by
  intro x p hx
  simp only [follow] at hx
  split_ifs at hx with hc
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hx
    rw [hc.1]
    exact hstep q (h _ _ hq)
  · exact h x p hx

theorem inv_sweep {Good : ℕ → List ℕ → Prop} {es : List (ℕ × ℕ)} {r : Chains}
    (hstep : ∀ e ∈ es, ∀ q, Good e.1 q → Good e.2 (q ++ [e.2])) (h : Inv Good r) :
    Inv Good (sweep es r) := by
  induction es generalizing r with
  | nil => exact h
  | cons e es ih =>
    exact ih (fun e' he' => hstep e' (List.mem_cons_of_mem _ he'))
      (inv_follow (hstep e List.mem_cons_self) h)

theorem inv_iterate {Good : ℕ → List ℕ → Prop} {es : List (ℕ × ℕ)} {r : Chains}
    (hstep : ∀ e ∈ es, ∀ q, Good e.1 q → Good e.2 (q ++ [e.2])) (h : Inv Good r) :
    ∀ k, Inv Good ((sweep es)^[k] r)
  | 0 => h
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact inv_sweep hstep (inv_iterate hstep h k)

/-- **Spreading keeps a property of chains** that every arrow carries forward. -/
theorem inv_chainsFrom {Good : ℕ → List ℕ → Prop} {h : Digraph} {r : Chains}
    (hstep : ∀ e ∈ h.arrows, ∀ q, Good e.1 q → Good e.2 (q ++ [e.2])) (h0 : Inv Good r) :
    Inv Good (chainsFrom h r) :=
  inv_iterate hstep h0 _

/-- Nothing left to spread: the head of every arrow whose tail has a chain has one. -/
def Closed (es : List (ℕ × ℕ)) (r : Chains) : Prop :=
  ∀ e ∈ es, (r e.1).isSome → (r e.2).isSome

theorem follow_eq_of_closed {r : Chains} {e : ℕ × ℕ} (h : (r e.1).isSome → (r e.2).isSome) :
    follow r e = r := by
  funext x
  simp only [follow]
  split_ifs with hc
  · obtain ⟨rfl, hx⟩ := hc
    have h1 : r e.1 = none := by
      cases h1 : r e.1 with
      | none => rfl
      | some q => simp [h1, hx] at h
    simp [h1, hx]
  · rfl

theorem sweep_eq_of_closed {es : List (ℕ × ℕ)} {r : Chains} (h : Closed es r) :
    sweep es r = r := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change sweep es (follow r e) = r
    rw [follow_eq_of_closed (h e List.mem_cons_self)]
    exact ih fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- The tasks below `n` that have a chain. -/
def dom (n : ℕ) (r : Chains) : Finset ℕ := (Finset.range n).filter fun x => (r x).isSome

/-- A sweep that leaves something to spread gives one more task a chain. -/
theorem card_dom_lt {n : ℕ} {es : List (ℕ × ℕ)} {r : Chains}
    (hb : ∀ x, (sweep es r x).isSome → x < n) (hnc : ¬ Closed es r) :
    (dom n r).card < (dom n (sweep es r)).card := by
  simp only [Closed, not_forall] at hnc
  obtain ⟨e, he, h1, h2⟩ := hnc
  apply Finset.card_lt_card
  have hsub : dom n r ⊆ dom n (sweep es r) := by
    intro x hx
    simp only [dom, Finset.mem_filter, Finset.mem_range] at hx ⊢
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hx.2
    exact ⟨hx.1, by rw [sweep_of_some hp]; rfl⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  have hs := isSome_sweep_head he h1
  exact ⟨e.2, by simp [dom, hs, hb _ hs], by simp [dom, h2]⟩

theorem card_dom_le (n : ℕ) (r : Chains) : (dom n r).card ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem closed_or_card {n : ℕ} {es : List (ℕ × ℕ)} {r : Chains}
    (hb : ∀ k x, ((sweep es)^[k] r x).isSome → x < n) :
    ∀ k, Closed es ((sweep es)^[k] r) ∨ k ≤ (dom n ((sweep es)^[k] r)).card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    by_cases hc : Closed es ((sweep es)^[k] r)
    · left
      rw [sweep_eq_of_closed hc]
      exact hc
    · right
      have hk := (closed_or_card hb k).resolve_left hc
      have hlt := card_dom_lt (n := n) (fun x hx => hb (k + 1) x
        (by rw [Function.iterate_succ_apply']; exact hx)) hc
      omega

/-- **`h.n + 1` sweeps leave nothing to spread**, when every chain is at a task of `h`. -/
theorem closed_chainsFrom {h : Digraph} {r : Chains} (hwf : h.WellFormed)
    (h0 : ∀ x, (r x).isSome → x < h.n) : Closed h.arrows (chainsFrom h r) := by
  have hinv : ∀ k, Inv (fun x _ => x < h.n) ((sweep h.arrows)^[k] r) :=
    inv_iterate (fun e he _ _ => (hwf e he).2)
      (fun x p hx => h0 x (by rw [hx]; rfl))
  have hb : ∀ k x, ((sweep h.arrows)^[k] r x).isSome → x < h.n := fun k x hx => by
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hx
    exact hinv k x p hp
  rcases closed_or_card hb (h.n + 1) with hc | hc
  · exact hc
  · have := card_dom_le h.n ((sweep h.arrows)^[h.n + 1] r)
    omega

/-- With nothing left to spread, a chain reaches everything its task reaches. -/
theorem isSome_of_reaches {h : Digraph} {r : Chains} (hc : Closed h.arrows r) {x y : ℕ}
    (hx : (r x).isSome) (hr : h.Reaches x y) : (r y).isSome := by
  induction hr with
  | refl => exact hx
  | tail _ hab ih => exact hc _ hab ih

/-! ## Knots -/

/-- A chain of one at `v`, and nothing elsewhere. -/
def single (v : ℕ) : Chains := fun x => if x = v then some [v] else none

/-- The arrows still holding anyone up join two tasks of the plan. -/
theorem wellFormed_pending {g : Digraph} {done : Finset ℕ} (hwf : g.WellFormed) :
    (pending g done).WellFormed := fun a ha => hwf a (List.mem_filter.1 ha).1

theorem arrow_pending {g : Digraph} {done : Finset ℕ} {a b : ℕ} :
    (pending g done).Arrow a b ↔ g.Arrow a b ∧ a ∉ done ∧ b ∉ done := by
  simp [pending, Digraph.Arrow, List.mem_filter]

/-- Spreading from `v` gives a chain to exactly the tasks `v` reaches. -/
theorem isSome_chainsFrom_single {h : Digraph} (hwf : h.WellFormed) {v x : ℕ} (hv : v < h.n) :
    (chainsFrom h (single v) x).isSome ↔ h.Reaches v x := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hx
    have hinv : Inv (fun x _ => h.Reaches v x) (chainsFrom h (single v)) :=
      inv_chainsFrom (fun e he _ hq => hq.tail he) (fun x p hx => by
        simp only [single] at hx
        split_ifs at hx with hxv
        exact hxv ▸ Relation.ReflTransGen.refl)
    exact hinv x p hp
  · intro hr
    refine isSome_of_reaches (closed_chainsFrom hwf fun x hx => ?_) ?_ hr
    · simp only [single] at hx
      split_ifs at hx with hxv
      · exact hxv ▸ hv
      · cases hx
    · rw [chainsFrom_of_some (p := [v]) (by simp [single])]; rfl

/-- **The knot test**: `v` is unfinished, and some arrow between unfinished tasks into `v` comes
from a task that spreading from `v` gives a chain. -/
def knotted (g : Digraph) (done : Finset ℕ) (v : ℕ) : Prop :=
  v < g.n ∧ v ∉ done ∧
    ∃ e ∈ (pending g done).arrows,
      e.2 = v ∧ (chainsFrom (pending g done) (single v) e.1).isSome

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) : Decidable (knotted g done v) := by
  unfold knotted; infer_instance

theorem knotted_iff {g : Digraph} {done : Finset ℕ} (hwf : g.WellFormed) {v : ℕ} :
    knotted g done v ↔ InKnot g done v := by
  unfold knotted InKnot Unfinished
  constructor
  · rintro ⟨hv, hd, e, he, rfl, hs⟩
    refine ⟨⟨hv, hd⟩, e.1, he, ?_⟩
    exact (isSome_chainsFrom_single (wellFormed_pending hwf) hv).1 hs
  · rintro ⟨⟨hv, hd⟩, w, hw, hr⟩
    exact ⟨hv, hd, (w, v), hw, rfl, (isSome_chainsFrom_single (wellFormed_pending hwf) hv).2 hr⟩

/-! ## The four lists, from what any task reaches -/

/-- A task a pending arrow leads to, or that is itself the start, is all `Reaches` gives. -/
theorem reaches_cases {g : Digraph} {done : Finset ℕ} {k v : ℕ}
    (h : (pending g done).Reaches k v) : v = k ∨ ∃ b, (pending g done).Arrow b v :=
  (Relation.ReflTransGen.cases_tail h).imp_right fun ⟨b, _, hb⟩ => ⟨b, hb⟩

theorem not_inKnot_of_ready {g : Digraph} {done : Finset ℕ} {v : ℕ} (h : Ready g done v) :
    ¬ InKnot g done v := by
  rintro ⟨_, w, hw, _⟩
  exact (arrow_pending.1 hw).2.1 (h.2 w (arrow_pending.1 hw).1)

theorem not_blocked_of_ready {g : Digraph} {done : Finset ℕ} {v : ℕ} (h : Ready g done v) :
    ¬ Blocked g done v := by
  rintro ⟨_, _, k, hk, hr⟩
  rcases reaches_cases hr with rfl | ⟨b, hb⟩
  · exact not_inKnot_of_ready h hk
  · exact (arrow_pending.1 hb).2.1 (h.2 b (arrow_pending.1 hb).1)

/-- **Each unfinished task is in exactly one list**, at the level of the definitions. -/
theorem later_iff {g : Digraph} {done : Finset ℕ} {v : ℕ} :
    Later g done v ↔ Unfinished g done v ∧ ¬ Ready g done v ∧ ¬ InKnot g done v ∧
      ¬ Blocked g done v := by
  unfold Later Blocked
  constructor
  · rintro ⟨hu, hr, hk⟩
    exact ⟨hu, hr, hk v Relation.ReflTransGen.refl, fun ⟨_, _, k, hk', hr'⟩ => hk k hr' hk'⟩
  · rintro ⟨hu, hr, hk, hb⟩
    exact ⟨hu, hr, fun k hr' hk' => hb ⟨hu, hk, k, hk', hr'⟩⟩

/-! ## The reference candidate -/

/-- What the reference builds: the plan, the tasks done, and a chain of waits for each task a
knot reaches. -/
structure Analysis where
  /-- The tasks and their arrows. -/
  g : Digraph
  /-- The tasks already done. -/
  done : Finset ℕ
  /-- For each task a knot reaches, a chain of waits from a task in a knot to it. -/
  chain : Chains

/-- A chain of one at every task in a knot. -/
def knotStarts (g : Digraph) (done : Finset ℕ) : Chains :=
  fun k => if knotted g done k then some [k] else none

/-- Build: spread chains from the knots along the arrows between unfinished tasks. -/
def analyse (g : Digraph) (done : Finset ℕ) : Analysis :=
  ⟨g, done, chainsFrom (pending g done) (knotStarts g done)⟩

/-- Invariant 1: every chain kept is a real chain of waits from a task in a knot to its task. -/
def Analysis.ChainsReal (s : Analysis) : Prop :=
  ∀ v p, s.chain v = some p → WaitChain s.g s.done v p

/-- Invariant 2: every task in a knot has a chain. -/
def Analysis.KnotsStart (s : Analysis) : Prop := ∀ k, InKnot s.g s.done k → (s.chain k).isSome

/-- Invariant 3: a chain passes along every wait between two unfinished tasks. -/
def Analysis.ChainsSpread (s : Analysis) : Prop :=
  ∀ a b, (pending s.g s.done).Arrow a b → (s.chain a).isSome → (s.chain b).isSome

/-- **The reference's invariants**, the bottom half of its box. -/
def Analysis.Valid (s : Analysis) : Prop := s.ChainsReal ∧ s.KnotsStart ∧ s.ChainsSpread

/-- **`Valid` alone gives the blocked tasks**: a task has a chain exactly when a knot reaches it. -/
theorem isSome_chain_iff {s : Analysis} (hs : s.Valid) {v : ℕ} :
    (s.chain v).isSome ↔ ∃ k, InKnot s.g s.done k ∧ (pending s.g s.done).Reaches k v := by
  constructor
  · intro hv
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hv
    obtain ⟨⟨k, hk, hkin⟩, hl, hc⟩ := hs.1 v p hp
    have hne : p ≠ [] := by rintro rfl; cases hl
    refine ⟨k, hkin, ?_⟩
    have hk' : p.head hne = k := by
      rwa [List.head?_eq_some_head hne, Option.some.injEq] at hk
    have hl' : p.getLast hne = v := by
      rwa [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hl
    have := List.relationReflTransGen_of_exists_isChain p hc hne
    rwa [hk', hl'] at this
  · rintro ⟨k, hk, hr⟩
    induction hr with
    | refl => exact hs.2.1 k hk
    | tail _ hab ih => exact hs.2.2 _ _ hab ih

theorem blocked_iff {s : Analysis} (hs : s.Valid) {v : ℕ} :
    Blocked s.g s.done v ↔ Unfinished s.g s.done v ∧ ¬ InKnot s.g s.done v ∧
      (s.chain v).isSome := by
  rw [isSome_chain_iff hs]; rfl

/-- The ready test the reference runs: unfinished, and every arrow into it comes from a done
task. -/
def readyTest (s : Analysis) (v : ℕ) : Prop :=
  v < s.g.n ∧ v ∉ s.done ∧ ∀ e ∈ s.g.arrows, e.2 = v → e.1 ∈ s.done

instance (s : Analysis) (v : ℕ) : Decidable (readyTest s v) := by
  unfold readyTest; infer_instance

theorem readyTest_iff {s : Analysis} {v : ℕ} : readyTest s v ↔ Ready s.g s.done v := by
  unfold readyTest Ready Unfinished Digraph.Arrow
  constructor
  · rintro ⟨hv, hd, h⟩
    exact ⟨⟨hv, hd⟩, fun a ha => h (a, v) ha rfl⟩
  · rintro ⟨⟨hv, hd⟩, h⟩
    exact ⟨hv, hd, fun e he hev => h e.1 (by rw [← hev]; exact he)⟩

/-- The blocked test the reference runs: unfinished, not in a knot, and it has a chain. -/
def blockedTest (s : Analysis) (v : ℕ) : Prop :=
  v < s.g.n ∧ v ∉ s.done ∧ ¬ knotted s.g s.done v ∧ (s.chain v).isSome

instance (s : Analysis) (v : ℕ) : Decidable (blockedTest s v) := by
  unfold blockedTest; infer_instance

/-- The later test the reference runs: unfinished, and none of the other three. -/
def laterTest (s : Analysis) (v : ℕ) : Prop :=
  v < s.g.n ∧ v ∉ s.done ∧ ¬ readyTest s v ∧ ¬ knotted s.g s.done v ∧
    ¬ (s.chain v).isSome

instance (s : Analysis) (v : ℕ) : Decidable (laterTest s v) := by
  unfold laterTest; infer_instance

/-- The tasks below `n` that pass a test. -/
def tasksWhere (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : List ℕ :=
  (List.range n).filter (p ·)

theorem mem_tasksWhere {n : ℕ} {p : ℕ → Prop} [DecidablePred p] {v : ℕ}
    (hp : ∀ v, p v → v < n) :
    v ∈ tasksWhere n p ↔ p v := by
  simp only [tasksWhere, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hp v h, h⟩⟩

theorem nodup_tasksWhere (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : (tasksWhere n p).Nodup :=
  List.nodup_range.filter _

/-! ## The reference keeps its invariants -/

theorem knotStarts_eq {g : Digraph} {done : Finset ℕ} {k : ℕ} {p : List ℕ}
    (h : knotStarts g done k = some p) : knotted g done k ∧ p = [k] := by
  simp only [knotStarts] at h
  split_ifs at h with hk
  · exact ⟨hk, (Option.some.inj h).symm⟩

/-- **The reference keeps its invariants** on every well-formed plan. -/
theorem valid_build {g : Digraph} {done : Finset ℕ} (hwf : g.WellFormed) :
    (analyse g done).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro v p hp
    have hinv : Inv (fun x p => WaitChain g done x p) (chainsFrom (pending g done)
        (knotStarts g done)) := by
      refine inv_chainsFrom (fun e he q hq => ?_) (fun x p hx => ?_)
      · obtain ⟨⟨k, hk, hkin⟩, hl, hc⟩ := hq
        have hne : q ≠ [] := by rintro rfl; cases hl
        refine ⟨⟨k, ?_, hkin⟩, by simp, ?_⟩
        · rw [List.head?_append, hk]; rfl
        · refine hc.append (List.isChain_singleton _) ?_
          intro x hx y hy
          rw [hl] at hx
          simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
          subst hx hy
          exact he
      · obtain ⟨hk, rfl⟩ := knotStarts_eq hx
        exact ⟨⟨x, rfl, (knotted_iff hwf).1 hk⟩, rfl, List.isChain_singleton _⟩
    exact hinv v p hp
  · intro k hk
    have hk' : knotted g done k := (knotted_iff hwf).2 hk
    change (chainsFrom _ _ k).isSome
    rw [chainsFrom_of_some (p := [k]) (by simp [knotStarts, hk'])]
    rfl
  · intro a b hab ha
    refine closed_chainsFrom (wellFormed_pending hwf) (fun x hx => ?_) (a, b) hab ha
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hx
    exact ((knotted_iff hwf).1 (knotStarts_eq hp).1).1.1

/-- **The reference candidate**: chains spread from the knots, and each list read off by its
test. -/
def reference : Ops Analysis where
  build := analyse
  ready s := tasksWhere s.g.n (readyTest s)
  later s := tasksWhere s.g.n (laterTest s)
  knot s := tasksWhere s.g.n (knotted s.g s.done)
  blocked s := tasksWhere s.g.n (blockedTest s)
  why s v := if blockedTest s v then s.chain v else none
  Valid := Analysis.Valid
  buildValid _ _ hwf := valid_build hwf

/-! ## The reference meets the contract -/

section
variable {g : Digraph} {done : Finset ℕ}

theorem mem_ready {v : ℕ} :
    v ∈ reference.ready (reference.build g done) ↔ Ready g done v := by
  change v ∈ tasksWhere _ _ ↔ _
  rw [mem_tasksWhere (fun v h => h.1)]
  exact readyTest_iff

theorem mem_knot (hwf : g.WellFormed) {v : ℕ} :
    v ∈ reference.knot (reference.build g done) ↔ InKnot g done v := by
  change v ∈ tasksWhere _ _ ↔ _
  rw [mem_tasksWhere (fun v h => h.1)]
  exact knotted_iff hwf

theorem blockedTest_iff (hwf : g.WellFormed) {v : ℕ} :
    blockedTest (analyse g done) v ↔ Blocked g done v := by
  have h := blocked_iff (valid_build (done := done) hwf) (v := v)
  simp only [analyse] at h
  rw [h]
  unfold blockedTest Unfinished
  have hk := knotted_iff (done := done) hwf (v := v)
  simp only [analyse, hk, and_assoc]

theorem mem_blocked (hwf : g.WellFormed) {v : ℕ} :
    v ∈ reference.blocked (reference.build g done) ↔ Blocked g done v := by
  change v ∈ tasksWhere _ _ ↔ _
  rw [mem_tasksWhere (fun v h => h.1)]
  exact blockedTest_iff hwf

theorem mem_later (hwf : g.WellFormed) {v : ℕ} :
    v ∈ reference.later (reference.build g done) ↔ Later g done v := by
  change v ∈ tasksWhere _ _ ↔ _
  rw [mem_tasksWhere (fun v h => h.1), later_iff, ← blockedTest_iff hwf]
  have hr := readyTest_iff (s := analyse g done) (v := v)
  have hk := knotted_iff (done := done) hwf (v := v)
  simp only [analyse] at hr
  unfold laterTest blockedTest Unfinished
  simp only [analyse, hk]
  tauto

theorem reference_eachOnce : reference.EachOnce := by
  intro g done hwf
  have hr := fun v => mem_ready (g := g) (done := done) (v := v)
  have hl := fun v => mem_later (done := done) hwf (v := v)
  have hk := fun v => mem_knot (done := done) hwf (v := v)
  have hb := fun v => mem_blocked (done := done) hwf (v := v)
  have hnd : ∀ l ∈ [reference.ready (reference.build g done),
      reference.later (reference.build g done), reference.knot (reference.build g done),
      reference.blocked (reference.build g done)], l.Nodup := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl | rfl) <;> exact nodup_tasksWhere _ _
  have hc : ∀ (l : List ℕ) {v : ℕ}, l.Nodup → l.count v = if v ∈ l then 1 else 0 := by
    intro l v hl
    split_ifs with h
    · exact List.count_eq_one_of_mem hl h
    · exact List.count_eq_zero_of_not_mem h
  refine ⟨fun v hu => ?_, fun v hv => ?_⟩
  · simp only [List.count_append]
    rw [hc _ (hnd _ (by simp)), hc _ (hnd _ (by simp)), hc _ (hnd _ (by simp)),
      hc _ (hnd _ (by simp))]
    generalize reference.ready (reference.build g done) = R at hr ⊢
    generalize reference.later (reference.build g done) = L at hl ⊢
    generalize reference.knot (reference.build g done) = K at hk ⊢
    generalize reference.blocked (reference.build g done) = B at hb ⊢
    classical
    simp only [hr, hl, hk, hb]
    by_cases h1 : Ready g done v
    · simp [h1, not_inKnot_of_ready h1, not_blocked_of_ready h1, later_iff]
    · by_cases h2 : InKnot g done v
      · simp [h1, h2, later_iff, Blocked]
      · by_cases h3 : Blocked g done v
        · simp [h1, h2, h3, later_iff]
        · simp [h1, h2, h3, later_iff, hu]
  · simp only [List.mem_append] at hv
    rcases hv with ((h | h) | h) | h
    · exact ((hr v).1 h).1
    · exact ((hl v).1 h).1
    · exact ((hk v).1 h).1
    · exact ((hb v).1 h).1

theorem reference_explains : reference.Explains := by
  intro g done hwf v
  have hs := valid_build (done := done) hwf
  have key := blockedTest_iff (done := done) hwf (v := v)
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have ht := key.2 hb
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 ht.2.2.2
    exact ⟨p, by simp [reference, ht, hp], hs.1 v p hp⟩
  · simp [reference, show ¬ blockedTest (analyse g done) v from fun h => hb (key.1 h)]

/-- **The reference meets the design project's contract.** -/
theorem reference_contract : Contract reference where
  promise :=
    ⟨reference_eachOnce, fun _ _ _ _ => mem_ready, fun _ _ hwf _ => mem_later hwf,
      fun _ _ hwf _ => mem_knot hwf, fun _ _ hwf _ => mem_blocked hwf, reference_explains⟩

end

/-! ## Examples, checked by the kernel

Tasks 0 and 1 wait for each other, 2 waits for 1, and 3 waits on itself. -/

/-- With nothing done: 0, 1 and 3 are in knots, 2 is blocked, and why gives the chain 1, 2. -/
example : let s := reference.build ⟨4, [(0, 1), (1, 0), (1, 2), (3, 3)]⟩ ∅
    reference.ready s = [] ∧ reference.later s = [] ∧ reference.knot s = [0, 1, 3] ∧
      reference.blocked s = [2] ∧ reference.why s 2 = some [1, 2] ∧
        reference.why s 0 = none := by
  decide

/-- With 0 done, the knot of two is gone: 1 is ready, and 2 will be able to start later. -/
example : let s := reference.build ⟨4, [(0, 1), (1, 0), (1, 2), (3, 3)]⟩ {0}
    reference.ready s = [1] ∧ reference.later s = [2] ∧ reference.knot s = [3] ∧
      reference.blocked s = [] ∧ reference.why s 2 = none := by
  decide

end AlgoDesign.Graphs.Workbench
