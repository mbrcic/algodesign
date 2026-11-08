/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Kruskal.Basic
public import Mathlib.Data.List.Sort

/-!
# Cheapest spanning forest: the walk

Source: Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), §21.2,
`MST-KRUSKAL` (p. 594): sort the links by cost, then, for each link in that order, keep it when its
two ends are in different groups, merging the two.

The test and the merge are one call: the Graphs chapter's union-find `union` merges the two groups
and answers yes, or finds the ends already together and answers no. The library sorts the link ids
by cost, equal costs by id; the proofs hold for every order that takes the links cheapest first
(`run_cheapestForest`). The walk stops once one group is left: every link after that has both ends
in it and would be skipped.
-/

@[expose] public section

namespace AlgoDesign.Paths.Kruskal

open AlgoDesign.Graphs UnionFind LinkNetwork

/-! ## The walk -/

/-- **The order of the links**: by cost, then by id. -/
def LinkLe (N : LinkNetwork) (i j : ℕ) : Prop :=
  N.linkCost i < N.linkCost j ∨ N.linkCost i = N.linkCost j ∧ i ≤ j

instance (N : LinkNetwork) : DecidableRel (LinkLe N) := fun i j =>
  inferInstanceAs (Decidable (N.linkCost i < N.linkCost j ∨ N.linkCost i = N.linkCost j ∧ i ≤ j))

/-- **The library's order**: the link ids sorted by cost, equal costs by id. -/
def order (N : LinkNetwork) : List ℕ := (List.range N.g.links.length).insertionSort (LinkLe N)

/-- **The start**: nothing kept or tried, every vertex a group of its own, the links to take in the
order `ord`. -/
def start (N : LinkNetwork) (ord : List ℕ) : State := ⟨N, ord, [], [], init N.g.n⟩

/-- **One step**: take the next link and merge its two ends in the union-find; keep the link when
the merge answers yes, skip it when the two were already together. -/
def step (N : LinkNetwork) (st : State) : State :=
  match st.rest with
  | [] => st
  | i :: r =>
    if (st.uf.union (N.ends i).1 (N.ends i).2).2 then
      ⟨st.net, r, st.kept ++ [i], st.tried ++ [i], (st.uf.union (N.ends i).1 (N.ends i).2).1⟩
    else ⟨st.net, r, st.kept, st.tried ++ [i], (st.uf.union (N.ends i).1 (N.ends i).2).1⟩

/-- **The walk**: the kept link ids, in the order kept, at most one step per link. -/
def kruskal (N : LinkNetwork) : List ℕ :=
  (runSteps (step N) N.g.links.length (start N (order N))).kept

/-! ## The order -/

instance (N : LinkNetwork) : Std.Total (LinkLe N) :=
  ⟨fun i j => by unfold LinkLe; omega⟩

instance (N : LinkNetwork) : IsTrans ℕ (LinkLe N) :=
  ⟨fun i j k => by unfold LinkLe; omega⟩

/-- **The library's order takes the links cheapest first.** -/
theorem cheapestFirst_order (N : LinkNetwork) : CheapestFirst N (order N) :=
  ⟨List.perm_insertionSort _ _, (List.pairwise_insertionSort (LinkLe N) _).imp fun h => by
    rcases h with h | h <;> omega⟩

/-! ## Running steps -/

theorem step_rest (N : LinkNetwork) (st : State) : (step N st).rest = st.rest.tail := by
  unfold step
  split
  · simp_all
  · split <;> simp_all

/-- **A step keeps the walk's network.** -/
@[simp] theorem step_net (N : LinkNetwork) (st : State) : (step N st).net = st.net := by
  unfold step
  split
  · rfl
  · split <;> rfl

/-- What every step from a state with a link left keeps holds after any number of steps. -/
theorem runSteps_induct {step : State → State} {P : State → Prop}
    (h : ∀ st, P st → st.rest ≠ [] → P (step st)) :
    ∀ f st, P st → P (runSteps step f st)
  | 0, _, hst => hst
  | f + 1, st, hst => by
    unfold runSteps
    split
    · exact hst
    · rename_i hc
      exact runSteps_induct h f _ (h st hst fun he => hc (Or.inl he))

/-- After as many steps as there are links left, none is left, or one group is. -/
theorem runSteps_done (N : LinkNetwork) :
    ∀ f st, st.rest.length ≤ f →
      (runSteps (step N) f st).rest = [] ∨ (runSteps (step N) f st).uf.count = 1
  | 0, st, h => Or.inl (by simp only [runSteps]; exact List.eq_nil_of_length_eq_zero (by omega))
  | f + 1, st, h => by
    unfold runSteps
    split
    · assumption
    · refine runSteps_done N f _ ?_
      rw [step_rest, List.length_tail]
      omega

/-! ## The invariants the merges keep -/

/-- Every piece of `Valid` and `WellFormed` but box invariant 1. -/
def Tracked (st : State) : Prop :=
  GroupsAreKeptJoins st ∧ UnionFindReady st ∧ KeptClosesNoCycle st ∧
    RestCheapestFirst st ∧ PassedAreJoined st

theorem ends_lt {N : LinkNetwork} (hN : N.WellFormed) {i : ℕ} (hi : i < N.g.links.length) :
    (N.ends i).1 < N.g.n ∧ (N.ends i).2 < N.g.n := by
  rw [ends_of_lt hi]
  exact hN.1 _ (List.getElem_mem hi)

theorem tracked_start {N : LinkNetwork} {ord : List ℕ} (hord : CheapestFirst N ord) :
    Tracked (start N ord) := by
  have hroot : ∀ k, (init N.g.n).root k = k := fun k => root_of_isRoot rfl
  refine ⟨fun u _ v _ => ?_, ⟨valid_init _, wellFormed_init _, rfl⟩,
    ⟨by simp [start], by simp [start, ClosesNoCycle]⟩,
    ⟨fun i hi => List.mem_range.1 (hord.1.mem_iff.1 hi), hord.2⟩, fun i hi hn => ?_⟩
  · change (init N.g.n).root u = (init N.g.n).root v ↔ Joined [] u v
    rw [hroot, hroot, joined_nil_iff]
  · exact absurd (hord.1.mem_iff.2 (List.mem_range.2 hi)) hn

/-- **A step keeps every piece but box invariant 1.** The merge answers yes exactly when the kept
links do not join the link's ends; then the groups and the kept links' joins grow alike, and
otherwise neither changes. -/
theorem tracked_step {st : State} (hN : st.net.WellFormed) (h : Tracked st)
    {i : ℕ} {r : List ℕ} (hr : st.rest = i :: r) : Tracked (step st.net st) := by
  set N := st.net with hNdef
  obtain ⟨hg, ⟨hu, hw, hun⟩, ⟨hkl, hkc⟩, ⟨hrl, hrp⟩, hp⟩ := h
  have hi : i < N.g.links.length := hrl i (by simp [hr])
  obtain ⟨hx, hy⟩ := ends_lt hN hi
  set x := (N.ends i).1
  set y := (N.ends i).2
  have hspec := union_spec hu hw (hun ▸ hx) (hun ▸ hy)
  have hrl' : RestCheapestFirst ⟨N, r, [], [], st.uf⟩ :=
    ⟨fun j hj => hrl j (by simp [hr, hj]), (hr ▸ hrp).of_cons⟩
  unfold step
  rw [hr]
  dsimp only
  split
  · rename_i hyes
    have hxy : ¬ N.Joins st.kept x y := fun h => hspec.answer.1 hyes ((hg x hx y hy).2 h)
    refine ⟨fun u hu' v hv => ?_, ⟨(valid_union hu hw (hun ▸ hx) (hun ▸ hy)).1,
      (valid_union hu hw (hun ▸ hx) (hun ▸ hy)).2, hspec.n_eq.trans hun⟩,
      ⟨fun j hj => ?_, ?_⟩, hrl', fun j hj hjr => ?_⟩
    · change (st.uf.union x y).1.Same u v ↔ N.Joins (st.kept ++ [i]) u v
      rw [hspec.groups u (hun ▸ hu') v (hun ▸ hv), joins_append_singleton, joins_cons_iff,
        hg u hu' v hv, hg u hu' x hx, hg v hv y hy, hg u hu' y hy, hg v hv x hx]
      exact or_congr_right (or_congr (and_congr_right fun _ => ⟨Joins.symm, Joins.symm⟩)
        (and_congr_right fun _ => ⟨Joins.symm, Joins.symm⟩))
    · rcases List.mem_append.1 hj with hj | hj
      · exact hkl j hj
      · rw [List.mem_singleton.1 hj]; exact hi
    · exact (closesNoCycle_perm (List.perm_append_singleton _ _)).2
        (closesNoCycle_cons_iff.2 ⟨hxy, hkc⟩)
    · change N.Joins (st.kept ++ [i]) _ _
      by_cases hji : j = i
      · subst hji; exact joins_of_mem (by simp)
      · exact joins_mono (fun k hk => List.mem_append_left _ hk)
          (hp j hj (by simp [hr, hji, hjr]))
  · rename_i hno
    have hxy : st.uf.Same x y := by
      by_contra h; exact hno (hspec.answer.2 h)
    refine ⟨fun u hu' v hv => ?_, ⟨(valid_union hu hw (hun ▸ hx) (hun ▸ hy)).1,
      (valid_union hu hw (hun ▸ hx) (hun ▸ hy)).2, hspec.n_eq.trans hun⟩,
      ⟨hkl, hkc⟩, hrl', fun j hj hjr => ?_⟩
    · change (st.uf.union x y).1.Same u v ↔ N.Joins st.kept u v
      rw [hspec.groups u (hun ▸ hu') v (hun ▸ hv), ← hg u hu' v hv]
      refine ⟨fun h => ?_, Or.inl⟩
      rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h
      · exact h1.trans (hxy.trans h2.symm)
      · exact h1.trans (hxy.symm.trans h2.symm)
    · by_cases hji : j = i
      · subst hji; exact (hg x hx y hy).1 hxy
      · exact hp j hj (by simp [hr, hji, hjr])

/-- **A step keeps box invariant 1: the cut property.** A kept link's ends are in two groups; the
kept links of one of them form a cut no kept link crosses, and the link is a cheapest one across
it, since every cheaper link was taken before it and its ends are joined. So it is exchanged into
some cheapest spanning forest that holds the kept links (`exchange`). -/
theorem partOfCheapest_step {st : State} (hN : st.net.WellFormed)
    (h1 : PartOfCheapest st) (h : Tracked st) {i : ℕ} {r : List ℕ} (hr : st.rest = i :: r) :
    PartOfCheapest (step st.net st) := by
  set N := st.net with hNdef
  obtain ⟨T, hT, hK⟩ := h1
  obtain ⟨hg, ⟨hu, hw, hun⟩, -, ⟨hrl, hrp⟩, hp⟩ := h
  have hi : i < N.g.links.length := hrl i (by simp [hr])
  obtain ⟨hx, hy⟩ := ends_lt hN hi
  have hspec := union_spec hu hw (hun ▸ hx) (hun ▸ hy)
  unfold step
  rw [hr]
  dsimp only
  split
  · rename_i hyes
    have hxy : ¬ N.Joins st.kept (N.ends i).1 (N.ends i).2 :=
      fun h => hspec.answer.1 hyes ((hg _ hx _ hy).2 h)
    by_cases hiT : i ∈ T
    · exact ⟨T, hT, fun j hj => by
        rcases List.mem_append.1 hj with hj | hj
        · exact hK j hj
        · rwa [List.mem_singleton.1 hj]⟩
    obtain ⟨f, hfT, -, hfj, hT', hKf⟩ := exchange hT.1 hK hi hiT hxy
    -- `f` was not taken yet, since the kept links do not join its ends: it comes after `i`
    have hfr : f ∈ r := by
      have hfm : f ∈ st.rest := by
        by_contra hn; exact hfj (hp f (hT.1.1 f hfT) hn)
      rw [hr] at hfm
      rcases List.mem_cons.1 hfm with rfl | hfm
      · exact absurd hfT hiT
      · exact hfm
    have hcost : N.linkCost i ≤ N.linkCost f := 
      List.rel_of_pairwise_cons (R := fun a b => N.linkCost a ≤ N.linkCost b) (hr ▸ hrp) hfr
    have htot := total_cons_erase hfT i (N := N)
    refine ⟨i :: T.erase f, ⟨hT', fun F' hF' => ?_⟩, fun j hj => ?_⟩
    · have : N.total T ≤ N.total F' := hT.2 F' hF'
      change N.total (i :: T.erase f) ≤ N.total F'
      omega
    · rcases List.mem_append.1 hj with hj | hj
      · exact List.mem_cons_of_mem _ (hKf j hj)
      · rw [List.mem_singleton.1 hj]; exact List.mem_cons_self
  · exact ⟨T, hT, hK⟩

/-! ## The walk's answer -/

/-- A finished walk's kept links are a spanning forest: they join the ends of every link, either
because every link was taken or because one group is left. -/
theorem isSpanningForest_of_done {st : State} (hN : st.net.WellFormed)
    (h : Tracked st) (hd : st.rest = [] ∨ st.uf.count = 1) : st.net.IsSpanningForest st.kept := by
  set N := st.net with hNdef
  obtain ⟨hg, ⟨hu, hw, hun⟩, ⟨hkl, hkc⟩, -, hp⟩ := h
  refine ⟨hkl, joinsWhatGraphJoins_iff.2 fun j hj => ?_, hkc⟩
  rcases hd with hd | hd
  · exact hp j hj (by simp [hd])
  · obtain ⟨hx, hy⟩ := ends_lt hN hj
    exact (hg _ hx _ hy).1 (same_of_count_eq_one hu hw hd (hun ▸ hx) (hun ▸ hy))

/-- **The walk keeps its network.** -/
theorem net_runSteps (N : LinkNetwork) (f : ℕ) (st : State) :
    (runSteps (step N) f st).net = st.net :=
  runSteps_induct (P := fun st' => st'.net = st.net) (fun _ h _ => (step_net _ _).trans h) f st
    rfl

theorem tracked_run {N : LinkNetwork} (hN : N.WellFormed) {ord : List ℕ}
    (hord : CheapestFirst N ord) (f : ℕ) : Tracked (runSteps (step N) f (start N ord)) :=
  (runSteps_induct (P := fun st => st.net = N ∧ Tracked st) (fun st h hr => by
    obtain ⟨i, r, hir⟩ := List.exists_cons_of_ne_nil hr
    obtain ⟨rfl, h⟩ := h
    exact ⟨step_net _ _, tracked_step hN h hir⟩) f _ ⟨rfl, tracked_start hord⟩).2

/-- The links taken cheapest first, the walk finishes in as many steps as there are links. -/
theorem done_run (N : LinkNetwork) {ord : List ℕ} (hord : CheapestFirst N ord) :
    (runSteps (step N) N.g.links.length (start N ord)).rest = [] ∨
      (runSteps (step N) N.g.links.length (start N ord)).uf.count = 1 :=
  runSteps_done N _ _ (by simp [start, hord.1.length_eq])

/-- **Some cheapest spanning forest exists**: the walk's answer is a spanning forest. -/
theorem exists_cheapestForest_of {N : LinkNetwork} (hN : N.WellFormed) :
    ∃ T, N.CheapestForest T := by
  have hn : (runSteps (step N) N.g.links.length (start N (order N))).net = N := net_runSteps N _ _
  have h := isSpanningForest_of_done (by rw [hn]; exact hN)
    (tracked_run hN (cheapestFirst_order N) _)
    (done_run N (cheapestFirst_order N))
  rw [hn] at h
  exact exists_cheapestForest h

/-- **The start is legal.** -/
theorem valid_start {N : LinkNetwork} (hN : N.WellFormed) {ord : List ℕ}
    (hord : CheapestFirst N ord) : Valid (start N ord) := by
  obtain ⟨T, hT⟩ := exists_cheapestForest_of hN
  exact ⟨⟨T, hT, by simp [start]⟩, (tracked_start hord).1⟩

/-- **The start is well formed.** -/
theorem wellFormed_start {N : LinkNetwork} {ord : List ℕ} (hord : CheapestFirst N ord) :
    WellFormed (start N ord) :=
  (tracked_start hord).2

/-- **A step with a link left keeps the walk legal.** -/
theorem valid_step {N : LinkNetwork} (hN : N.WellFormed) {st : State} (hnet : st.net = N)
    (h : Valid st) (hw : WellFormed st) (hr : st.rest ≠ []) : Valid (step N st) := by
  subst hnet
  obtain ⟨i, r, hir⟩ := List.exists_cons_of_ne_nil hr
  exact ⟨partOfCheapest_step hN h.1 ⟨h.2, hw⟩ hir, (tracked_step hN ⟨h.2, hw⟩ hir).1⟩

/-- **A step with a link left keeps the walk well formed.** -/
theorem wellFormed_step {N : LinkNetwork} (hN : N.WellFormed) {st : State} (hnet : st.net = N)
    (h : Valid st) (hw : WellFormed st) (hr : st.rest ≠ []) : WellFormed (step N st) := by
  subst hnet
  obtain ⟨i, r, hir⟩ := List.exists_cons_of_ne_nil hr
  exact (tracked_step hN ⟨h.2, hw⟩ hir).2

/-- **`Valid` and `WellFormed` together are the six pieces the walk keeps**, the box's two and
the four the walk needs beyond it. -/
theorem valid_and_wellFormed_iff (st : State) :
    Valid st ∧ WellFormed st ↔ PartOfCheapest st ∧ GroupsAreKeptJoins st ∧ UnionFindReady st ∧
      KeptClosesNoCycle st ∧ RestCheapestFirst st ∧ PassedAreJoined st :=
  and_assoc

/-- **For every order that takes the links cheapest first, the walk's kept links are a cheapest
spanning forest**, however the order breaks ties between equal costs. -/
theorem run_cheapestForest {N : LinkNetwork} (hN : N.WellFormed) {ord : List ℕ}
    (hord : CheapestFirst N ord) :
    N.CheapestForest (runSteps (step N) N.g.links.length (start N ord)).kept := by
  have hv := runSteps_induct (P := fun st => st.net = N ∧ Valid st ∧ WellFormed st)
    (fun st ⟨hn, h, hw⟩ hr => ⟨(step_net _ _).trans hn, valid_step hN hn h hw hr,
      wellFormed_step hN hn h hw hr⟩) N.g.links.length _
    ⟨rfl, valid_start hN hord, wellFormed_start hord⟩
  obtain ⟨hn, ⟨⟨T, hT, hK⟩, hg⟩, hw⟩ := hv
  obtain ⟨hl, hj, hc⟩ := isSpanningForest_of_done (by rw [hn]; exact hN) ⟨hg, hw⟩ (done_run N hord)
  rw [hn] at hT hl hj hc
  exact cheapestForest_of_part hT hK hj hc

/-- **The library's walk gives a cheapest spanning forest.** -/
theorem kruskal_cheapestForest {N : LinkNetwork} (hN : N.WellFormed) :
    N.CheapestForest (kruskal N) :=
  run_cheapestForest hN (cheapestFirst_order N)

/-! ## The cost -/

/-- **Each link is given to the union-find at most once**: the links tried, then the links left,
are the order the walk started with. -/
theorem kruskal_cost (N : LinkNetwork) :
    (runSteps (step N) N.g.links.length (start N (order N))).tried.Nodup ∧
      (runSteps (step N) N.g.links.length (start N (order N))).tried.length ≤
        N.g.links.length := by
  have h := runSteps_induct (P := fun st => st.tried ++ st.rest = order N) (step := step N)
    (fun st h hr => by
      obtain ⟨i, r, hir⟩ := List.exists_cons_of_ne_nil hr
      unfold step
      rw [hir]
      dsimp only
      split <;> simp [← h, hir]) N.g.links.length (start N (order N)) (by simp [start])
  have hnd : (order N).Nodup := (cheapestFirst_order N).1.nodup_iff.2 List.nodup_range
  have hlen : (order N).length = N.g.links.length := (cheapestFirst_order N).1.length_eq.trans
    List.length_range
  rw [← h] at hnd
  have hl := congrArg List.length h
  rw [List.length_append, hlen] at hl
  exact ⟨hnd.of_append_left, by omega⟩

end AlgoDesign.Paths.Kruskal
