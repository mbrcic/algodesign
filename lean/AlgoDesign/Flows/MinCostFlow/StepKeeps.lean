/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MinCostFlow.Steps
public import AlgoDesign.Flows.MinCostFlow.Walk
public import AlgoDesign.Flows.MinCostFlow.Cheapest

/-!
# Cheapest flow of a given amount: one step keeps the heights fitting

Source: Ahuja, Magnanti and Orlin, *Network Flows* (1993), §9.7, Lemma 9.11 (p. 321) and the
heights after a search stopped at the sink (p. 323).

The search's network has an arrow for each residual arrow with room, costing its changed cost;
under fitting heights none is below 0, so chapter 6's walk applies. When it settles the sink, the
path back from the sink follows the recorded arrows; each is an arrow with room whose changed cost
is the difference of the known costs at its ends, both settled (`OnPath`, `trace`). The heights
after the step keep every arrow with room at a changed cost of at least zero (`raise_fit`): the
arrows of the path just used get changed cost zero, so their ways back do too. When the search
does not settle the sink, no path with room leads there (`step_none`).
-/

@[expose] public section

namespace AlgoDesign.Flows.MinCostFlow

variable {P : Problem} {f : Flow} {h : Heights}

/-! ## The search's network -/

theorem residual_endpoints_lt {N : Network} (hN : N.WellFormed) {a : ResidualArrow}
    (ha : a.id < N.g.arrows.length) : a.tail N < N.g.n ∧ a.head N < N.g.n := by
  have := Network.endpoints_lt hN ha
  cases a <;> simp only [ResidualArrow.id, ResidualArrow.tail, ResidualArrow.head] at this ha ⊢ <;>
    omega

theorem mem_roomy {N : Network} {a : ResidualArrow} :
    a ∈ roomy N f ↔ a.id < N.g.arrows.length ∧ 0 < a.residualCapacity N f := by
  cases a <;> simp [roomy, Network.ids, ResidualArrow.id]

theorem searchNet_arrow {j u w : ℕ} :
    (searchNet P f h).g.arrows[j]? = some (u, w) ↔
      ∃ a, (roomy P.net f)[j]? = some a ∧ a.tail P.net = u ∧ a.head P.net = w := by
  simp [searchNet, List.getElem?_map]

theorem searchNet_cost {j : ℕ} {a : ResidualArrow} (ha : (roomy P.net f)[j]? = some a) :
    (searchNet P f h).arrowCost j = changedCost P h a := by
  simp [searchNet, Paths.Network.arrowCost, List.getD_eq_getElem?_getD, List.getElem?_map, ha]

theorem searchNet_wellFormed (hN : P.net.WellFormed) : (searchNet P f h).WellFormed := by
  refine ⟨fun x hx => ?_, by simp [searchNet]⟩
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact residual_endpoints_lt hN (mem_roomy.1 ha).1

theorem searchNet_noArrowBelowZero (hfit : HeightsFitEverywhere ⟨P, f, h⟩) :
    (searchNet P f h).NoArrowBelowZero := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  exact hfit a (mem_roomy.1 ha).1 (mem_roomy.1 ha).2

/-- An arrow with room is an arrow of the search's network, at its changed cost. -/
theorem searchNet_of_residualCapacity {a : ResidualArrow} (ha : a.id < P.net.g.arrows.length)
    (hr : 0 < a.residualCapacity P.net f) : ∃ j, (searchNet P f h).g.arrows[j]? =
      some (a.tail P.net, a.head P.net) ∧ (searchNet P f h).arrowCost j = changedCost P h a := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (mem_roomy.2 ⟨ha, hr⟩)
  exact ⟨j, searchNet_arrow.2 ⟨a, hj, rfl, rfl⟩, searchNet_cost hj⟩

/-- A path with room from `u` to `v` is a way from `u` to `v` in the search's network. -/
theorem searchNet_reaches : ∀ {p : List ResidualArrow} {u v : ℕ}, ends P.net u p = some v →
    (∀ a ∈ p, 0 < a.residualCapacity P.net f) → (searchNet P f h).g.Reaches u v
  | [], u, v, he, _ => by
    simp only [ends, Option.some.injEq] at he
    subst he; exact Relation.ReflTransGen.refl
  | a :: p, u, v, he, hr => by
    simp only [ends] at he
    split_ifs at he with ha
    refine Relation.ReflTransGen.head ?_ (searchNet_reaches he fun b hb => hr b (by simp [hb]))
    rw [← ha.2]
    exact List.mem_map.2 ⟨a, mem_roomy.2 ⟨ha.1, hr a (by simp)⟩, rfl⟩

/-! ## The path back from the sink -/

/-- What each arrow of the path back satisfies: an arrow with room between two settled vertices,
whose changed cost is the difference of their known costs. -/
def OnPath (P : Problem) (f : Flow) (h : Heights) (st : Paths.Dijkstra.State)
    (r : ResidualArrow) : Prop :=
  r.id < P.net.g.arrows.length ∧ 0 < r.residualCapacity P.net f ∧ r.tail P.net ∈ st.settled ∧
    r.head P.net ∈ st.settled ∧
    changedCost P h r = dist st (r.head P.net) - dist st (r.tail P.net)

/-- The arrow recorded into a settled vertex with a previous vertex exists, and is on the path. -/
theorem viaOf_some {st : Paths.Dijkstra.State} (hnet : st.net = searchNet P f h)
    (htight : PreviousTight st) {a b : ℕ} (hprev : st.prev b = some a)
    (hb : b ∈ st.settled) :
    ∃ r, viaOf P f h st b = some r ∧ r.tail P.net = a ∧ r.head P.net = b ∧ OnPath P f h st r := by
  obtain ⟨ha, da, db, i, hda, hdb, hi, hd⟩ := htight b a hprev
  rw [hnet] at hi hd
  obtain ⟨c, hc, hct, hch⟩ := searchNet_arrow.1 hi
  rw [searchNet_cost hc] at hd
  obtain ⟨hcid, hcr⟩ := mem_roomy.1 (List.mem_of_getElem? hc)
  have hdist : dist st b - dist st a = changedCost P h c := by
    simp only [dist, hda, hdb, Option.getD_some]; omega
  have hsome : (arrowInto P f h st a b).isSome := by
    refine List.find?_isSome.2 ⟨c, mem_residualOut.2 ⟨hcid, hct⟩, ?_⟩
    simp [hch, hcr, hdist]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
  have hp := List.find?_some hr
  have hm := mem_residualOut.1 (List.mem_of_find?_eq_some hr)
  simp only [decide_eq_true_eq] at hp
  refine ⟨r, by simp [viaOf, hprev, hr], hm.2, hp.1, hm.1, hp.2.1, ?_, ?_, ?_⟩
  · rw [hm.2]; exact ha
  · rw [hp.1]; exact hb
  · rw [hp.2.2, hp.1, hm.2]

/-- **Following the recorded arrows back** along a chain of previous vertices from the source,
ending at a settled vertex, gives a path from the source along that chain, every arrow of it on
the path. -/
theorem trace {st : Paths.Dijkstra.State} (hnet : st.net = searchNet P f h)
    (htight : PreviousTight st) :
    ∀ xs : List ℕ, (P.net.source :: xs).IsChain (fun a b => st.prev b = some a) →
      (P.net.source :: xs).Nodup → (P.net.source :: xs).getLast (by simp) ∈ st.settled →
      ∀ k, xs.length ≤ k → ∀ acc, ∃ rs,
        pathBack P.net (viaOf P f h st) k ((P.net.source :: xs).getLast (by simp)) acc =
          some (rs ++ acc) ∧
        ends P.net P.net.source rs = some ((P.net.source :: xs).getLast (by simp)) ∧
        visits P.net P.net.source rs = P.net.source :: xs ∧ ∀ r ∈ rs, OnPath P f h st r := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro _ _ _ k _ acc
    refine ⟨[], ?_, by simp [ends], by simp [visits], by simp⟩
    cases k <;> simp [pathBack]
  | append_singleton ys v ih =>
    intro hc hn hv k hk acc
    have hlast : (P.net.source :: (ys ++ [v])).getLast (by simp) = v := by
      rw [List.getLast_cons (by simp), List.getLast_append_singleton]
    rw [hlast] at hv ⊢
    rw [← List.cons_append] at hc hn
    obtain ⟨hc1, -, hc3⟩ := List.isChain_append.1 hc
    have hu := List.getLast?_eq_some_getLast (l := P.net.source :: ys) (by simp)
    have hprev : st.prev v = some ((P.net.source :: ys).getLast (by simp)) :=
      hc3 _ (by rw [hu]; rfl) v (by simp)
    have hn' := List.nodup_append.1 hn
    have hvs : v ≠ P.net.source := fun e => hn'.2.2 P.net.source (by simp) v (by simp) e.symm
    obtain ⟨r, hr, hrt, hrh, hon⟩ := viaOf_some hnet htight hprev hv
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    obtain ⟨rs, h1, h2, h3, h4⟩ := ih hc1 hn'.1 (hrt ▸ hon.2.2.1) k (by simp at hk; omega)
      (r :: acc)
    refine ⟨rs ++ [r], ?_, ?_, ?_, ?_⟩
    · simp only [pathBack, hvs, ite_false, hr]
      rw [hrt, h1]; simp
    · rw [← hrh]; exact ends_append_one P.net r rs _ _ h2 hon.1 hrt
    · rw [visits_append_one, h3, hrh]; simp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h4 x hx
      · rw [List.mem_singleton.1 hx]; exact hon

/-- **When the search settles the sink, the path back is found**: a path from the source to the
sink, passing no vertex twice, every arrow of it on the path. -/
theorem found (hP : P.WellFormed) (hfit : HeightsFitEverywhere ⟨P, f, h⟩)
    (ht : P.net.sink ∈ (search P f h).settled) :
    ∃ rs, pathBack P.net (viaOf P f h (search P f h)) P.net.g.n P.net.sink [] = some rs ∧
      ends P.net P.net.source rs = some P.net.sink ∧ (visits P.net P.net.source rs).Nodup ∧
      ∀ r ∈ rs, OnPath P f h (search P f h) r := by
  have hW := searchNet_wellFormed (f := f) (h := h) hP.1
  have hnn := searchNet_noArrowBelowZero hfit
  have hs : P.net.source < (searchNet P f h).g.n := hP.1.2.2.1
  obtain ⟨dt, hdt, -, -, htight, hnet⟩ := goal_settled hW hnn hs ht
  obtain ⟨q, hq, -, hl⟩ :=
    Paths.Dijkstra.dijkstraTo_previous hs P.net.sink hP.1.2.2.2.1 dt hdt
  set xs := q.map (searchNet P f h).target
  have hvis : (searchNet P f h).visits P.net.source q = P.net.source :: xs := rfl
  have hlast : (P.net.source :: xs).getLast (by simp) = P.net.sink := by
    have := hq.visits_eq
    rw [hvis] at this
    rw [List.getLast_congr _ (by simp) this]; simp
  have hnd : (P.net.source :: xs).Nodup := hvis ▸ hq.2
  have hlen : xs.length ≤ P.net.g.n := by
    have := hnd.length_le_of_subset (l₂ := List.range P.net.g.n) fun y hy =>
      List.mem_range.2 (hq.lt_of_mem hW hs (hvis ▸ hy))
    simp at this; omega
  have hc := hl.2
  rw [hvis] at hc
  obtain ⟨rs, h1, h2, h3, h4⟩ := trace hnet htight xs hc hnd (by rw [hlast]; exact ht) _ hlen []
  rw [hlast] at h1 h2
  simp only [List.append_nil] at h1
  exact ⟨rs, h1, h2, h3 ▸ hnd, h4⟩

/-! ## The heights after a step -/

/-- What a vertex's height rises by: its own known cost if settled, the sink's otherwise. -/
def rise (P : Problem) (st : Paths.Dijkstra.State) (v : ℕ) : ℤ :=
  if v ∈ st.settled then dist st v else dist st P.net.sink

theorem rise_mem {st : Paths.Dijkstra.State} {v : ℕ} {d : ℤ} (hv : v ∈ st.settled)
    (hd : st.known v = some d) : rise P st v = d := by
  simp [rise, hv, dist, hd]

theorem rise_not_mem {st : Paths.Dijkstra.State} {v : ℕ} {d : ℤ} (hv : v ∉ st.settled)
    (hd : st.known P.net.sink = some d) : rise P st v = d := by
  simp [rise, hv, dist, hd]

theorem raise_at (st : Paths.Dijkstra.State) {v : ℕ} (hv : v < P.net.g.n) :
    (raise P h st).at v = h.at v + rise P st v := by
  simp [raise, rise, Heights.at, List.getD_eq_getElem?_getD, hv]

theorem changedCost_raise (hN : P.net.WellFormed) (st : Paths.Dijkstra.State)
    {a : ResidualArrow} (ha : a.id < P.net.g.arrows.length) :
    changedCost P (raise P h st) a =
      changedCost P h a + rise P st (a.tail P.net) - rise P st (a.head P.net) := by
  obtain ⟨h1, h2⟩ := residual_endpoints_lt hN ha
  simp only [changedCost, raise_at st h1, raise_at st h2]
  ring

/-- **Every arrow with room before the step keeps a changed cost of at least zero under the
heights after it.** -/
theorem raise_fit_residualCapacity (hP : P.WellFormed) (hfit : HeightsFitEverywhere ⟨P, f, h⟩)
    (ht : P.net.sink ∈ (search P f h).settled) {a : ResidualArrow}
    (ha : a.id < P.net.g.arrows.length) (hr : 0 < a.residualCapacity P.net f) :
    0 ≤ changedCost P (raise P h (search P f h)) a := by
  have hW := searchNet_wellFormed (f := f) (h := h) hP.1
  have hnn := searchNet_noArrowBelowZero hfit
  have hs : P.net.source < (searchNet P f h).g.n := hP.1.2.2.1
  obtain ⟨dt, hdt, hA, hB, -, -⟩ := goal_settled hW hnn hs ht
  obtain ⟨j, hj, hcj⟩ := searchNet_of_residualCapacity (h := h) ha hr
  have hc0 := hfit a ha hr
  simp only at hc0
  rw [changedCost_raise hP.1 _ ha]
  unfold search
  by_cases hu : a.tail P.net ∈ (Paths.Dijkstra.finalTo (searchNet P f h) P.net.source
    P.net.sink).settled <;>
    by_cases hv : a.head P.net ∈ (Paths.Dijkstra.finalTo (searchNet P f h) P.net.source
      P.net.sink).settled
  · obtain ⟨du, hdu, -⟩ := hA _ hu
    obtain ⟨dv, hdv, -⟩ := hA _ hv
    have := (hB _ hu _ j hj du hdu).1 dv hdv hv
    rw [rise_mem hu hdu, rise_mem hv hdv]
    linarith
  · obtain ⟨du, hdu, -⟩ := hA _ hu
    have := (hB _ hu _ j hj du hdu).2 hv
    rw [rise_mem hu hdu, rise_not_mem hv hdt]
    linarith
  · obtain ⟨dv, hdv, hle⟩ := hA _ hv
    rw [rise_not_mem hu hdt, rise_mem hv hdv]
    linarith
  · rw [rise_not_mem hu hdt, rise_not_mem hv hdt]
    linarith

/-- An arrow on the path has changed cost zero under the heights after the step. -/
theorem raise_onPath (hN : P.net.WellFormed) {r : ResidualArrow}
    (hr : OnPath P f h (search P f h) r) : changedCost P (raise P h (search P f h)) r = 0 := by
  rw [changedCost_raise hN _ hr.1]
  simp only [rise, hr.2.2.1, hr.2.2.2.1, ite_true, hr.2.2.2.2]
  ring

/-- The two residual arrows of one arrow of the network, under any heights, have opposite
changed costs. -/
theorem changedCost_partner (P : Problem) (h : Heights) {a b : ResidualArrow} (he : a.id = b.id)
    (hne : a ≠ b) : changedCost P h b = -changedCost P h a := by
  cases a <;> cases b <;> simp only [ResidualArrow.id] at he <;> subst he
  · exact absurd rfl hne
  · exact changedCost_back P h _
  · rw [changedCost_back]; ring
  · exact absurd rfl hne

/-- **The heights after a step fit the flow after it.** -/
theorem raise_fit (hP : P.WellFormed) (hf : IsFlow P.net f)
    (hfit : HeightsFitEverywhere ⟨P, f, h⟩) (ht : P.net.sink ∈ (search P f h).settled)
    {rs : List ResidualArrow} (hon : ∀ r ∈ rs, OnPath P f h (search P f h) r) (x : ℕ) :
    HeightsFitEverywhere ⟨P, (⟨rs, x⟩ : Augmentation).apply f, raise P h (search P f h)⟩ := by
  intro b hb hroom
  simp only at hb hroom ⊢
  by_cases hm : b.id ∈ rs.map (·.id)
  · obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
    by_cases hab : a = b
    · subst hab
      exact raise_fit_residualCapacity hP hfit ht hb (hon a ha).2.1
    · rw [changedCost_partner P _ he hab, raise_onPath hP.1 (hon a ha)]
      simp
  · have hl : ∀ c ∈ (⟨rs, x⟩ : Augmentation).path, c.id < f.length := fun c hc => by
      rw [hf.2.2]; exact (hon c hc).1
    rw [residualCapacity_apply_not_mem P.net hl hm] at hroom
    exact raise_fit_residualCapacity hP hfit ht hb hroom

/-! ## One step -/

/-- **A step sends along an augmenting path an amount that fits it, at least one unit and no more
than is left, and the heights after it fit the flow after it.** -/
theorem step_some (hP : P.WellFormed) (hf : IsFlow P.net f)
    (hfit : HeightsFitEverywhere ⟨P, f, h⟩) {left : ℕ} (hl : 0 < left) {r : RoundRecord}
    (hr : step P left f h = some r) :
    (IsAugmentingPath P.net f r.sent.path ∧
      ∀ a ∈ r.sent.path, r.sent.amount ≤ a.residualCapacity P.net f) ∧
      1 ≤ r.sent.amount ∧ r.sent.amount ≤ left ∧
      HeightsFitEverywhere ⟨P, r.sent.apply f, r.heights⟩ := by
  unfold step at hr
  simp only at hr
  split_ifs at hr with ht
  obtain ⟨rs, h1, h2, h3, h4⟩ := found hP hfit ht
  rw [h1] at hr
  simp only [Option.some.injEq] at hr
  subst hr
  have hroom : ∀ a ∈ rs, 0 < a.residualCapacity P.net f := fun a ha => (h4 a ha).2.1
  refine ⟨⟨⟨h2, h3, hroom⟩, fun a ha => (min_le_left _ _).trans (bottleneck_le ha)⟩, ?_,
    min_le_right _ _, raise_fit hP hf hfit ht h4 _⟩
  exact le_min (one_le_bottleneck (ne_nil_of_ends hP.1 h2) hroom) hl

/-- **A step that finds nothing means no augmenting path is left.** -/
theorem step_none (hP : P.WellFormed) (hfit : HeightsFitEverywhere ⟨P, f, h⟩) {left : ℕ}
    (hr : step P left f h = none) : ∀ p, ¬ IsAugmentingPath P.net f p := by
  intro p hp
  unfold step at hr
  simp only at hr
  split_ifs at hr with ht
  · obtain ⟨rs, h1, -⟩ := found hP hfit ht
    rw [h1] at hr
    cases hr
  · exact goal_unsettled (searchNet_wellFormed hP.1)
      (searchNet_noArrowBelowZero hfit) hP.1.2.2.1 ht (searchNet_reaches hp.1 hp.2.2)

end AlgoDesign.Flows.MinCostFlow
