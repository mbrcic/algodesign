/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Matching.Spec
public import AlgoDesign.Flows.MaxFlow

/-!
# Matching: the network, and what the last search reads

Source: the Flow chapter, "Who gets the quiet rooms?"; König (1931) and Hall (1935).

Where every arrow of the matching network starts and ends; why a flow on it is a matching (a
person passes on at most the one unit its source arrow brings, an object takes in at most the one
unit its sink arrow passes on); and what the vertices the last search reached say: every person it
did not reach is matched, every object it reached is matched, and a person it reached reaches every
object they accept. From these, the people not reached and the objects reached are a cover as
large as the matching, and when someone stays unmatched the people reached accept fewer objects
than there are of them.
-/

@[expose] public section

namespace AlgoDesign.Flows.Matching

open AlgoDesign.Flows

/-! ## Sums over lists of arrow ids -/

theorem sum_le_of_all_eq {g : ℕ → ℕ} {a : ℕ} :
    ∀ {L : List ℕ}, L.Nodup → (∀ x ∈ L, x = a) → (L.map g).sum ≤ g a
  | [], _, _ => by simp
  | x :: L, hn, h => by
    have hx := h x List.mem_cons_self
    subst hx
    have hL : L = [] := List.eq_nil_iff_forall_not_mem.2 fun y hy =>
      (List.nodup_cons.1 hn).1 (h y (List.mem_cons_of_mem _ hy) ▸ hy)
    simp [hL]

theorem add_le_sum {g : ℕ → ℕ} {a b : ℕ} :
    ∀ {L : List ℕ}, L.Nodup → a ∈ L → b ∈ L → a ≠ b → g a + g b ≤ (L.map g).sum
  | [], _, ha, _, _ => by simp at ha
  | x :: L, hn, ha, hb, hab => by
    have hrest := (List.nodup_cons.1 hn).2
    rcases List.mem_cons.1 ha with ha | ha <;> rcases List.mem_cons.1 hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · have := List.le_sum_of_mem (List.mem_map_of_mem (f := g) hb)
      simp only [List.map_cons, List.sum_cons, ha]
      omega
    · have := List.le_sum_of_mem (List.mem_map_of_mem (f := g) ha)
      simp only [List.map_cons, List.sum_cons, hb]
      omega
    · have := add_le_sum (g := g) hrest ha hb hab
      simp only [List.map_cons, List.sum_cons]
      omega

theorem sum_le_length {g : ℕ → ℕ} : ∀ {L : List ℕ}, (∀ x ∈ L, g x ≤ 1) → (L.map g).sum ≤ L.length
  | [], _ => by simp
  | x :: L, h => by
    have := h x List.mem_cons_self
    have := sum_le_length (g := g) fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-! ## The arrows of the matching network -/

variable {P : Problem}

/-- Pair `j` of the problem. -/
def Problem.pair (P : Problem) (j : ℕ) : ℕ × ℕ := P.pairs.getD j (0, 0)

theorem pair_mem {j : ℕ} (hj : j < P.pairs.length) : P.pair j ∈ P.pairs := by
  simp [Problem.pair, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem pair_lt (hP : P.WellFormed) {j : ℕ} (hj : j < P.pairs.length) :
    (P.pair j).1 < P.people ∧ (P.pair j).2 < P.objects :=
  hP _ (pair_mem hj)

theorem length_arrows : P.network.g.arrows.length = P.people + P.pairs.length + P.objects := by
  simp [Problem.network]; omega

theorem arrow_source {i : ℕ} (hi : i < P.people) :
    P.network.g.arrows.getD i (0, 0) = (0, 1 + i) := by
  simp [Problem.network, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]

theorem arrow_pair {j : ℕ} (hj : j < P.pairs.length) :
    P.network.g.arrows.getD (P.people + j) (0, 0) =
      (1 + (P.pair j).1, 1 + P.people + (P.pair j).2) := by
  simp [Problem.network, Problem.pair, List.getD_eq_getElem?_getD, List.getElem?_append_left,
    List.getElem?_append_right, hj]

theorem arrow_sink {o : ℕ} (ho : o < P.objects) :
    P.network.g.arrows.getD (P.people + P.pairs.length + o) (0, 0) =
      (1 + P.people + o, 1 + P.people + P.objects) := by
  simp only [Problem.network, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  have : P.people + P.pairs.length + o -
      (List.map (fun p => (0, 1 + p)) (List.range P.people)).length -
      (List.map (fun e => (1 + e.1, 1 + P.people + e.2)) P.pairs).length = o := by simp; omega
  rw [this]
  simp [ho]

theorem tail_source {i : ℕ} (hi : i < P.people) : P.network.tail i = 0 := by
  rw [Network.tail, arrow_source hi]

theorem head_source {i : ℕ} (hi : i < P.people) : P.network.head i = 1 + i := by
  rw [Network.head, arrow_source hi]

theorem tail_pair {j : ℕ} (hj : j < P.pairs.length) :
    P.network.tail (P.people + j) = 1 + (P.pair j).1 := by
  rw [Network.tail, arrow_pair hj]

theorem head_pair {j : ℕ} (hj : j < P.pairs.length) :
    P.network.head (P.people + j) = 1 + P.people + (P.pair j).2 := by
  rw [Network.head, arrow_pair hj]

theorem tail_sink {o : ℕ} (ho : o < P.objects) :
    P.network.tail (P.people + P.pairs.length + o) = 1 + P.people + o := by
  rw [Network.tail, arrow_sink ho]

theorem head_sink {o : ℕ} (ho : o < P.objects) :
    P.network.head (P.people + P.pairs.length + o) = 1 + P.people + P.objects := by
  rw [Network.head, arrow_sink ho]

/-- Every arrow is a source arrow, a pair's arrow or a sink arrow. -/
theorem arrow_cases {i : ℕ} (hi : i < P.network.g.arrows.length) :
    i < P.people ∨ (∃ j < P.pairs.length, i = P.people + j) ∨
      ∃ o < P.objects, i = P.people + P.pairs.length + o := by
  rw [length_arrows] at hi
  by_cases h1 : i < P.people
  · exact Or.inl h1
  by_cases h2 : i < P.people + P.pairs.length
  · exact Or.inr (Or.inl ⟨i - P.people, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨i - P.people - P.pairs.length, by omega, by omega⟩)

theorem capOf_eq {i : ℕ} (hi : i < P.network.g.arrows.length) : P.network.capOf i = 1 := by
  rw [length_arrows] at hi
  simp [Network.capOf, Problem.network, List.getD_eq_getElem?_getD, hi]

theorem network_source : P.network.source = 0 := rfl

theorem network_sink : P.network.sink = 1 + P.people + P.objects := rfl

theorem network_n : P.network.g.n = P.people + P.objects + 2 := rfl

/-- The matching network of a well-formed problem is a well-formed network. -/
theorem network_wellFormed (hP : P.WellFormed) : P.network.WellFormed := by
  refine ⟨fun a ha => show a.1 < P.people + P.objects + 2 ∧ a.2 < P.people + P.objects + 2 from ?_,
    by simp [Problem.network]; omega, by simp [Problem.network],
    by simp [Problem.network]; omega, by simp [Problem.network]; omega⟩
  simp only [Problem.network, List.mem_append, List.mem_map, List.mem_range] at ha
  rcases ha with (⟨p, hp, rfl⟩ | ⟨e, he, rfl⟩) | ⟨o, ho, rfl⟩
  · simp; omega
  · have := hP e he
    simp; omega
  · simp; omega

/-! ## Which arrows enter and leave a vertex -/

/-- Only a person's source arrow enters the person. -/
theorem head_eq_person {i p : ℕ} (hi : i < P.network.g.arrows.length)
    (hp : p < P.people) (h : P.network.head i = 1 + p) : i = p := by
  rcases arrow_cases hi with hi | ⟨j, hj, rfl⟩ | ⟨o, ho, rfl⟩
  · rw [head_source hi] at h; omega
  · rw [head_pair hj] at h; omega
  · rw [head_sink ho] at h; omega

/-- Only the arrows of a person's pairs leave the person. -/
theorem tail_eq_person {i p : ℕ} (hi : i < P.network.g.arrows.length)
    (hp : p < P.people) (h : P.network.tail i = 1 + p) :
    ∃ j < P.pairs.length, i = P.people + j ∧ (P.pair j).1 = p := by
  rcases arrow_cases hi with hi | ⟨j, hj, rfl⟩ | ⟨o, ho, rfl⟩
  · rw [tail_source hi] at h; omega
  · rw [tail_pair hj] at h; exact ⟨j, hj, rfl, by omega⟩
  · rw [tail_sink ho] at h; omega

/-- Only the arrows of an object's pairs enter the object. -/
theorem head_eq_object {i o : ℕ} (hi : i < P.network.g.arrows.length)
    (ho : o < P.objects) (h : P.network.head i = 1 + P.people + o) :
    ∃ j < P.pairs.length, i = P.people + j ∧ (P.pair j).2 = o := by
  rcases arrow_cases hi with hi | ⟨j, hj, rfl⟩ | ⟨o', ho', rfl⟩
  · rw [head_source hi] at h; omega
  · rw [head_pair hj] at h; exact ⟨j, hj, rfl, by omega⟩
  · rw [head_sink ho'] at h; omega

/-- Only an object's sink arrow leaves the object. -/
theorem tail_eq_object (hP : P.WellFormed) {i o : ℕ} (hi : i < P.network.g.arrows.length)
    (h : P.network.tail i = 1 + P.people + o) : i = P.people + P.pairs.length + o := by
  rcases arrow_cases hi with hi | ⟨j, hj, rfl⟩ | ⟨o', ho', rfl⟩
  · rw [tail_source hi] at h; omega
  · rw [tail_pair hj] at h; have := (pair_lt hP hj).1; omega
  · rw [tail_sink ho'] at h; omega

/-- Only the source arrows leave the source. -/
theorem tail_eq_source {i : ℕ} (hi : i < P.network.g.arrows.length)
    (h : P.network.tail i = 0) : i < P.people := by
  rcases arrow_cases hi with hi | ⟨j, hj, rfl⟩ | ⟨o, ho, rfl⟩
  · exact hi
  · rw [tail_pair hj] at h; omega
  · rw [tail_sink ho] at h; omega

/-! ## Sums of a flow at a vertex -/

theorem nodup_filter_ids (N : Network) (q : ℕ → Bool) : (N.ids.filter q).Nodup :=
  (List.nodup_range).filter _

theorem mem_filter_ids {N : Network} {i v : ℕ} {e : Network → ℕ → ℕ} :
    i ∈ N.ids.filter (fun i => e N i = v) ↔ i < N.g.arrows.length ∧ e N i = v := by
  simp [Network.ids]

theorem le_outflow {N : Network} (f : Flow) {i : ℕ} (hi : i < N.g.arrows.length) :
    f.on i ≤ outflow N f (N.tail i) :=
  List.le_sum_of_mem (List.mem_map_of_mem (mem_filter_ids.2 ⟨hi, rfl⟩))

theorem le_inflow {N : Network} (f : Flow) {i : ℕ} (hi : i < N.g.arrows.length) :
    f.on i ≤ inflow N f (N.head i) :=
  List.le_sum_of_mem (List.mem_map_of_mem (mem_filter_ids.2 ⟨hi, rfl⟩))

theorem add_le_outflow {N : Network} (f : Flow) {i i' v : ℕ} (hi : i < N.g.arrows.length)
    (hi' : i' < N.g.arrows.length) (hne : i ≠ i') (h : N.tail i = v) (h' : N.tail i' = v) :
    f.on i + f.on i' ≤ outflow N f v :=
  add_le_sum (nodup_filter_ids _ _) (mem_filter_ids.2 ⟨hi, h⟩) (mem_filter_ids.2 ⟨hi', h'⟩) hne

theorem add_le_inflow {N : Network} (f : Flow) {i i' v : ℕ} (hi : i < N.g.arrows.length)
    (hi' : i' < N.g.arrows.length) (hne : i ≠ i') (h : N.head i = v) (h' : N.head i' = v) :
    f.on i + f.on i' ≤ inflow N f v :=
  add_le_sum (nodup_filter_ids _ _) (mem_filter_ids.2 ⟨hi, h⟩) (mem_filter_ids.2 ⟨hi', h'⟩) hne

theorem outflow_eq_zero {N : Network} (f : Flow) {v : ℕ}
    (h : ∀ i < N.g.arrows.length, N.tail i = v → f.on i = 0) : outflow N f v = 0 :=
  List.sum_eq_zero fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i (mem_filter_ids.1 hi).1 (mem_filter_ids.1 hi).2

theorem inflow_eq_zero {N : Network} (f : Flow) {v : ℕ}
    (h : ∀ i < N.g.arrows.length, N.head i = v → f.on i = 0) : inflow N f v = 0 :=
  List.sum_eq_zero fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i (mem_filter_ids.1 hi).1 (mem_filter_ids.1 hi).2

/-- What enters a person is what its source arrow carries. -/
theorem inflow_person_le (f : Flow) {p : ℕ} (hp : p < P.people) :
    inflow P.network f (1 + p) ≤ f.on p :=
  sum_le_of_all_eq (nodup_filter_ids _ _) fun _ hi =>
    head_eq_person (mem_filter_ids.1 hi).1 hp (mem_filter_ids.1 hi).2

/-- What leaves an object is what its sink arrow carries. -/
theorem outflow_object_le (hP : P.WellFormed) (f : Flow) (o : ℕ) :
    outflow P.network f (1 + P.people + o) ≤ f.on (P.people + P.pairs.length + o) :=
  sum_le_of_all_eq (nodup_filter_ids _ _) fun _ hi =>
    tail_eq_object hP (mem_filter_ids.1 hi).1 (mem_filter_ids.1 hi).2

theorem on_le_one {f : Flow} (hf : IsFlow P.network f) {i : ℕ}
    (hi : i < P.network.g.arrows.length) : f.on i ≤ 1 :=
  (hf.1 i hi).trans (capOf_eq hi).le

theorem conserved_person {f : Flow} (hf : IsFlow P.network f) {p : ℕ} (hp : p < P.people) :
    inflow P.network f (1 + p) = outflow P.network f (1 + p) :=
  hf.2.1 _ (by rw [network_n]; omega) (by rw [network_source]; omega)
    (by rw [network_sink]; omega)

theorem conserved_object {f : Flow} (hf : IsFlow P.network f) {o : ℕ} (ho : o < P.objects) :
    inflow P.network f (1 + P.people + o) = outflow P.network f (1 + P.people + o) :=
  hf.2.1 _ (by rw [network_n]; omega) (by rw [network_source]; omega)
    (by rw [network_sink]; omega)

/-- **A person passes on at most one unit**: the one its source arrow brings. -/
theorem outflow_person_le_one {f : Flow} (hf : IsFlow P.network f) {p : ℕ}
    (hp : p < P.people) : outflow P.network f (1 + p) ≤ 1 := by
  rw [← conserved_person hf hp]
  exact (inflow_person_le f hp).trans (on_le_one hf (by rw [length_arrows]; omega))

/-- **An object takes in at most one unit**: the one its sink arrow passes on. -/
theorem inflow_object_le_one (hP : P.WellFormed) {f : Flow} (hf : IsFlow P.network f) {o : ℕ}
    (ho : o < P.objects) : inflow P.network f (1 + P.people + o) ≤ 1 := by
  rw [conserved_object hf ho]
  exact (outflow_object_le hP f o).trans (on_le_one hf (by rw [length_arrows]; omega))

/-! ## An integer flow is a matching -/

/-- **The pairs that carry the unit are a matching.** -/
theorem carried_isMatching (hP : P.WellFormed) {f : Flow} (hf : IsFlow P.network f) :
    IsMatching P (carried P f) := by
  have hJ : ∀ j ∈ (List.range P.pairs.length).filter (fun j => 0 < f.on (P.people + j)),
      j < P.pairs.length ∧ 0 < f.on (P.people + j) := fun j hj => by simpa using hj
  have hlen : ∀ j < P.pairs.length, P.people + j < P.network.g.arrows.length := fun j hj => by
    rw [length_arrows]; omega
  refine ⟨fun e he => ?_, ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    exact pair_mem (hJ j hj).1
  · rw [carried, List.map_map]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_range.filter _)
    have hab' : (P.pair a).1 = (P.pair b).1 := hab
    obtain ⟨ha1, ha2⟩ := hJ a ha
    obtain ⟨hb1, hb2⟩ := hJ b hb
    by_contra hne
    have := add_le_outflow f (hlen a ha1) (hlen b hb1) (by omega) (tail_pair ha1)
      (by rw [tail_pair hb1, hab'])
    have := outflow_person_le_one hf (pair_lt hP ha1).1
    omega
  · rw [carried, List.map_map]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_range.filter _)
    have hab' : (P.pair a).2 = (P.pair b).2 := hab
    obtain ⟨ha1, ha2⟩ := hJ a ha
    obtain ⟨hb1, hb2⟩ := hJ b hb
    by_contra hne
    have := add_le_inflow f (hlen a ha1) (hlen b hb1) (by omega) (head_pair ha1)
      (by rw [head_pair hb1, hab'])
    have := inflow_object_le_one hP hf (pair_lt hP ha1).2
    omega

/-! ## The last search -/

/-- The search adds the end of every arrow with room that leaves a vertex it reached. -/
theorem closed_along {N : Network} (hN : N.WellFormed) {f : Flow} {i : ℕ}
    (hi : i < N.g.arrows.length) (ht : N.tail i ∈ reached N f)
    (hr : 0 < (ResidualArrow.along i).residualCapacity N f) : N.head i ∈ reached N f := by
  have hn := (List.flatMap_eq_nil_iff.1 (reached_closed hN f)) i (by simpa [Network.ids] using hi)
  rw [List.append_eq_nil_iff] at hn
  by_contra hh
  have h1 := hn.1
  split_ifs at h1 with hc
  exact hc ⟨ht, hh, hr⟩

/-- The search adds the start of every arrow that carries something into a vertex it reached. -/
theorem closed_back {N : Network} (hN : N.WellFormed) {f : Flow} {i : ℕ}
    (hi : i < N.g.arrows.length) (hh : N.head i ∈ reached N f) (hr : 0 < f.on i) :
    N.tail i ∈ reached N f := by
  have hn := (List.flatMap_eq_nil_iff.1 (reached_closed hN f)) i (by simpa [Network.ids] using hi)
  rw [List.append_eq_nil_iff] at hn
  by_contra ht
  have h2 := hn.2
  split_ifs at h2 with hc
  exact hc ⟨hh, ht, hr⟩

/-- **How the search entered a vertex**: every vertex it reached, except the source, is the end of
an arrow with room from a vertex it reached, or the start of an arrow carrying something into one.
-/
theorem entered (N : Network) (f : Flow) :
    ∀ v ∈ reached N f, v = N.source ∨ ∃ i < N.g.arrows.length,
      (N.head i = v ∧ N.tail i ∈ reached N f ∧ 0 < (ResidualArrow.along i).residualCapacity N f) ∨
        (N.tail i = v ∧ N.head i ∈ reached N f ∧ 0 < f.on i) := by
  suffices h : ∀ k, ∀ v ∈ (reachStep N f)^[k] [N.source], v = N.source ∨
      ∃ i < N.g.arrows.length,
        (N.head i = v ∧ N.tail i ∈ (reachStep N f)^[k] [N.source] ∧
            0 < (ResidualArrow.along i).residualCapacity N f) ∨
          (N.tail i = v ∧ N.head i ∈ (reachStep N f)^[k] [N.source] ∧ 0 < f.on i) from h _
  intro k
  induction k with
  | zero => intro v hv; exact Or.inl (List.mem_singleton.1 hv)
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply'] at hv ⊢
    have mono : ∀ w ∈ (reachStep N f)^[k] [N.source],
        w ∈ reachStep N f ((reachStep N f)^[k] [N.source]) := fun w hw => by
      rw [reachStep_eq]; exact List.mem_append_left _ hw
    rw [reachStep_eq, List.mem_append] at hv
    rcases hv with hv | hv
    · rcases ih v hv with h | ⟨i, hi, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, Or.inl ⟨h1, mono _ h2, h3⟩⟩
      · exact Or.inr ⟨i, hi, Or.inr ⟨h1, mono _ h2, h3⟩⟩
    · obtain ⟨i, hi, ⟨h1, -, h3, rfl⟩ | ⟨h1, -, h3, rfl⟩⟩ := mem_reachNew hv
      · exact Or.inr ⟨i, hi, Or.inl ⟨rfl, mono _ h1, h3⟩⟩
      · exact Or.inr ⟨i, hi, Or.inr ⟨rfl, mono _ h1, h3⟩⟩

theorem source_mem_reached (N : Network) (f : Flow) : N.source ∈ reached N f :=
  source_mem_iterate N f _

/-! ## What the last search says on the matching network -/

/-- **A person the search reached reaches every object they accept.** -/
theorem reaches_accepted (hP : P.WellFormed) {f : Flow} (hf : IsFlow P.network f) {j : ℕ}
    (hj : j < P.pairs.length) (hp : 1 + (P.pair j).1 ∈ reached P.network f) :
    1 + P.people + (P.pair j).2 ∈ reached P.network f := by
  have hN := network_wellFormed hP
  have hi : P.people + j < P.network.g.arrows.length := by rw [length_arrows]; omega
  have hpj := (pair_lt hP hj).1
  by_cases h0 : f.on (P.people + j) = 0
  · have := closed_along hN hi (by rw [tail_pair hj]; exact hp)
      (by simp [ResidualArrow.residualCapacity, h0, capOf_eq hi])
    rwa [head_pair hj] at this
  by_contra hno
  rcases entered _ _ _ hp with h | ⟨i', hi', ⟨hh, -, hr⟩ | ⟨ht, hS, hpos⟩⟩
  · rw [network_source] at h; omega
  · obtain rfl := head_eq_person hi' hpj hh
    simp only [ResidualArrow.residualCapacity, capOf_eq hi'] at hr
    have h1 := le_outflow f hi
    rw [tail_pair hj, ← conserved_person hf hpj] at h1
    have h2 := inflow_person_le f hpj
    omega
  · have hne : P.people + j ≠ i' := by
      rintro rfl
      rw [head_pair hj] at hS
      exact hno hS
    have := add_le_outflow f hi hi' hne (tail_pair hj) ht
    have := outflow_person_le_one hf hpj
    omega

/-- **A person the search did not reach is matched.** -/
theorem matched_of_not_reached (hP : P.WellFormed) {f : Flow} (hf : IsFlow P.network f) {p : ℕ}
    (hp : p < P.people) (hno : 1 + p ∉ reached P.network f) :
    ∃ j < P.pairs.length, (P.pair j).1 = p ∧ 0 < f.on (P.people + j) := by
  by_contra hall
  simp only [not_exists, not_and, not_lt] at hall
  have hN := network_wellFormed hP
  have hout : outflow P.network f (1 + p) = 0 := outflow_eq_zero f fun i hi ht => by
    obtain ⟨j, hj, rfl, hpj⟩ := tail_eq_person hi hp ht
    have := hall j hj hpj
    omega
  have hi : p < P.network.g.arrows.length := by rw [length_arrows]; omega
  have hin := le_inflow f hi
  rw [head_source hp, conserved_person hf hp, hout] at hin
  have := closed_along (f := f) hN hi (by rw [tail_source hp]; exact source_mem_reached _ _)
    (by simp [ResidualArrow.residualCapacity, capOf_eq hi]; omega)
  rw [head_source hp] at this
  exact hno this

/-- **An object the search reached is matched**, since the search did not reach the sink. -/
theorem matched_of_reached (hP : P.WellFormed) {f : Flow} (hf : IsFlow P.network f)
    (hsink : P.network.sink ∉ reached P.network f) {o : ℕ} (ho : o < P.objects)
    (hS : 1 + P.people + o ∈ reached P.network f) :
    ∃ j < P.pairs.length, (P.pair j).2 = o ∧ 0 < f.on (P.people + j) := by
  by_contra hall
  simp only [not_exists, not_and, not_lt] at hall
  have hN := network_wellFormed hP
  have hin : inflow P.network f (1 + P.people + o) = 0 := inflow_eq_zero f fun i hi hh => by
    obtain ⟨j, hj, rfl, hoj⟩ := head_eq_object hi ho hh
    have := hall j hj hoj
    omega
  have hi : P.people + P.pairs.length + o < P.network.g.arrows.length := by
    rw [length_arrows]; omega
  have hout := le_outflow f hi
  rw [tail_sink ho, ← conserved_object hf ho, hin] at hout
  have := closed_along hN hi (by rw [tail_sink ho]; exact hS)
    (by simp [ResidualArrow.residualCapacity, capOf_eq hi]; omega)
  rw [head_sink ho] at this
  exact hsink this

/-- **A matched pair whose object the search reached has its person reached too.** -/
theorem reached_of_matched (hP : P.WellFormed) {f : Flow} {j : ℕ} (hj : j < P.pairs.length)
    (hpos : 0 < f.on (P.people + j)) (hS : 1 + P.people + (P.pair j).2 ∈ reached P.network f) :
    1 + (P.pair j).1 ∈ reached P.network f := by
  have hi : P.people + j < P.network.g.arrows.length := by rw [length_arrows]; omega
  have := closed_back (network_wellFormed hP) hi (by rw [head_pair hj]; exact hS) hpos
  rwa [tail_pair hj] at this

/-! ## The answer read from the last search -/

/-- **The cover's people**: those the search did not reach. -/
def coverPeopleOf (P : Problem) (S : List ℕ) : List ℕ :=
  (List.range P.people).filter fun p => 1 + p ∉ S

/-- **The cover's objects**: those the search reached. -/
def coverObjectsOf (P : Problem) (S : List ℕ) : List ℕ :=
  (List.range P.objects).filter fun o => 1 + P.people + o ∈ S

/-- **The blocked group**: the people the search reached, and the objects they accept. -/
def groupOf (P : Problem) (S : List ℕ) : Group :=
  let g := (List.range P.people).filter fun p => 1 + p ∈ S
  ⟨g, (List.range P.objects).filter fun o => ∃ p ∈ g, (p, o) ∈ P.pairs⟩

/-- The answer read from a flow and the vertices the last search reached: the pairs that carry the
unit, the cover, and the blocked group when someone stays unmatched. -/
def answerOf (P : Problem) (f : Flow) (S : List ℕ) : Answer where
  pairs := carried P f
  coverPeople := coverPeopleOf P S
  coverObjects := coverObjectsOf P S
  blocked := if (carried P f).length < P.people then some (groupOf P S) else none

theorem mem_carried {f : Flow} {e : ℕ × ℕ} :
    e ∈ carried P f ↔ ∃ j < P.pairs.length, 0 < f.on (P.people + j) ∧ P.pair j = e := by
  simp [carried, Problem.pair, and_assoc]

/-- **No matching is larger than a cover**: each pair of a matching is incident to a member of the
cover, and no two pairs at the same person or at the same object. -/
theorem matching_le_cover {M : List (ℕ × ℕ)} {cp co : List ℕ} (hM : IsMatching P M)
    (hC : IsCover P cp co) : M.length ≤ cp.length + co.length := by
  have hsplit := List.length_eq_length_filter_add (l := M) (fun e => decide (e.1 ∈ cp))
  have h1 : (M.filter fun e => decide (e.1 ∈ cp)).length ≤ cp.length := by
    rw [← List.length_map (f := Prod.fst)]
    refine List.Subperm.length_le (List.Nodup.subperm ?_ fun x hx => ?_)
    · exact hM.2.1.sublist (List.filter_sublist.map _)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      simpa using (List.mem_filter.1 he).2
  have h2 : (M.filter fun e => !decide (e.1 ∈ cp)).length ≤ co.length := by
    rw [← List.length_map (f := Prod.snd)]
    refine List.Subperm.length_le (List.Nodup.subperm ?_ fun x hx => ?_)
    · exact hM.2.2.sublist (List.filter_sublist.map _)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      obtain ⟨heM, hn⟩ := List.mem_filter.1 he
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hn
      exact (hC.2.2.2.2 e (hM.1 e heM)).resolve_left hn
  omega

variable {f : Flow}

/-- **The people not reached and the objects reached are a cover.** -/
theorem isCover_read (hP : P.WellFormed) (hf : IsFlow P.network f) :
    IsCover P (coverPeopleOf P (reached P.network f)) (coverObjectsOf P (reached P.network f)) := by
  refine ⟨List.nodup_range.filter _, List.nodup_range.filter _,
    fun p hp => by simpa [coverPeopleOf] using (List.mem_filter.1 hp).1,
    fun o ho => by simpa [coverObjectsOf] using (List.mem_filter.1 ho).1, fun e he => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
  have hpj : P.pair j = P.pairs[j] := by
    simp [Problem.pair, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hlt := pair_lt hP hj
  rw [hpj] at hlt
  by_cases hS : 1 + P.pairs[j].1 ∈ reached P.network f
  · right
    have := reaches_accepted hP hf hj (by rw [hpj]; exact hS)
    rw [hpj] at this
    simpa [coverObjectsOf, hlt.2] using this
  · left
    simpa [coverPeopleOf, hlt.1] using hS

/-- **The cover is no larger than the matching**: every person in it is matched, every object in it
is matched, and no matched pair has both its person and its object in it. -/
theorem cover_le_carried (hP : P.WellFormed) (hf : IsFlow P.network f)
    (hsink : P.network.sink ∉ reached P.network f) :
    (coverPeopleOf P (reached P.network f)).length +
        (coverObjectsOf P (reached P.network f)).length ≤ (carried P f).length := by
  set S := reached P.network f
  set M := carried P f
  have hsplit := List.length_eq_length_filter_add (l := M) (fun e => decide (1 + e.1 ∉ S))
  have h1 : (coverPeopleOf P S).length ≤ (M.filter fun e => decide (1 + e.1 ∉ S)).length := by
    refine (List.Subperm.length_le (List.Nodup.subperm (List.nodup_range.filter _)
      fun p hp => ?_)).trans_eq (List.length_map (f := Prod.fst) ..)
    obtain ⟨hp, hno⟩ := List.mem_filter.1 hp
    simp only [List.mem_range, decide_eq_true_eq] at hp hno
    obtain ⟨j, hj, hpj, hpos⟩ := matched_of_not_reached hP hf hp hno
    refine List.mem_map.2 ⟨P.pair j, List.mem_filter.2 ⟨mem_carried.2 ⟨j, hj, hpos, rfl⟩, ?_⟩, hpj⟩
    simpa [hpj] using hno
  have h2 : (coverObjectsOf P S).length ≤
      (M.filter fun e => decide (1 + P.people + e.2 ∈ S)).length := by
    refine (List.Subperm.length_le (List.Nodup.subperm (List.nodup_range.filter _)
      fun o ho => ?_)).trans_eq (List.length_map (f := Prod.snd) ..)
    obtain ⟨ho, hS⟩ := List.mem_filter.1 ho
    simp only [List.mem_range, decide_eq_true_eq] at ho hS
    obtain ⟨j, hj, hoj, hpos⟩ := matched_of_reached hP hf hsink ho hS
    refine List.mem_map.2 ⟨P.pair j, List.mem_filter.2 ⟨mem_carried.2 ⟨j, hj, hpos, rfl⟩, ?_⟩, hoj⟩
    simpa [hoj] using hS
  have h3 : (M.filter fun e => decide (1 + P.people + e.2 ∈ S)).length ≤
      (M.filter fun e => !decide (1 + e.1 ∉ S)).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    refine List.countP_mono_left fun e he hB => ?_
    obtain ⟨j, hj, hpos, rfl⟩ := mem_carried.1 he
    simp only [decide_eq_true_eq] at hB
    simpa using reached_of_matched hP hj hpos hB
  omega

/-- **When someone stays unmatched, the people the search reached are a blocked group.** -/
theorem isBlocked_read (hP : P.WellFormed) (hf : IsFlow P.network f)
    (hsink : P.network.sink ∉ reached P.network f) (hlt : (carried P f).length < P.people) :
    IsBlocked P (groupOf P (reached P.network f)) := by
  have hM := matching_le_cover (carried_isMatching hP hf) (isCover_read hP hf)
  have hC := cover_le_carried hP hf hsink
  set S := reached P.network f
  have hsplit := List.length_eq_length_filter_add (l := List.range P.people)
    (fun p => decide (1 + p ∈ S))
  have hcp : (coverPeopleOf P S).length =
      ((List.range P.people).filter fun p => !decide (1 + p ∈ S)).length := by
    simp [coverPeopleOf]
  have hobj : ∀ o ∈ (groupOf P S).objects, o ∈ coverObjectsOf P S := fun o ho => by
    obtain ⟨ho, hex⟩ := List.mem_filter.1 ho
    simp only [decide_eq_true_eq] at hex
    obtain ⟨p, hp, hpo⟩ := hex
    obtain ⟨-, hpS⟩ := List.mem_filter.1 hp
    simp only [decide_eq_true_eq] at hpS
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 hpo
    have hpj : P.pair j = (p, o) := by
      simp [Problem.pair, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, hje]
    have := reaches_accepted hP hf hj (by rw [hpj]; exact hpS)
    rw [hpj] at this
    exact List.mem_filter.2 ⟨ho, by simpa using this⟩
  have hlen : (groupOf P S).objects.length ≤ (coverObjectsOf P S).length :=
    (List.Nodup.subperm (List.nodup_range.filter _) hobj).length_le
  refine ⟨List.nodup_range.filter _, fun p hp => by simpa using (List.mem_filter.1 hp).1,
    List.nodup_range.filter _, fun o => ⟨fun ho => ?_, fun ⟨p, hp, hpo⟩ => ?_⟩, ?_⟩
  · simpa [groupOf] using (List.mem_filter.1 ho).2
  · have hp' : p < P.people ∧ 1 + p ∈ S := by simpa [groupOf] using hp
    exact List.mem_filter.2 ⟨List.mem_range.2 (hP _ hpo).2, by simpa using ⟨p, hp', hpo⟩⟩
  · change _ < ((List.range P.people).filter fun p => decide (1 + p ∈ S)).length
    simp only [List.length_range] at hsplit
    omega

end AlgoDesign.Flows.Matching
