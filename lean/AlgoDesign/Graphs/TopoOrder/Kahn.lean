/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.TopoOrder.Basic

/-!
# Kahn's walk

Source: Weiss, *Data Structures and Algorithm Analysis in C++* (4th ed.), §9.2, Fig. 9.7 (p. 385):
count the arrows into each vertex; queue every vertex of count 0, scanning the vertices in order;
take the front of the queue, place it, and walk its row, lowering each neighbour's count and
queueing a neighbour whose count reaches 0. Ahuja, Magnanti and Orlin, *Network Flows* (1993),
pp. 77–78, for what is left when the queue runs dry: the vertices not placed, each with an arrow in
from another of them.

A doubled arrow counts twice and is walked twice; a loop counts once on its vertex, which never
becomes ready. The walk is `runSteps` from `start` with `step`, at most one step per vertex.
-/

@[expose] public section

namespace AlgoDesign.Graphs.TopoOrder

open Digraph

/-! ## The walk -/

/-- Walk a row: for each entry `(w, id)` in order, lower `w`'s count by one, and queue `w` at the
back if its count is now 0. -/
def relax : List (ℕ × ℕ) → (ℕ → ℕ) → List ℕ → (ℕ → ℕ) × List ℕ
  | [], c, q => (c, q)
  | (w, _) :: r, c, q =>
    let c' := Function.update c w (c w - 1)
    relax r c' (if c' w = 0 then q ++ [w] else q)

/-- **Kahn's start**: nothing placed; each vertex's count is the number of arrows into it; every
vertex of count 0 queued, from vertex 0 upward. -/
def start (g : Digraph) : KahnState :=
  let c := fun v => g.arrows.countP (fun a => a.2 = v)
  ⟨g, [], c, (List.range g.n).filter (fun v => c v = 0)⟩

/-- **Kahn's step**: take the front of the queue, place it, and walk its row in the state's
graph. -/
def step (st : KahnState) : KahnState :=
  match st.queue with
  | [] => st
  | v :: q =>
    let r := relax (st.g.out v) st.count q
    ⟨st.g, st.placed ++ [v], r.1, r.2⟩

/-- **Kahn's method**: walk until the queue is empty, one step per vertex at most; the order if
every vertex is placed, else the vertices not placed. -/
def kahn (g : Digraph) : Except (List ℕ) (List ℕ) :=
  answer g (runSteps step g.n (start g))

/-! ## Rows -/

/-- The arrows from `v` to `w`, counted by position, are the copies of `(v, w)`. -/
theorem length_idsBetween (g : Digraph) (v w : ℕ) :
    (g.idsBetween v w).length = g.arrows.countP (fun a => a = (v, w)) := by
  unfold idsBetween
  generalize g.arrows = l
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.countP_cons]
    simp only [List.getElem?_cons_zero, Option.some.injEq, Function.comp_def,
      List.getElem?_cons_succ]
    split <;> simp [ih]

theorem countP_out {g : Digraph} {v w : ℕ} (hw : w < g.n) :
    (g.out v).countP (fun e => e.1 = w) = g.arrows.countP (fun a => a = (v, w)) := by
  rw [← length_idsBetween]
  unfold out
  rw [List.countP_flatMap]
  have hterm : ∀ w', ((List.countP fun e : ℕ × ℕ => decide (e.fst = w')) ∘
      fun w'' => List.map (fun i => (w'', i)) (g.idsBetween v w'')) =
      fun w'' => if w'' = w' then (g.idsBetween v w').length else 0 := by
    intro w'
    funext w''
    split
    · subst w''; simp [List.countP_map, Function.comp_def]
    · simp [List.countP_map, Function.comp_def, *]
  rw [hterm]
  have hsum : ∀ m, ((List.range m).map
      fun w'' => if w'' = w then (g.idsBetween v w).length else 0).sum =
      if w < m then (g.idsBetween v w).length else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      by_cases h1 : w < m
      · simp [h1, show w < m + 1 by omega, show m ≠ w by omega]
      · by_cases h2 : w = m
        · subst h2; simp
        · simp [h1, show ¬ w < m + 1 by omega, Ne.symm h2]
  simp [hsum, hw]

/-! ## Walking a row -/

theorem relax_spec (r : List (ℕ × ℕ)) (c : ℕ → ℕ) (q : List ℕ)
    (h1 : ∀ w, r.countP (fun e => e.1 = w) ≤ c w) (h2 : ∀ e ∈ r, e.1 ∉ q) (hq : q.Nodup) :
    (relax r c q).1 = (fun w => c w - r.countP (fun e => e.1 = w)) ∧ (relax r c q).2.Nodup ∧
      ∀ x, x ∈ (relax r c q).2 ↔
        x ∈ q ∨ ((∃ e ∈ r, e.1 = x) ∧ c x - r.countP (fun e => e.1 = x) = 0) := by
  induction r generalizing c q with
  | nil => simp [relax, hq]
  | cons e r ih =>
    obtain ⟨w, i⟩ := e
    have hwq : w ∉ q := h2 (w, i) List.mem_cons_self
    have h1w := h1 w
    simp only [List.countP_cons, decide_true, ite_true] at h1w
    have hcnt : ∀ x, ((w, i) :: r).countP (fun e => e.1 = x) =
        r.countP (fun e => e.1 = x) + if x = w then 1 else 0 := by
      intro x
      rw [List.countP_cons]
      by_cases hx : x = w
      · simp [hx]
      · simp [hx, Ne.symm hx]
    simp only [relax]
    set c' := Function.update c w (c w - 1) with hc'
    have hc'x : ∀ x, c' x = if x = w then c w - 1 else c x := by
      intro x
      by_cases hx : x = w <;> simp [hc', hx]
    set q' := if c' w = 0 then q ++ [w] else q with hq'
    have h1' : ∀ x, r.countP (fun e => e.1 = x) ≤ c' x := by
      intro x
      have hx1 := h1 x
      rw [hcnt] at hx1
      rw [hc'x]
      by_cases hx : x = w
      · subst hx
        simp only [ite_true] at hx1 ⊢
        omega
      · simpa only [hx, ite_false, Nat.add_zero] using hx1
    have hmem_r : ∀ x, (∃ e ∈ r, e.1 = x) → 0 < r.countP (fun e => e.1 = x) := by
      rintro x ⟨e, he, rfl⟩
      exact List.countP_pos_iff.2 ⟨e, he, by simp⟩
    have h2' : ∀ e ∈ r, e.1 ∉ q' := by
      intro e he hin
      rw [hq'] at hin
      split at hin
      · rcases List.mem_append.1 hin with hin | hin
        · exact h2 e (List.mem_cons_of_mem _ he) hin
        · have hew : e.1 = w := by simpa using hin
          have := hmem_r w ⟨e, he, hew⟩
          have := h1' w
          omega
      · exact h2 e (List.mem_cons_of_mem _ he) hin
    have hqn' : q'.Nodup := by
      rw [hq']
      split
      · have : ∀ x ∈ q, x ≠ w := fun x hx (h : x = w) => hwq (h ▸ hx)
        simpa [List.nodup_append, hq] using this
      · exact hq
    obtain ⟨ha, hb, hc⟩ := ih c' q' h1' h2' hqn'
    refine ⟨?_, hb, ?_⟩
    · rw [ha]
      funext x
      rw [hcnt, hc'x]
      by_cases hx : x = w
      · subst hx
        simp only [ite_true]
        omega
      · simp only [hx, ite_false, Nat.add_zero]
    · intro x
      rw [hc x, hcnt, hc'x]
      by_cases hx : x = w
      · subst hx
        have hex : ∃ e ∈ (x, i) :: r, e.1 = x := ⟨(x, i), List.mem_cons_self, rfl⟩
        have hq'x : x ∈ q' ↔ c x - 1 = 0 := by
          rw [hq', hc'x]
          by_cases h0 : c x - 1 = 0 <;> simp [h0, hwq]
        rw [hq'x]
        simp only [ite_true, hex, true_and, hwq, false_or]
        constructor
        · rintro (h | ⟨-, h⟩) <;> omega
        · intro h
          by_cases h0 : c x - 1 = 0
          · exact Or.inl h0
          · right
            obtain ⟨e, he, hex⟩ := List.countP_pos_iff.1 
              (show 0 < r.countP (fun e => decide (e.1 = x)) by omega)
            exact ⟨⟨e, he, by simpa using hex⟩, by omega⟩
      · have hq'x : x ∈ q' ↔ x ∈ q := by
          rw [hq']
          split <;> simp [hx]
        have hex : (∃ e ∈ (w, i) :: r, e.1 = x) ↔ ∃ e ∈ r, e.1 = x := by
          simp [Ne.symm hx]
        rw [hq'x, hex]
        simp [hx]

/-! ## The invariants -/

/-- **Kahn's start is legal.** -/
theorem valid_start {g : Digraph} : Valid (start g) := by
  refine ⟨⟨⟨List.nodup_nil, by simp [start]⟩, by simp [start]⟩, ?_, ?_, ?_, ?_⟩
  · intro v _ _
    simp [start]
  · exact List.nodup_range.filter _
  · intro v hv
    simp only [start, List.mem_filter, List.mem_range, decide_eq_true_eq] at hv
    simpa [start] using hv
  · intro v hv _ h0
    simp only [start] at hv
    simpa [start, hv] using h0

/-- Taking `v` out of the unplaced vertices: the arrows into `x` from unplaced vertices other than
`v`, and those from `v`. -/
theorem countP_split (l : List (ℕ × ℕ)) (placed : List ℕ) {v : ℕ} (hv : v ∉ placed) (x : ℕ) :
    l.countP (fun a => a.2 = x ∧ a.1 ∉ placed) =
      l.countP (fun a => a.2 = x ∧ a.1 ∉ placed ++ [v]) + l.countP (fun a => a = (v, x)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    obtain ⟨a1, a2⟩ := a
    by_cases h2 : a2 = x
    · by_cases h1 : a1 = v
      · subst h1 h2; simp [hv]; omega
      · by_cases hp : a1 ∈ placed
        · simp [hp, h1]
        · simp [hp, h1, h2]; omega
    · simp [h2]

/-- In a legal state, an unplaced vertex of count 0 waits only on placed vertices. -/
theorem waits_placed_of_zero {st : KahnState} (hC : CountsUnplacedWaits st)
    {x : ℕ} (hx : x < st.g.n) (hxp : x ∉ st.placed) (h0 : st.count x = 0) :
    ∀ a ∈ st.g.arrows, a.2 = x → a.1 ∈ st.placed := by
  intro a ha h2
  by_contra h1
  have hc := hC x hx hxp
  have : 0 < st.g.arrows.countP (fun a => a.2 = x ∧ a.1 ∉ st.placed) :=
    List.countP_pos_iff.2 ⟨a, ha, by simp [h2, h1]⟩
  omega

/-- **Kahn's step keeps its state legal**, the box's three invariants. -/
theorem valid_step {st : KahnState} (h : Valid st)
    (hq : st.queue ≠ []) : Valid (step st) := by
  obtain ⟨g, placed, c, queue⟩ := st
  cases queue with
  | nil => exact absurd rfl hq
  | cons v q =>
  have hC : CountsUnplacedWaits ⟨g, placed, c, v :: q⟩ := h.2.1
  have hC' : ∀ x < g.n, x ∉ placed →
      c x = g.arrows.countP (fun a => a.2 = x ∧ a.1 ∉ placed) := hC
  obtain ⟨⟨hA, hlt⟩, -, hnd, hR1, hR2⟩ := h
  simp only at hA hlt hnd hR1 hR2
  obtain ⟨hvn, hvp, hcv⟩ := hR1 v List.mem_cons_self
  have hvq : v ∉ q := (List.nodup_cons.1 hnd).1
  have hpred := waits_placed_of_zero hC hvn hvp hcv
  have hrow : ∀ e ∈ g.out v, e.1 < g.n ∧ e.1 ∉ placed ∧ e.1 ≠ v ∧ e.1 ∉ q := by
    intro e he
    obtain ⟨hen, harr⟩ := mem_out he
    have hep : e.1 ∉ placed := fun hp => hvp (hA.2 _ harr hp).mem_left
    refine ⟨hen, hep, fun hev => hvp (hpred _ harr hev), fun heq => ?_⟩
    obtain ⟨-, -, h0⟩ := hR1 e.1 (List.mem_cons_of_mem _ heq)
    exact hvp (waits_placed_of_zero hC hen hep h0 _ harr rfl)
  have hle : ∀ w, (g.out v).countP (fun e => e.1 = w) ≤ c w := by
    intro w
    by_cases hw : w < g.n
    · rw [countP_out hw]
      by_cases hwp : w ∈ placed
      · have : g.arrows.countP (fun a => a = (v, w)) = 0 := by
          refine List.countP_eq_zero.2 fun a ha h => ?_
          simp only [decide_eq_true_eq] at h
          subst h
          exact hvp (hA.2 _ ha hwp).mem_left
        rw [this]
        exact Nat.zero_le _
      · rw [hC' w hw hwp]
        exact List.countP_mono_left fun a _ h => by simp at h; simp [h, hvp]
    · have : (g.out v).countP (fun e => e.1 = w) = 0 :=
        List.countP_eq_zero.2 fun e he h => hw (by
          simp only [decide_eq_true_eq] at h
          exact h ▸ (mem_out he).1)
      omega
  obtain ⟨hc', hqnd', hmem'⟩ := relax_spec (g.out v) c q hle (fun e he => (hrow e he).2.2.2)
    (List.nodup_cons.1 hnd).2
  have hnot : ∀ x, x ∉ placed ++ [v] ↔ x ∉ placed ∧ x ≠ v := by simp
  change Valid ⟨g, placed ++ [v], (relax (g.out v) c q).1, (relax (g.out v) c q).2⟩
  refine ⟨⟨hA.append_ready hvp hpred, ?_⟩, ?_, hqnd', ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hlt x hx
    · simp only [List.mem_singleton] at hx
      exact hx ▸ hvn
  · intro x hx hxp
    dsimp only at hxp ⊢
    rw [hnot] at hxp
    rw [hc']
    dsimp only
    rw [countP_out hx, hC' x hx hxp.1, countP_split g.arrows placed hvp x]
    simp
  · intro x hx
    dsimp only at hx ⊢
    rw [hnot, hc']
    rcases (hmem' x).1 hx with hx | ⟨⟨e, he, rfl⟩, h0⟩
    · obtain ⟨h1, h2, h3⟩ := hR1 x (List.mem_cons_of_mem _ hx)
      exact ⟨h1, ⟨h2, fun h => hvq (h ▸ hx)⟩, by simp [h3]⟩
    · obtain ⟨h1, h2, h3, -⟩ := hrow e he
      exact ⟨h1, ⟨h2, h3⟩, h0⟩
  · intro x hx hxp h0
    dsimp only at hxp h0 ⊢
    rw [hnot] at hxp
    rw [hc'] at h0
    dsimp only at h0
    refine (hmem' x).2 ?_
    by_cases he : ∃ e ∈ g.out v, e.1 = x
    · exact Or.inr ⟨he, h0⟩
    · have : (g.out v).countP (fun e => e.1 = x) = 0 :=
        List.countP_eq_zero.2 fun e he' h => he ⟨e, he', by simpa using h⟩
      rw [this, Nat.sub_zero] at h0
      rcases List.mem_cons.1 (hR2 x hx hxp.1 h0) with h | h
      · exact absurd h hxp.2
      · exact Or.inl h

/-! ## The answer -/

/-- A step from a nonempty queue places one vertex. -/
theorem length_step {st : KahnState} (hq : st.queue ≠ []) :
    (step st).placed.length = st.placed.length + 1 := by
  obtain ⟨g, placed, c, queue⟩ := st
  cases queue with
  | nil => exact absurd rfl hq
  | cons v q => simp [step]

/-- A step keeps the state's graph. -/
theorem step_g (st : KahnState) : (step st).g = st.g := by
  unfold step
  split <;> rfl

/-- Steps keep the state's graph. -/
theorem runSteps_g : ∀ (f : ℕ) (st : KahnState), (runSteps step f st).g = st.g
  | 0, _ => rfl
  | f + 1, st => by
    unfold runSteps
    split
    · rfl
    · rw [runSteps_g f (step st), step_g]

/-- In a legal state, a list of placed vertices as long as the graph holds every vertex. -/
theorem range_subset_placed {st : KahnState} (h : Valid st)
    (hlen : st.g.n ≤ st.placed.length) : List.range st.g.n ⊆ st.placed :=
  subset_of_length_le h.1.1.1 (fun x hx => List.mem_range.2 (h.1.2 x hx)) (by simpa using hlen)

/-- **The walk ends legal with an empty queue**, given one step per vertex still to place. -/
theorem runSteps_spec (f : ℕ) {st : KahnState} (h : Valid st)
    (hf : st.g.n ≤ st.placed.length + f) :
    Valid (runSteps step f st) ∧ (runSteps step f st).queue = [] := by
  induction f generalizing st with
  | zero =>
    refine ⟨h, ?_⟩
    rcases hq : st.queue with _ | ⟨x, q⟩
    · exact hq
    · obtain ⟨hx, hxp, -⟩ := h.2.2.2.1 x (by simp [hq])
      exact absurd (range_subset_placed h (by simpa using hf) (List.mem_range.2 hx)) hxp
  | succ f ih =>
    unfold runSteps
    split
    · exact ⟨h, by assumption⟩
    · next hq => exact ih (valid_step h hq) (by rw [length_step hq, step_g]; omega)

/-- **Kahn's promise**: on a graph whose arrows join its vertices, every vertex exactly once with
every arrow forward, or the stuck set. -/
theorem kahn_spec {g : Digraph} (hg : g.WellFormed) : KahnPromise g (kahn g) := by
  obtain ⟨h, hq⟩ := runSteps_spec (st := start g) g.n valid_start (by simp [start])
  have hgst : (runSteps step g.n (start g)).g = g := runSteps_g _ _
  set st := runSteps step g.n (start g)
  have hsub : g.n ≤ st.placed.length → List.range g.n ⊆ st.placed := fun hlen =>
    hgst ▸ range_subset_placed h (hgst ▸ hlen)
  obtain ⟨⟨hA, hlt⟩, hC, -, -, hR2⟩ := h
  unfold CountsUnplacedWaits at hC
  rw [hgst] at hA hlt hC hR2
  have hmem : ∀ x, x ∈ outside g st.placed ↔ x < g.n ∧ x ∉ st.placed := fun _ => mem_outside
  unfold kahn answer
  split
  · next hlen =>
    refine ⟨(List.perm_ext_iff_of_nodup hA.1 List.nodup_range).2 fun x =>
      ⟨fun hx => List.mem_range.2 (hlt x hx), fun hx => ?_⟩, fun a ha => ?_⟩
    · exact hsub hlen.ge hx
    · exact hA.2 a ha (hsub hlen.ge (List.mem_range.2 (hg a ha).2))
  · next hlen =>
    refine ⟨?_, List.pairwise_lt_range.filter _, fun x hx => ((hmem x).1 hx).1, ?_, ?_⟩
    · intro hnil
      apply hlen
      have hsub : List.range g.n ⊆ st.placed := fun x hx => by
        by_contra hxp
        have := (hmem x).2 ⟨List.mem_range.1 hx, hxp⟩
        rw [hnil] at this
        simp at this
      have h1 := List.nodup_range.length_le_of_subset hsub
      have h2 := hA.1.length_le_of_subset (fun x hx => List.mem_range.2 (hlt x hx))
      simp only [List.length_range] at h1 h2
      exact le_antisymm h2 h1
    · intro x hx
      obtain ⟨hxn, hxp⟩ := (hmem x).1 hx
      have hc := hC x hxn hxp
      have hne : st.count x ≠ 0 := fun h0 => by simpa [hq] using hR2 x hxn hxp h0
      obtain ⟨a, ha, hax⟩ := List.countP_pos_iff.1 (show 0 < g.arrows.countP
        (fun a => decide (a.2 = x ∧ a.1 ∉ st.placed)) by omega)
      simp only [decide_eq_true_eq] at hax
      refine ⟨a.1, (hmem a.1).2 ⟨(hg a ha).1, hax.2⟩, ?_⟩
      have : a = (a.1, x) := by rw [← hax.1]
      exact this ▸ ha
    · refine ⟨st.placed, (List.perm_ext_iff_of_nodup hA.1 (nodup_outside _ _)).2 fun x => ?_, hA⟩
      rw [mem_outside, hmem]
      exact ⟨fun hx => ⟨hlt x hx, fun h => h.2 hx⟩,
        fun ⟨hxn, hno⟩ => by_contra fun hxp => hno ⟨hxn, hxp⟩⟩

/-- **Kahn names the stuck set exactly when there is one**: on a graph whose arrows join its
vertices, a list is the stuck set exactly when Kahn reports it. -/
theorem kahn_eq_error_iff {g : Digraph} (hg : g.WellFormed) (s : List ℕ) :
    kahn g = .error s ↔ IsStuck g s := by
  have hk := kahn_spec hg
  constructor
  · intro h
    rw [h] at hk
    exact hk
  · intro hs
    revert hk
    cases kahn g with
    | ok l => exact fun hl => absurd ⟨l, hl⟩ (no_topoOrder_of_isStuck hs)
    | error t => exact fun ht => by rw [IsStuck.unique ht hs]

/-! ## Cost

The box's cost, one look at every vertex and every arrow: each step looks at the vertex it takes and
at every entry of that vertex's row, once; over the whole walk that is at most `n + m` looks. -/

/-- Over the vertices `0, …, n - 1`, a sum that is `c` at `k` and 0 elsewhere. -/
theorem sum_range_ite (n k c : ℕ) :
    ((List.range n).map fun w => if w = k then c else 0).sum = if k < n then c else 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : k < m
    · simp [h1, show k < m + 1 by omega, show m ≠ k by omega]
    · by_cases h2 : k = m
      · subst h2; simp
      · simp [h1, show ¬ k < m + 1 by omega, Ne.symm h2]

/-- A row holds every arrow from its vertex to a vertex of the graph. -/
theorem length_out (g : Digraph) (v : ℕ) :
    (g.out v).length = g.arrows.countP (fun a => a.1 = v ∧ a.2 < g.n) := by
  unfold out
  rw [List.length_flatMap]
  simp only [List.length_map, length_idsBetween]
  generalize g.arrows = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    rw [← ih]
    have : ∀ w, (if a = (v, w) then 1 else 0) =
        if w = a.2 then (if a.1 = v then 1 else 0) else 0 := by
      intro w
      obtain ⟨a1, a2⟩ := a
      by_cases h1 : a1 = v
      · subst h1
        by_cases h2 : w = a2 <;> simp [h2, eq_comm]
      · by_cases h2 : w = a2 <;> simp [h1, h2]
    have hsplit : ((List.range g.n).map fun w =>
        List.countP (fun x => decide (x = (v, w))) l + if a = (v, w) then 1 else 0).sum =
        ((List.range g.n).map fun w => List.countP (fun x => decide (x = (v, w))) l).sum +
        ((List.range g.n).map fun w => if a = (v, w) then 1 else 0).sum := by
      generalize List.range g.n = r
      induction r with
      | nil => simp
      | cons b r ihr => simp only [List.map_cons, List.sum_cons, ihr]; omega
    simp only [decide_eq_true_eq] at hsplit ⊢
    rw [hsplit, funext this, sum_range_ite]
    obtain ⟨a1, a2⟩ := a
    by_cases h1 : a1 = v <;> by_cases h2 : a2 < g.n <;> simp [h1, h2]

/-- Over vertices listed once, the arrows leaving them number at most all the arrows. -/
theorem sum_countP_le (n : ℕ) (l : List (ℕ × ℕ)) :
    ∀ L : List ℕ, L.Nodup →
      (L.map fun v => l.countP (fun a => a.1 = v ∧ a.2 < n)).sum ≤ l.length := by
  induction l with
  | nil => intro L _; simp
  | cons a l ih =>
    intro L hL
    have hzero : ∀ L : List ℕ, a.1 ∉ L →
        (L.map fun v => if a.1 = v ∧ a.2 < n then 1 else 0).sum = 0 := by
      intro L hL
      induction L with
      | nil => simp
      | cons b L ihL =>
        have hb : a.1 ≠ b := fun h => hL (h ▸ List.mem_cons_self)
        simp only [List.map_cons, List.sum_cons, hb, false_and, ite_false,
          ihL (fun h => hL (List.mem_cons_of_mem _ h))]
    have hone : ∀ L : List ℕ, L.Nodup →
        (L.map fun v => if a.1 = v ∧ a.2 < n then 1 else 0).sum ≤ 1 := by
      intro L hL
      induction L with
      | nil => simp
      | cons b L ihL =>
        have hb := List.nodup_cons.1 hL
        simp only [List.map_cons, List.sum_cons]
        by_cases hab : a.1 = b ∧ a.2 < n
        · rw [hzero L (fun hv => hb.1 (hab.1 ▸ hv))]
          split <;> omega
        · simp only [hab, ite_false, Nat.zero_add]
          exact ihL hb.2
    have hsplit : (L.map fun v => (a :: l).countP (fun a => a.1 = v ∧ a.2 < n)).sum =
        (L.map fun v => l.countP (fun a => a.1 = v ∧ a.2 < n)).sum +
        (L.map fun v => if a.1 = v ∧ a.2 < n then 1 else 0).sum := by
      clear ih hone hzero hL
      induction L with
      | nil => simp
      | cons b L ihL =>
        simp only [List.map_cons, List.sum_cons]
        rw [ihL]
        simp only [List.countP_cons, decide_eq_true_eq]
        omega
    rw [hsplit, List.length_cons]
    have := ih L hL
    have := hone L hL
    omega

/-- **One look at every vertex and every arrow**: over Kahn's whole walk, the vertices it takes and
the row entries it walks number at most `n + m`. -/
theorem kahn_cost (g : Digraph) :
    ((runSteps step g.n (start g)).placed.map fun v => (g.out v).length + 1).sum ≤
      g.n + g.arrows.length := by
  obtain ⟨h, -⟩ := runSteps_spec (st := start g) g.n valid_start (by simp [start])
  have hgst : (runSteps step g.n (start g)).g = g := runSteps_g _ _
  obtain ⟨⟨hA, hlt⟩, -⟩ := h
  rw [hgst] at hA hlt
  set placed := (runSteps step g.n (start g)).placed
  have hlen : placed.length ≤ g.n := by
    have := hA.1.length_le_of_subset (fun x hx => List.mem_range.2 (hlt x hx))
    simpa using this
  have hsum : (placed.map fun v => (g.out v).length + 1).sum =
      (placed.map fun v => (g.out v).length).sum + placed.length := by
    clear_value placed
    clear hA hlt hlen
    induction placed with
    | nil => simp
    | cons b L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
  have hle := sum_countP_le g.n g.arrows placed hA.1
  simp only [← length_out] at hle
  omega

example : Valid (start ⟨3, [(0, 1), (0, 1), (1, 2)]⟩) := by decide
example : kahn ⟨3, [(0, 1), (0, 1), (1, 2)]⟩ = .ok [0, 1, 2] := by decide
example : kahn ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ = .error [0, 1, 2] := by decide
example : kahn ⟨0, []⟩ = .ok [] := by decide

end AlgoDesign.Graphs.TopoOrder
