/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.RulesBasic

/-!
# Max flow: Dinic's path rule

Sources: Dinic, "Algorithm for solution of a problem of maximum flow in a network with power
estimation" (1970); Even and Itai's form, in Even, *Graph Algorithms* (1979), §5.2; the Flow
chapter, "Max flow".

A round is one phase. The first-in-first-out search from the source gives every vertex it labels
a level, and stops as soon as the sink is labeled; if the sink is not labeled, the round adds
nothing. An arrow is **admissible** if it has room and goes from one level to the next. Vertices on
the sink's level, other than the sink, are dead ends.

Then one depth-first sweep. Each vertex has a current-arrow pointer into its residual arrows in
adjacency order, 0 at the start of the phase. At the vertex the sweep is at, it moves along the
current arrow if that arrow is admissible, and otherwise advances the pointer. A vertex whose
pointer has passed its last arrow is a dead end: the sweep steps back, and the vertex before
advances its pointer past the arrow it came by. On reaching the sink, the sweep adds the path by
its bottleneck and starts again from the source, with the pointers kept. The phase ends when the
source is a dead end. The round adds the paths in the order the sweep added them.
-/

@[expose] public section

namespace AlgoDesign.Flows

/-- **Admissible** under the flow `f` and the levels `level`: the arrow has room and goes from one
level to the next. -/
def admissible (N : Network) (f : Flow) (level : ℕ → Option ℕ) (a : ResidualArrow) : Bool :=
  decide (0 < a.residualCapacity N f) &&
    match level (a.tail N) with
    | some l => level (a.head N) == some (l + 1)
    | none => false

/-- **The sweep's state**: the flow so far, each vertex's current-arrow pointer, the arrows from the
source to the vertex the sweep is at (the last one first), and the paths added, in order. -/
structure Sweep where
  /-- The flow so far. -/
  flow : Flow
  /-- Each vertex's current arrow: an index into its residual arrows in adjacency order. -/
  ptr : ℕ → ℕ
  /-- The arrows from the source to the vertex the sweep is at, the last one first. -/
  path : List ResidualArrow
  /-- The paths added, in order. -/
  sent : List Augmentation

/-- The vertex the sweep is at: the source, or the head of the last arrow taken. -/
def Sweep.at (N : Network) (S : Sweep) : ℕ :=
  match S.path with
  | [] => N.source
  | a :: _ => a.head N

/-- **One step of the sweep**, with the levels `level` and the sink's level `ls`; none when the
source is a dead end. At the sink: add the path by its bottleneck and go back to the source. At a
vertex off the sink's level whose pointer has an arrow left: move along it if admissible, else
advance the pointer. Otherwise the vertex is a dead end: step back, and the vertex before advances
its pointer. A vertex on the sink's level, other than the sink, is a dead end at once, without
trying its arrows. -/
def sweepStep (N : Network) (level : ℕ → Option ℕ) (ls : ℕ) (S : Sweep) : Option Sweep :=
  let v := S.at N
  if v = N.sink then
    let x := byBottleneck N S.flow S.path.reverse
    some { S with flow := x.apply S.flow, path := [], sent := S.sent ++ [x] }
  else if level v ≠ some ls ∧ S.ptr v < (N.residualOut v).length then
    let a := (N.residualOut v).getD (S.ptr v) (.along 0)
    if admissible N S.flow level a then some { S with path := a :: S.path }
    else some { S with ptr := Function.update S.ptr v (S.ptr v + 1) }
  else
    match S.path with
    | [] => none
    | a :: rest =>
      some { S with path := rest, ptr := Function.update S.ptr (a.tail N) (S.ptr (a.tail N) + 1) }

/-- At most `k` steps of the sweep; it stops when the source is a dead end. -/
def sweepSteps (N : Network) (level : ℕ → Option ℕ) (ls : ℕ) : ℕ → Sweep → Sweep
  | 0, S => S
  | k + 1, S =>
    match sweepStep N level ls S with
    | none => S
    | some S' => sweepSteps N level ls k S'

/-- **Enough steps for one sweep**: each step adds a path, advances a pointer, or moves one level
deeper. A phase adds at most one path per residual arrow, each of the `n` vertices advances its
pointer at most once per residual arrow, and between two of these the sweep moves deeper fewer
than `n` times. -/
def sweepFuel (N : Network) : ℕ := (N.g.n + 1) * (2 * N.g.arrows.length * (N.g.n + 1) + 1)

/-- The steps of the sweep from `S`, at most `k`, the last one (which finds the source a dead
end) included. -/
def sweepCount (N : Network) (level : ℕ → Option ℕ) (ls : ℕ) : ℕ → Sweep → ℕ
  | 0, _ => 0
  | k + 1, S =>
    match sweepStep N level ls S with
    | none => 1
    | some S' => sweepCount N level ls k S' + 1

/-- **One phase**: levels by the search; if the sink is labeled, one sweep from the zero
pointers. -/
def dinicPhase (N : Network) (f : Flow) : List Augmentation :=
  let L := search N f 1
  match L.level N.sink with
  | none => []
  | some ls => (sweepSteps N L.level ls (sweepFuel N) ⟨f, fun _ => 0, [], []⟩).sent

/-- **The steps of one phase's sweep**, the last one included; 0 when the search misses the sink.
-/
def dinicSweepSteps (N : Network) (f : Flow) : ℕ :=
  let L := search N f 1
  match L.level N.sink with
  | none => 0
  | some ls => sweepCount N L.level ls (sweepFuel N) ⟨f, fun _ => 0, [], []⟩

/-- **Dinic's path rule**: a round is one phase, the paths of a blocking flow along the levels. -/
def dinic : PathRule where
  Memory := Unit
  start _ := ()
  round N _ f := ((), dinicPhase N f)

/-! ## Admissible arrows and dead ends -/

theorem admissible_iff {N : Network} {g : Flow} {level : ℕ → Option ℕ} {a : ResidualArrow} :
    admissible N g level a = true ↔ 0 < a.residualCapacity N g ∧ LevelUp N level a := by
  unfold admissible LevelUp
  cases level (a.tail N) <;> simp

/-- A path of admissible arrows goes one level deeper per arrow. -/
theorem levelUp_path_level {N : Network} {level : ℕ → Option ℕ} :
    ∀ (q : List ResidualArrow) (w v l : ℕ), ends N w q = some v → (∀ c ∈ q, LevelUp N level c) →
      level w = some l → level v = some (l + q.length)
  | [], w, v, l, he, _, hl => by simp only [ends, Option.some.injEq] at he; simpa [← he] using hl
  | a :: q, w, v, l, he, hq, hl => by
    simp only [ends] at he
    split_ifs at he with ha
    obtain ⟨l', hl', hh⟩ := hq a (by simp)
    rw [ha.2, hl, Option.some.injEq] at hl'
    subst hl'
    have := levelUp_path_level q _ v (l + 1) he (fun c hc => hq c (by simp [hc])) hh
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- **A dead end**: no path of admissible arrows leads from `w` to the sink. -/
def Dead (N : Network) (g : Flow) (level : ℕ → Option ℕ) (w : ℕ) : Prop :=
  ∀ q, ends N w q = some N.sink → ¬ ∀ c ∈ q, admissible N g level c = true

/-- A vertex on the sink's level, other than the sink, is a dead end. -/
theorem dead_of_level {N : Network} {g : Flow} {level : ℕ → Option ℕ} {ls w : ℕ}
    (hls : level N.sink = some ls) (hw : level w = some ls) (hws : w ≠ N.sink) :
    Dead N g level w := by
  intro q he hq
  have := levelUp_path_level q w N.sink ls he (fun c hc => (admissible_iff.1 (hq c hc)).2) hw
  rw [hls, Option.some.injEq] at this
  obtain rfl : q = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp only [ends, Option.some.injEq] at he
  exact hws he

/-- A vertex other than the sink each of whose arrows is not admissible, or leads to a dead end,
is a dead end. -/
theorem dead_of_all {N : Network} {g : Flow} {level : ℕ → Option ℕ} {w : ℕ} (hws : w ≠ N.sink)
    (hall : ∀ a ∈ N.residualOut w, admissible N g level a = false ∨ Dead N g level (a.head N)) :
    Dead N g level w := by
  intro q he hq
  cases q with
  | nil => simp only [ends, Option.some.injEq] at he; exact hws he
  | cons a q =>
    simp only [ends] at he
    split_ifs at he with ha
    rcases hall a (mem_residualOut.2 ha) with h | h
    · simp [hq a (by simp)] at h
    · exact h q he fun c hc => hq c (by simp [hc])

/-! ## Counting -/

theorem length_residualOut_le (N : Network) (v : ℕ) :
    (N.residualOut v).length ≤ 2 * N.g.arrows.length := by
  unfold Network.residualOut
  rw [List.length_flatMap]
  have := List.sum_le_length_nsmul ((N.ids).map fun i =>
    ((if N.tail i = v then [ResidualArrow.along i] else []) ++
      (if N.head i = v then [ResidualArrow.back i] else [])).length) 2 (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    simp only [List.length_append]
    split_ifs <;> simp)
  simpa [Network.ids, Nat.mul_comm] using this

/-- A residual arrow as a number below `2m`: `along i` is `2i`, `back i` is `2i + 1`. -/
def ResidualArrow.code : ResidualArrow → ℕ
  | .along i => 2 * i
  | .back i => 2 * i + 1

theorem ResidualArrow.code_injective : Function.Injective ResidualArrow.code := by
  intro a b h
  cases a <;> cases b <;> simp [ResidualArrow.code] at h ⊢ <;> omega

/-- Distinct residual arrows of the network number at most `2m`. -/
theorem length_le_of_nodup {N : Network} {l : List ResidualArrow} (hn : l.Nodup)
    (hl : ∀ a ∈ l, a.id < N.g.arrows.length) : l.length ≤ 2 * N.g.arrows.length := by
  have hsub : l.map ResidualArrow.code ⊆ List.range (2 * N.g.arrows.length) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have := hl a ha
    cases a <;> simp [ResidualArrow.code, ResidualArrow.id] at this ⊢ <;> omega
  have := (List.subperm_of_subset (hn.map ResidualArrow.code_injective) hsub).length_le
  simpa using this

/-! ## What the sweep keeps -/

/-- **What the sweep keeps**, for the flow `f` at the start of the phase and the levels `level`:
the paths added so far fit in turn and carry at least 1 each, and the flow is what they sent; the
arrows taken climb the levels with room; each added path emptied a different admissible arrow;
the pointers stay within their vertices' arrows; each arrow taken is its tail's current arrow;
every arrow a pointer has passed is not admissible or leads to a dead end; and an arrow with room
had room at the start of the phase, or is the way back of an arrow one level up. -/
structure SweepInv (N : Network) (f : Flow) (level : ℕ → Option ℕ) (S : Sweep) : Prop where
  fit : FitInTurn N f S.sent
  flow : S.flow = applyAll f S.sent
  amounts : ∀ x ∈ S.sent, 1 ≤ x.amount
  path : Climbs N level (fun a => 0 < a.residualCapacity N S.flow) S.path.reverse (S.at N)
  sat : ∃ l : List ResidualArrow, l.Nodup ∧ l.length = S.sent.length ∧
    ∀ a ∈ l, a.id < N.g.arrows.length ∧ a.residualCapacity N S.flow = 0 ∧ LevelUp N level a
  ptrLe : ∀ v, S.ptr v ≤ (N.residualOut v).length
  ptrOut : ∀ v, N.g.n ≤ v → S.ptr v = 0
  current : ∀ a ∈ S.path, (N.residualOut (a.tail N))[S.ptr (a.tail N)]? = some a
  dead : ∀ v j a, j < S.ptr v → (N.residualOut v)[j]? = some a →
    admissible N S.flow level a = false ∨ Dead N S.flow level (a.head N)
  grow : ∀ c, 0 < c.residualCapacity N S.flow →
    0 < c.residualCapacity N f ∨ ∃ d, d ≠ c ∧ d.id = c.id ∧ LevelUp N level d

/-- What only grows during the sweep: the pointers, weighed above the paths added, and the arrows
taken. -/
def Sweep.potential (N : Network) (S : Sweep) : ℕ :=
  (N.g.n + 1) * (((List.range N.g.n).map S.ptr).sum + S.sent.length) + S.path.length

theorem sweepInv_start {N : Network} {f : Flow} {level : ℕ → Option ℕ}
    (hsrc : level N.source = some 0) : SweepInv N f level ⟨f, fun _ => 0, [], []⟩ where
  fit := trivial
  flow := rfl
  amounts := by simp
  path := Climbs.nil hsrc
  sat := ⟨[], by simp⟩
  ptrLe := by simp
  ptrOut := by simp
  current := by simp
  dead := by simp
  grow _ h := Or.inl h

theorem Sweep.at_of_ends {N : Network} {S : Sweep} {t : ℕ}
    (h : ends N N.source S.path.reverse = some t) : S.at N = t := by
  unfold Sweep.at
  split
  · rename_i hp
    simpa [hp, ends] using h
  · rename_i c rest hp
    rw [hp, List.reverse_cons] at h
    obtain ⟨_, _, _, _, e⟩ := ends_snoc h
    exact e

theorem SweepInv.isFlow {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {level : ℕ → Option ℕ} {S : Sweep} (hI : SweepInv N f level S) : IsFlow N S.flow := by
  rw [hI.flow]; exact (applyAll_isFlow h hf hI.fit).1

theorem SweepInv.flow_of_nil {N : Network} {f : Flow} {level : ℕ → Option ℕ} {S : Sweep}
    (hI : SweepInv N f level S) (h0 : S.sent = []) : S.flow = f := by
  rw [hI.flow, h0]; rfl

theorem SweepInv.at_lt {N : Network} (h : N.WellFormed) {f : Flow} {level : ℕ → Option ℕ}
    {S : Sweep} (hI : SweepInv N f level S) : S.at N < N.g.n :=
  ends_visits_lt h _ _ _ h.2.2.1 hI.path.1 _ (mem_visits_end hI.path.1)

theorem SweepInv.sent_le {N : Network} {f : Flow} {level : ℕ → Option ℕ} {S : Sweep}
    (hI : SweepInv N f level S) : S.sent.length ≤ 2 * N.g.arrows.length := by
  obtain ⟨l, hn, hl, ha⟩ := hI.sat
  exact hl ▸ length_le_of_nodup hn fun a h => (ha a h).1

/-- **The potential stays bounded**. -/
theorem SweepInv.potential_le {N : Network} (h : N.WellFormed) {f : Flow} {level : ℕ → Option ℕ}
    {S : Sweep} (hI : SweepInv N f level S) :
    S.potential N < sweepFuel N := by
  have h1 := sum_range_le (b := 2 * N.g.arrows.length)
    (fun v => (hI.ptrLe v).trans (length_residualOut_le N v)) N.g.n
  have h2 := hI.sent_le
  have h3 : S.path.length < N.g.n := by
    have := hI.path.length_lt h; simpa using this
  unfold Sweep.potential sweepFuel
  have h4 : (N.g.n + 1) * (((List.range N.g.n).map S.ptr).sum + S.sent.length) ≤
      (N.g.n + 1) * (N.g.n * (2 * N.g.arrows.length) + 2 * N.g.arrows.length) :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 : (N.g.n + 1) * (2 * N.g.arrows.length * (N.g.n + 1) + 1) =
      (N.g.n + 1) * (N.g.n * (2 * N.g.arrows.length) + 2 * N.g.arrows.length) + (N.g.n + 1) := by
    ring
  omega

/-- Sending along a climbing path gives no arrow one level up more room. -/
theorem residualCapacity_apply_le {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {x : Augmentation} {g : Flow} {v : ℕ} (hp : Climbs N level ok x.path v)
    (hl : ∀ c ∈ x.path, c.id < g.length) {a : ResidualArrow} (ha : LevelUp N level a) :
    a.residualCapacity N (x.apply g) ≤ a.residualCapacity N g := by
  by_cases hm : a.id ∈ x.path.map (·.id)
  · obtain ⟨d, hd, hda⟩ := List.mem_map.1 hm
    by_cases e : d = a
    · subst e
      rw [residualCapacity_apply_mem N hl hp.ids_nodup hd]
      omega
    · exact (ha.not_of_id_eq (hp.levelUp d hd) hda e).elim
  · rw [residualCapacity_apply_not_mem N hl hm]

/-- After sending along a climbing path, an arrow with room had room before, or is the way back
of an arrow of the path. -/
theorem residualCapacity_apply_grow {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {x : Augmentation} {g : Flow} {v : ℕ} (hp : Climbs N level ok x.path v)
    (hl : ∀ c ∈ x.path, c.id < g.length) {a : ResidualArrow}
    (ha : 0 < a.residualCapacity N (x.apply g)) :
    0 < a.residualCapacity N g ∨ ∃ d, d ≠ a ∧ d.id = a.id ∧ LevelUp N level d := by
  by_cases hm : a.id ∈ x.path.map (·.id)
  · obtain ⟨d, hd, hda⟩ := List.mem_map.1 hm
    by_cases e : d = a
    · subst e
      rw [residualCapacity_apply_mem N hl hp.ids_nodup hd] at ha
      exact Or.inl (by omega)
    · exact Or.inr ⟨d, e, hda, hp.levelUp d hd⟩
  · rw [residualCapacity_apply_not_mem N hl hm] at ha
    exact Or.inl ha

theorem admissible_of_apply {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {x : Augmentation} {g : Flow} {v : ℕ} (hp : Climbs N level ok x.path v)
    (hl : ∀ c ∈ x.path, c.id < g.length) {a : ResidualArrow}
    (ha : admissible N (x.apply g) level a = true) : admissible N g level a = true := by
  obtain ⟨hr, hu⟩ := admissible_iff.1 ha
  exact admissible_iff.2 ⟨lt_of_lt_of_le hr (residualCapacity_apply_le hp hl hu), hu⟩

theorem Dead.apply {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {x : Augmentation} {g : Flow} {v w : ℕ} (hp : Climbs N level ok x.path v)
    (hl : ∀ c ∈ x.path, c.id < g.length) (hd : Dead N g level w) : Dead N (x.apply g) level w :=
  fun q he hq => hd q he fun c hc => admissible_of_apply hp hl (hq c hc)

theorem mul_succ_eq (n a : ℕ) : (n + 1) * (a + 1) = (n + 1) * a + (n + 1) := by ring

theorem mul_add_one_add (n a b : ℕ) : (n + 1) * (a + 1 + b) = (n + 1) * (a + b) + (n + 1) := by
  ring

/-- **One step keeps what the sweep keeps, and raises the potential.** -/
theorem SweepInv.step {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {level : ℕ → Option ℕ} {ls : ℕ} (hsrc : level N.source = some 0)
    (hls : level N.sink = some ls) {S S' : Sweep}
    (hI : SweepInv N f level S) (hs : sweepStep N level ls S = some S') :
    SweepInv N f level S' ∧ S.potential N + 1 ≤ S'.potential N := by
  have hlen : S.flow.length = N.g.arrows.length := (hI.isFlow h hf).2.2
  have hvn := hI.at_lt h
  have hpn : S.path.length < N.g.n := by have := hI.path.length_lt h; simpa using this
  simp only [sweepStep] at hs
  split_ifs at hs with hsink hcond hadm
  · -- at the sink: add the path
    injection hs with hs
    subst hs
    have hc := hsink ▸ hI.path
    have hsend := byBottleneck_sends h hc fun _ ha => ha
    have hids : ∀ c ∈ S.path.reverse, c.id < S.flow.length := fun c hc' =>
      hlen ▸ ends_ids_lt hc.1 c hc'
    refine ⟨⟨fitInTurn_append_one hI.fit (hI.flow ▸ hsend.1), ?_, ?_, ?_, ?_, hI.ptrLe, hI.ptrOut,
      by simp, ?_, ?_⟩, ?_⟩
    · simp [applyAll_append_one, hI.flow]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hI.amounts x hx
      · rw [List.mem_singleton.1 hx]; exact hsend.2
    · exact Climbs.nil hsrc
    · obtain ⟨l, hn, hl, ha⟩ := hI.sat
      obtain ⟨b, hb, hbr⟩ := bottleneck_mem (f := S.flow) (N := N) (ne_nil_of_ends h hc.1)
      refine ⟨b :: l, ?_, by simp [hl], ?_⟩
      · refine List.nodup_cons.2 ⟨fun hbl => ?_, hn⟩
        have : 0 < b.residualCapacity N S.flow := hc.2.2 b hb
        rw [(ha b hbl).2.1] at this
        exact absurd this (lt_irrefl 0)
      · intro a ha'
        rcases List.mem_cons.1 ha' with rfl | ha'
        · refine ⟨ends_ids_lt hc.1 a hb, ?_, hc.levelUp a hb⟩
          rw [residualCapacity_apply_mem N hids hc.ids_nodup hb]
          simp [byBottleneck, hbr]
        · obtain ⟨hid, hr0, hup⟩ := ha a ha'
          refine ⟨hid, ?_, hup⟩
          rw [residualCapacity_apply_not_mem N hids]
          · exact hr0
          · intro hm
            obtain ⟨c, hcp, hce⟩ := List.mem_map.1 hm
            by_cases hca : c = a
            · subst hca
              have : 0 < c.residualCapacity N S.flow := hc.2.2 c hcp
              rw [hr0] at this
              exact lt_irrefl 0 this
            · exact hup.not_of_id_eq (hc.levelUp c hcp) hce hca
    · intro v j a hj ha
      rcases hI.dead v j a hj ha with hn | hn
      · left
        by_contra hy
        have := admissible_of_apply (x := byBottleneck N S.flow S.path.reverse) hc hids
          (Bool.not_eq_false _ ▸ hy)
        simp [hn] at this
      · exact Or.inr (hn.apply (x := byBottleneck N S.flow S.path.reverse) hc hids)
    · intro c hc'
      rcases residualCapacity_apply_grow (x := byBottleneck N S.flow S.path.reverse) hc hids
        hc' with hn | hn
      · exact hI.grow c hn
      · exact Or.inr hn
    · unfold Sweep.potential
      simp only [List.length_append, List.length_singleton, List.length_nil]
      rw [← Nat.add_assoc, mul_succ_eq]
      omega
  · -- move along the current arrow
    injection hs with hs
    subst hs
    set v := S.at N with hv
    set a := (N.residualOut v).getD (S.ptr v) (.along 0) with ha
    have hget : (N.residualOut v)[S.ptr v]? = some a := by
      rw [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcond.2, Option.getD_some]
    obtain ⟨hid, htail⟩ := mem_residualOut.1 (List.mem_of_getElem? hget)
    obtain ⟨hroom, l, hl, hl'⟩ := admissible_iff.1 hadm
    have hlv := hI.path.level_end
    rw [htail, hlv, Option.some.injEq] at hl
    refine ⟨⟨hI.fit, hI.flow, hI.amounts, ?_, hI.sat, hI.ptrLe, hI.ptrOut, ?_, hI.dead, hI.grow⟩,
      ?_⟩
    · change Climbs N level _ (a :: S.path).reverse (a.head N)
      rw [List.reverse_cons]
      exact hI.path.snoc hid htail (by rw [hl', ← hl]) hroom
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · rw [htail]; exact hget
      · exact hI.current c hc
    · simp only [Sweep.potential, List.length_cons]
      omega
  · -- advance the pointer
    injection hs with hs
    subst hs
    set v := S.at N with hv
    set a := (N.residualOut v).getD (S.ptr v) (.along 0) with ha
    have hget : (N.residualOut v)[S.ptr v]? = some a := by
      rw [ha, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcond.2, Option.getD_some]
    refine ⟨⟨hI.fit, hI.flow, hI.amounts, hI.path, hI.sat, ?_, ?_, ?_, ?_, hI.grow⟩, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hw]; exact hI.ptrLe w
    · intro w hw
      have hwv : w ≠ v := by omega
      simp only [Function.update_of_ne hwv]; exact hI.ptrOut w hw
    · intro c hc
      have hcv : c.tail N ≠ v := hI.path.tail_ne (List.mem_reverse.2 hc)
      simp only [Function.update_of_ne hcv]; exact hI.current c hc
    · intro w j b hj hb
      by_cases hw : w = v
      · rw [hw] at hj hb
        dsimp only at hj
        rw [Function.update_self] at hj
        by_cases hjv : j = S.ptr v
        · rw [hjv, hget, Option.some.injEq] at hb
          subst hb
          left
          simpa using hadm
        · exact hI.dead v j b (by omega) hb
      · simp only [Function.update_of_ne hw] at hj
        exact hI.dead w j b hj hb
    · simp only [Sweep.potential]
      rw [sum_range_bump _ hvn, mul_add_one_add]
      omega
  · -- a dead end: step back
    split at hs
    · simp at hs
    · rename_i c rest hp
      injection hs with hs
      subst hs
      have hcl : Climbs N level (fun a => 0 < a.residualCapacity N S.flow) (rest.reverse ++ [c])
          (S.at N) := by
        rw [← List.reverse_cons, ← hp]; exact hI.path
      obtain ⟨hcr, -, hhead, -, -⟩ := hcl.dropLast
      have hat : Sweep.at N ⟨S.flow, Function.update S.ptr (c.tail N) (S.ptr (c.tail N) + 1),
          rest, S.sent⟩ = c.tail N := Sweep.at_of_ends hcr.1
      have hcur : (N.residualOut (c.tail N))[S.ptr (c.tail N)]? = some c :=
        hI.current c (by simp [hp])
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hcur
      have htn : c.tail N < N.g.n :=
        ends_visits_lt h _ _ _ h.2.2.1 hcr.1 _ (mem_visits_end hcr.1)
      refine ⟨⟨hI.fit, hI.flow, hI.amounts, ?_, hI.sat, ?_, ?_, ?_, ?_, hI.grow⟩, ?_⟩
      · change Climbs N level _ rest.reverse (Sweep.at N _)
        rw [hat]; exact hcr
      · intro w
        by_cases hw : w = c.tail N
        · subst hw; simp only [Function.update_self]; omega
        · simp only [Function.update_of_ne hw]; exact hI.ptrLe w
      · intro w hw
        have hwv : w ≠ c.tail N := by omega
        simp only [Function.update_of_ne hwv]; exact hI.ptrOut w hw
      · intro d hd
        have hdv : d.tail N ≠ c.tail N := hcr.tail_ne (List.mem_reverse.2 hd)
        simp only [Function.update_of_ne hdv]; exact hI.current d (by simp [hp, hd])
      · intro w j b hj hb
        by_cases hw : w = c.tail N
        · rw [hw] at hj hb
          dsimp only at hj
          rw [Function.update_self] at hj
          by_cases hjv : j = S.ptr (c.tail N)
          · rw [hjv, hcur, Option.some.injEq] at hb
            subst hb
            right
            rw [hhead]
            by_cases hlv : level (S.at N) = some ls
            · exact dead_of_level hls hlv hsink
            · have hge : (N.residualOut (S.at N)).length ≤ S.ptr (S.at N) := by
                by_contra hc'; exact hcond ⟨hlv, by omega⟩
              refine dead_of_all hsink fun a ha => ?_
              obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
              obtain ⟨hk', -⟩ := List.getElem?_eq_some_iff.1 hk
              exact hI.dead _ k a (by omega) hk
          · exact hI.dead _ j b (by omega) hb
        · dsimp only at hj
          simp only [Function.update_of_ne hw] at hj
          exact hI.dead w j b hj hb
      · simp only [Sweep.potential, hp, List.length_cons]
        rw [sum_range_bump _ htn, mul_add_one_add]
        omega

theorem SweepInv.steps {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {level : ℕ → Option ℕ} {ls : ℕ} (hsrc : level N.source = some 0)
    (hls : level N.sink = some ls) :
    ∀ (k : ℕ) (S : Sweep), SweepInv N f level S →
      SweepInv N f level (sweepSteps N level ls k S) ∧
        (sweepStep N level ls (sweepSteps N level ls k S) ≠ none →
          S.potential N + k ≤ (sweepSteps N level ls k S).potential N)
  | 0, S, hI => ⟨hI, fun _ => by simp [sweepSteps]⟩
  | k + 1, S, hI => by
    unfold sweepSteps
    split
    · rename_i hn
      exact ⟨hI, fun hs => absurd hn hs⟩
    · rename_i S' hS'
      obtain ⟨hI', hp⟩ := hI.step h hf hsrc hls hS'
      obtain ⟨hI'', hk⟩ := SweepInv.steps h hf hsrc hls k S' hI'
      exact ⟨hI'', fun hs => by have := hk hs; omega⟩

/-- The sweep never runs out of steps: with `sweepFuel` steps it ends with the source a dead end. -/
theorem sweepSteps_ends {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    {ls : ℕ} (hls : (search N f 1).level N.sink = some ls) :
    sweepStep N (search N f 1).level ls
      (sweepSteps N (search N f 1).level ls (sweepFuel N) ⟨f, fun _ => 0, [], []⟩) = none := by
  have hsrc := (Labels.sound_search N f 1).1
  obtain ⟨hI, hk⟩ := SweepInv.steps h hf hsrc hls (sweepFuel N) _ (sweepInv_start hsrc)
  by_contra hs
  have h1 := hk hs
  have h2 := hI.potential_le h
  omega

/-- **When the sweep ends, the source is a dead end.** -/
theorem SweepInv.source_dead {N : Network} {f : Flow} {level : ℕ → Option ℕ} {ls : ℕ}
    (hls : level N.sink = some ls) {S : Sweep} (hI : SweepInv N f level S)
    (hnone : sweepStep N level ls S = none) : Dead N S.flow level N.source := by
  simp only [sweepStep] at hnone
  split_ifs at hnone with hsink hcond hadm
  split at hnone
  · rename_i hpath
    have hat : S.at N = N.source := by simp [Sweep.at, hpath]
    rw [← hat]
    by_cases hlv : level (S.at N) = some ls
    · exact dead_of_level hls hlv hsink
    · have hge : (N.residualOut (S.at N)).length ≤ S.ptr (S.at N) := by
        by_contra hc'; exact hcond ⟨hlv, by omega⟩
      refine dead_of_all hsink fun a ha => ?_
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
      obtain ⟨hk', -⟩ := List.getElem?_eq_some_iff.1 hk
      exact hI.dead _ k a (by omega) hk
  · simp at hnone

/-- **A sweep that adds nothing ends only if no admissible path is left.** -/
theorem SweepInv.sent_ne_nil {N : Network} {f : Flow} {level : ℕ → Option ℕ} {ls : ℕ}
    (hls : level N.sink = some ls) {S : Sweep} (hI : SweepInv N f level S)
    (hnone : sweepStep N level ls S = none)
    (hp : ∃ p, ends N N.source p = some N.sink ∧ ∀ c ∈ p, admissible N f level c = true) :
    S.sent ≠ [] := by
  intro h0
  have hd := hI.source_dead hls hnone
  rw [hI.flow_of_nil h0] at hd
  obtain ⟨p, hpe, hpa⟩ := hp
  exact hd p hpe hpa

/-- **What one phase adds**: paths that fit in turn, each carrying at least 1, at most one per
residual arrow; and nothing only when the search misses the sink. -/
theorem dinicPhase_spec {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f) :
    FitInTurn N f (dinicPhase N f) ∧ (∀ x ∈ dinicPhase N f, 1 ≤ x.amount) ∧
      (dinicPhase N f).length ≤ 2 * N.g.arrows.length ∧
      (dinicPhase N f = [] → (search N f 1).level N.sink = none) := by
  dsimp only [dinicPhase]
  split
  · rename_i hn
    exact ⟨trivial, by simp, by simp, fun _ => hn⟩
  · rename_i ls hls
    have hsrc := (Labels.sound_search N f 1).1
    obtain ⟨hI, -⟩ := SweepInv.steps h hf hsrc hls (sweepFuel N) _ (sweepInv_start hsrc)
    refine ⟨hI.fit, hI.amounts, hI.sent_le, fun h0 => absurd h0 (hI.sent_ne_nil hls
      (sweepSteps_ends h hf hls) ?_)⟩
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
      (shortestPath_isSome h (Option.isSome_iff_exists.2 ⟨ls, hls⟩))
    have hc := shortestPath_climbs h hp
    exact ⟨p, hc.1, fun c hc' => admissible_iff.2 ⟨(hc.2.2 c hc').1, hc.levelUp c hc'⟩⟩

/-- Dinic's rule keeps the promise of every path rule. -/
theorem dinic_promise : dinic.Promise where
  sendsAlong _ h _ _ hf := (dinicPhase_spec h hf).1
  addsAtLeastOne _ h _ _ hf := (dinicPhase_spec h hf).2.1
  noneOnlyWhenDone _ h _ _ hf hr p hp :=
    search_complete h ((dinicPhase_spec h hf).2.2.2 hr) p hp.1 fun a ha =>
      fits_of_le_one le_rfl (hp.2.2 a ha)

/-- **At most one path per residual arrow** in a round of Dinic's rule. -/
theorem dinic_paths_per_round : ∀ N : Network, N.WellFormed → ∀ m f, IsFlow N f →
    (dinic.round N m f).2.length ≤ 2 * N.g.arrows.length :=
  fun _ h _ _ hf => (dinicPhase_spec h hf).2.2.1

/-! ## Each phase lengthens the shortest path -/

theorem Labels.cut_lt {L : Labels} {ls v : ℕ} (h : L.cut ls v < ls) :
    L.level v = some (L.cut ls v) := by
  unfold Labels.cut at h ⊢
  cases hv : L.level v with
  | none => simp [hv] at h
  | some l => simp [hv] at h ⊢; omega

/-- After the sweep, the cut levels of the phase still rise by at most one along every arrow with
room: a new arrow with room is the way back of an arrow one level up. -/
theorem SweepInv.cut_rises {N : Network} (h : N.WellFormed) {f : Flow} {ls : ℕ}
    (hls : (search N f 1).level N.sink = some ls) {S : Sweep}
    (hI : SweepInv N f (search N f 1).level S) (c : ResidualArrow)
    (hc : c.id < N.g.arrows.length) (hr : 0 < c.residualCapacity N S.flow) :
    (search N f 1).cut ls (c.head N) ≤ (search N f 1).cut ls (c.tail N) + 1 := by
  rcases hI.grow c hr with h0 | ⟨d, hne, hid, l, hl, hl'⟩
  · exact search_cut_rises h hls c hc (fits_of_le_one le_rfl h0)
  · obtain ⟨ht, hh⟩ := ResidualArrow.ends_of_partner N hne hid
    rw [ht, hh]
    simp only [Labels.cut, hl, hl', Option.getD_some]
    omega

/-- A path of arrows with room as short as the cut levels allow is admissible. -/
theorem tight_admissible {N : Network} {g : Flow} {L : Labels} {ls : ℕ}
    (hls : L.level N.sink = some ls)
    (hT : ∀ c : ResidualArrow, c.id < N.g.arrows.length → 0 < c.residualCapacity N g →
      L.cut ls (c.head N) ≤ L.cut ls (c.tail N) + 1) :
    ∀ (q : List ResidualArrow) (w : ℕ), ends N w q = some N.sink →
      (∀ c ∈ q, 0 < c.residualCapacity N g) →
      L.cut ls N.sink = L.cut ls w + q.length → ∀ c ∈ q, admissible N g L.level c = true
  | [], _, _, _, _, c, hc => absurd hc List.not_mem_nil
  | c :: q, w, he, hq, heq, d, hd => by
    simp only [ends] at he
    split_ifs at he with hc
    have h1 := hT c hc.1 (hq c (by simp))
    have h2 := le_of_rises hT q _ _ he fun e he' => hq e (by simp [he'])
    have hsink : L.cut ls N.sink = ls := by simp [Labels.cut, hls]
    rw [hc.2] at h1
    simp only [List.length_cons] at heq
    rcases List.mem_cons.1 hd with rfl | hd
    · refine admissible_iff.2 ⟨hq d (by simp), L.cut ls w, ?_, ?_⟩
      · rw [hc.2]; exact Labels.cut_lt (by omega)
      · by_cases hlt : L.cut ls (d.head N) < ls
        · rw [Labels.cut_lt hlt]; congr 1; omega
        · obtain rfl : q = [] := List.eq_nil_of_length_eq_zero (by omega)
          simp only [ends, Option.some.injEq] at he
          rw [he, hls]; congr 1; omega
    · exact tight_admissible hls hT q _ he (fun e he' => hq e (by simp [he'])) (by omega) d hd

/-- **One phase lengthens the shortest path**: when a phase adds paths, the sink was `ls` arrows
away, fewer than the vertices, and afterwards every path with room has more than `ls` arrows. -/
theorem dinicPhase_next {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f)
    (hne : dinicPhase N f ≠ []) : ∃ ls, (∃ p, IsAugmentingPath N f p ∧ p.length = ls) ∧
      ls < N.g.n ∧ ∀ q, ends N N.source q = some N.sink →
        (∀ c ∈ q, 0 < c.residualCapacity N (applyAll f (dinicPhase N f))) → ls + 1 ≤ q.length := by
  dsimp only [dinicPhase] at hne ⊢
  split at hne
  · exact absurd rfl hne
  · rename_i ls hls
    have hsrc := (Labels.sound_search N f 1).1
    obtain ⟨hI, -⟩ := SweepInv.steps h hf hsrc hls (sweepFuel N) _ (sweepInv_start hsrc)
    set S := sweepSteps N (search N f 1).level ls (sweepFuel N) ⟨f, fun _ => 0, [], []⟩
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
      (shortestPath_isSome h (Option.isSome_iff_exists.2 ⟨ls, hls⟩))
    have hc := shortestPath_climbs h hp
    have hpl : p.length = ls := by
      have := hc.level_end; rw [hls, Option.some.injEq] at this; exact this.symm
    refine ⟨ls, ⟨p, hc.isAugmentingPath fun _ ha => ha.1, hpl⟩, hpl ▸ hc.length_lt h,
      fun q hq hr => ?_⟩
    rw [← hI.flow] at hr
    have hT := hI.cut_rises h hls
    have hle := le_of_rises hT q _ _ hq hr
    have hsink : (search N f 1).cut ls N.sink = ls := by simp [Labels.cut, hls]
    have h0 : (search N f 1).cut ls N.source = 0 := by simp [Labels.cut, hsrc]
    by_contra hlt
    have hdead := hI.source_dead hls (sweepSteps_ends h hf hls)
    exact hdead q hq (tight_admissible hls hT q _ hq hr (by omega))

/-- The rounds from a flow whose paths with room all have at least `D` arrows number at most
`n - D`. -/
theorem dinic_runRounds_le {N : Network} (h : N.WellFormed) :
    ∀ (k : ℕ) (g : Flow) (D : ℕ), IsFlow N g → D ≤ N.g.n →
      (∀ q, ends N N.source q = some N.sink → (∀ c ∈ q, 0 < c.residualCapacity N g) →
        D ≤ q.length) →
      (dinic.runRounds N k () g).1.length + D ≤ N.g.n
  | 0, _, _, _, hD, _ => by simpa [PathRule.runRounds] using hD
  | k + 1, g, D, hg, hD, hlb => by
    cases hp : dinicPhase N g with
    | nil =>
      rw [dinic.runRounds_nil N k (m' := ()) (show dinic.round N () g = ((), []) by
        change ((), dinicPhase N g) = _; rw [hp])]
      simpa using hD
    | cons x xs =>
      rw [dinic.runRounds_cons N k (m' := ()) (show dinic.round N () g = ((), x :: xs) by
        change ((), dinicPhase N g) = _; rw [hp])]
      obtain ⟨ls, ⟨p, hpa, hpl⟩, hlt, hnext⟩ := dinicPhase_next h hg (by simp [hp])
      have hDl : D ≤ ls := hpl ▸ hlb p hpa.1 hpa.2.2
      have hfit := (dinicPhase_spec h hg).1
      rw [hp] at hfit hnext
      have := dinic_runRounds_le h k _ (ls + 1) (applyAll_isFlow h hg hfit).1 (by omega) hnext
      simp only [List.length_cons]
      omega

/-- **At most n rounds** with Dinic's rule. -/
theorem dinic_rounds : (dinic.ops dinic_promise).RoundsAtMostN := by
  intro N h
  have := dinic_runRounds_le h (totalCapacity N + 1) (Flow.zero N) 0 (zero_isFlow N)
    (Nat.zero_le _) fun _ _ _ => Nat.zero_le _
  exact this

/-- **A bound set by the network's size alone** with Dinic's rule: at most n rounds of at most
2m paths each. -/
theorem dinic_bound : (dinic.ops dinic_promise).BoundSetBySize := by
  refine ⟨fun n m => n * (2 * m), fun N h => ?_⟩
  have heach := PathRule.runRounds_each dinic_promise h
    (fun m g hg => dinic_paths_per_round N h m g hg) (totalCapacity N + 1) () (Flow.zero N)
    (zero_isFlow N)
  have := length_flatten_le heach
  have hr := dinic_rounds N h
  exact this.trans (Nat.mul_le_mul_right _ hr)

/-! ## At most one path per arrow in a round, and the sweep's steps

Of an arrow and its way back, at most one steps one level up, so the arrows a phase's paths empty
are different arrows of the network, not only different residual arrows. -/

/-- **Distinct residual arrows that each step one level up number at most `m`**: of an arrow and
its way back, at most one steps one level up. -/
theorem length_le_of_levelUp {N : Network} {level : ℕ → Option ℕ} {l : List ResidualArrow}
    (hn : l.Nodup) (hl : ∀ a ∈ l, a.id < N.g.arrows.length ∧ LevelUp N level a) :
    l.length ≤ N.g.arrows.length := by
  have hinj : (l.map ResidualArrow.id).Nodup := by
    refine hn.map_on fun a ha c hc e => ?_
    by_contra hne
    exact LevelUp.not_of_id_eq (hl a ha).2 (hl c hc).2 e.symm (Ne.symm hne)
  have hsub : l.map ResidualArrow.id ⊆ List.range N.g.arrows.length := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hl a ha).1
  have := (List.subperm_of_subset hinj hsub).length_le
  simpa using this

/-- The sweep adds at most one path per arrow of the network. -/
theorem SweepInv.sent_le_arrows {N : Network} {f : Flow} {level : ℕ → Option ℕ} {S : Sweep}
    (hI : SweepInv N f level S) : S.sent.length ≤ N.g.arrows.length := by
  obtain ⟨l, hn, hl, ha⟩ := hI.sat
  exact hl ▸ length_le_of_levelUp hn fun a h => ⟨(ha a h).1, (ha a h).2.2⟩

/-- **At most one path per arrow** in a phase of Dinic's rule. -/
theorem dinicPhase_length_le {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f) :
    (dinicPhase N f).length ≤ N.g.arrows.length := by
  dsimp only [dinicPhase]
  split
  · simp
  · rename_i ls hls
    have hsrc := (Labels.sound_search N f 1).1
    exact (SweepInv.steps h hf hsrc hls (sweepFuel N) _ (sweepInv_start hsrc)).1.sent_le_arrows

/-- **At most one path per arrow** in a round of Dinic's rule, `m` for `m` arrows. -/
theorem dinic_paths_per_round_arrows : ∀ N : Network, N.WellFormed → ∀ m f, IsFlow N f →
    (dinic.round N m f).2.length ≤ N.g.arrows.length :=
  fun _ h _ _ hf => dinicPhase_length_le h hf

/-- **At most n·m added paths** with Dinic's rule: at most n rounds of at most m paths each. -/
theorem dinic_augmentations : (dinic.ops dinic_promise).AugmentationsAtMostNM := by
  intro N h
  have heach := PathRule.runRounds_each dinic_promise h
    (fun m g hg => dinic_paths_per_round_arrows N h m g hg) (totalCapacity N + 1) ()
    (Flow.zero N) (zero_isFlow N)
  exact (length_flatten_le heach).trans (Nat.mul_le_mul_right _ (dinic_rounds N h))

/-- A vertex's residual arrows are different. -/
theorem nodup_residualOut (N : Network) (v : ℕ) : (N.residualOut v).Nodup := by
  unfold Network.residualOut
  rw [List.nodup_flatMap]
  have key : ∀ i b, b ∈ (if N.tail i = v then [ResidualArrow.along i] else []) ++
      (if N.head i = v then [ResidualArrow.back i] else []) → b.id = i := by
    intro i b hb
    simp only [List.mem_append] at hb
    rcases hb with hb | hb <;> split_ifs at hb <;> simp_all [ResidualArrow.id]
  refine ⟨fun i _ => ?_, List.nodup_range.pairwise_of_forall_ne fun i _ j _ hij => ?_⟩
  · split_ifs <;> simp
  · exact List.disjoint_left.2 fun _ hb hb' => hij ((key i _ hb).symm.trans (key j _ hb'))

/-- The residual arrows of all the vertices number at most `2m`: each arrow leaves one vertex
along it and one back against it. -/
theorem sum_residualOut_le (N : Network) (n : ℕ) :
    ((List.range n).map fun v => (N.residualOut v).length).sum ≤ 2 * N.g.arrows.length := by
  have hn : ((List.range n).flatMap N.residualOut).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun v _ => nodup_residualOut N v,
      List.nodup_range.pairwise_of_forall_ne fun v _ w _ hvw => ?_⟩
    exact List.disjoint_left.2 fun _ hb hb' =>
      hvw ((mem_residualOut.1 hb).2.symm.trans (mem_residualOut.1 hb').2)
  have := length_le_of_nodup hn fun a ha => by
    obtain ⟨v, -, hv⟩ := List.mem_flatMap.1 ha
    exact (mem_residualOut.1 hv).1
  simpa [List.length_flatMap] using this

/-- **The potential stays below `(n + 1)(3m + 1)`**: the pointers pass at most `2m` arrows in all,
the sweep adds at most `m` paths, and it is fewer than `n` arrows deep. -/
theorem SweepInv.potential_lt {N : Network} (h : N.WellFormed) {f : Flow}
    {level : ℕ → Option ℕ} {S : Sweep} (hI : SweepInv N f level S) :
    S.potential N < (N.g.n + 1) * (3 * N.g.arrows.length + 1) := by
  have h1 : ((List.range N.g.n).map S.ptr).sum ≤ 2 * N.g.arrows.length :=
    (List.sum_le_sum fun v _ => hI.ptrLe v).trans (sum_residualOut_le N N.g.n)
  have h2 := hI.sent_le_arrows
  have h3 : S.path.length < N.g.n := by
    have := hI.path.length_lt h; simpa using this
  unfold Sweep.potential
  have h4 : (N.g.n + 1) * (((List.range N.g.n).map S.ptr).sum + S.sent.length) ≤
      (N.g.n + 1) * (3 * N.g.arrows.length) :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 : (N.g.n + 1) * (3 * N.g.arrows.length + 1) =
      (N.g.n + 1) * (3 * N.g.arrows.length) + (N.g.n + 1) := by ring
  omega

/-- Every step of the sweep raises the potential, so the potential at the start and the steps
counted after it stay within `(n + 1)(3m + 1)`. -/
theorem SweepInv.potential_add_count {N : Network} (h : N.WellFormed) {f : Flow}
    (hf : IsFlow N f) {level : ℕ → Option ℕ} {ls : ℕ} (hsrc : level N.source = some 0)
    (hls : level N.sink = some ls) :
    ∀ (k : ℕ) (S : Sweep), SweepInv N f level S →
      S.potential N + sweepCount N level ls k S ≤ (N.g.n + 1) * (3 * N.g.arrows.length + 1)
  | 0, S, hI => by have := hI.potential_lt h; simp only [sweepCount]; omega
  | k + 1, S, hI => by
    have := hI.potential_lt h
    unfold sweepCount
    split
    · omega
    · rename_i S' hS'
      obtain ⟨hI', hp⟩ := hI.step h hf hsrc hls hS'
      have := SweepInv.potential_add_count h hf hsrc hls k S' hI'
      omega

/-- **One phase's sweep takes at most `(n + 1)(3m + 1)` steps**, the last one included. -/
theorem dinicSweepSteps_le {N : Network} (h : N.WellFormed) {f : Flow} (hf : IsFlow N f) :
    dinicSweepSteps N f ≤ (N.g.n + 1) * (3 * N.g.arrows.length + 1) := by
  dsimp only [dinicSweepSteps]
  split
  · exact Nat.zero_le _
  · rename_i ls hls
    have hsrc := (Labels.sound_search N f 1).1
    have := SweepInv.potential_add_count h hf hsrc hls (sweepFuel N) _ (sweepInv_start hsrc)
    omega

/-- **The sweep steps of the loop's rounds** from the flow `f`, at most `k` rounds, the round that
adds nothing included. -/
def dinicRunSweepSteps (N : Network) : ℕ → Flow → ℕ
  | 0, _ => 0
  | k + 1, f =>
    match dinicPhase N f with
    | [] => dinicSweepSteps N f
    | x :: xs => dinicSweepSteps N f + dinicRunSweepSteps N k (applyAll f (x :: xs))

theorem dinicRunSweepSteps_le {N : Network} (h : N.WellFormed) :
    ∀ (k : ℕ) (g : Flow), IsFlow N g → dinicRunSweepSteps N k g ≤
      ((dinic.runRounds N k () g).1.length + 1) * ((N.g.n + 1) * (3 * N.g.arrows.length + 1))
  | 0, _, _ => Nat.zero_le _
  | k + 1, g, hg => by
    have hs := dinicSweepSteps_le h hg
    cases hp : dinicPhase N g with
    | nil =>
      rw [dinic.runRounds_nil N k (m' := ()) (show dinic.round N () g = ((), []) by
        change ((), dinicPhase N g) = _; rw [hp])]
      simp only [dinicRunSweepSteps, hp, List.length_nil, zero_add, one_mul]
      exact hs
    | cons x xs =>
      rw [dinic.runRounds_cons N k (m' := ()) (show dinic.round N () g = ((), x :: xs) by
        change ((), dinicPhase N g) = _; rw [hp])]
      have hfit := (dinicPhase_spec h hg).1
      rw [hp] at hfit
      have := dinicRunSweepSteps_le h k _ (applyAll_isFlow h hg hfit).1
      simp only [dinicRunSweepSteps, hp, List.length_cons]
      nlinarith

/-- **Dinic's sweeps take `O(n²m)` steps over the whole run**: at most `n + 1` phases, each sweep
at most `(n + 1)(3m + 1)` steps. -/
theorem dinic_sweep_steps_le {N : Network} (h : N.WellFormed) :
    dinicRunSweepSteps N (totalCapacity N + 1) (Flow.zero N) ≤
      (N.g.n + 1) * ((N.g.n + 1) * (3 * N.g.arrows.length + 1)) := by
  refine (dinicRunSweepSteps_le h _ _ (zero_isFlow N)).trans (Nat.mul_le_mul_right _ ?_)
  have := dinic_rounds N h
  change (dinic.runRounds N (totalCapacity N + 1) () (Flow.zero N)).1.length ≤ N.g.n at this
  omega

end AlgoDesign.Flows
