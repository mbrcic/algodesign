/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Basic

/-!
# Cheapest paths: the walk

Source: Weiss, *Data Structures and Algorithm Analysis in C++* (4th ed.), Fig. 9.31 (p. 399): take
the unsettled vertex of smallest known cost, settle it, and for each arrow out of it to an
unsettled vertex, lower that vertex's known cost if the arrow gives less, recording the settled
vertex as its previous one.

The queue keeps every entry it is given, in order (`EntryLe`); a vertex whose cost drops is queued
again, and the old entry stays until it comes off and is skipped.
-/

@[expose] public section

namespace AlgoDesign.Paths.Dijkstra

open Network

/-! ## The walk -/

/-- Put an entry into the queue before the first entry it does not come after. -/
def insertEntry (e : ℤ × ℕ) : List (ℤ × ℕ) → List (ℤ × ℕ)
  | [] => [e]
  | f :: q => if EntryLe e f then e :: f :: q else f :: insertEntry e q

/-- **Try one arrow** `(w, i)` out of `u`, settled at cost `du`: unless `w` is settled, if `w` has
no known cost or the arrow gives less, record the new cost and `u`, and queue the entry. -/
def tryArrow (N : Network) (u : ℕ) (du : ℤ) (st : State) (e : ℕ × ℕ) : State :=
  if e.1 ∈ st.settled then st
  else if (st.known e.1).all (du + N.arrowCost e.2 < ·) then
    { st with
      known := Function.update st.known e.1 (some (du + N.arrowCost e.2))
      prev := Function.update st.prev e.1 (some u)
      queue := insertEntry (du + N.arrowCost e.2, e.1) st.queue
      pushed := st.pushed + 1 }
  else st

/-- **The start**: nothing settled; the start vertex known at cost 0 and queued. -/
def start (N : Network) (s : ℕ) : State :=
  ⟨N, s, [], Function.update (fun _ => none) s (some 0), fun _ => none, [(0, s)], 1⟩

/-- **One step**: take the smallest entry off the queue; skip its vertex if it is settled, else
settle it and try every arrow out of it, in its row's order. -/
def step (N : Network) (st : State) : State :=
  match st.queue with
  | [] => st
  | (du, u) :: q =>
    if u ∈ st.settled then { st with queue := q }
    else (N.g.out u).foldl (tryArrow N u du) { st with settled := st.settled ++ [u], queue := q }

/-- **The walk**: steps until the queue is empty, at most one per entry it can receive. -/
def dijkstra (N : Network) (s : ℕ) : Answer :=
  answer (runSteps (step N) (N.g.arrows.length + 1) (start N s))

/-! ## The queue -/

theorem EntryLe.fst_le {a b : ℤ × ℕ} (h : EntryLe a b) : a.1 ≤ b.1 := by
  rcases h with h | h <;> omega

theorem EntryLe.refl (a : ℤ × ℕ) : EntryLe a a := Or.inr ⟨rfl, le_rfl⟩

theorem EntryLe.trans {a b c : ℤ × ℕ} (h₁ : EntryLe a b) (h₂ : EntryLe b c) : EntryLe a c := by
  unfold EntryLe at *; omega

theorem EntryLe.total (a b : ℤ × ℕ) : EntryLe a b ∨ EntryLe b a := by
  unfold EntryLe; omega

theorem mem_insertEntry {e a : ℤ × ℕ} {q : List (ℤ × ℕ)} :
    a ∈ insertEntry e q ↔ a = e ∨ a ∈ q := by
  induction q with
  | nil => simp [insertEntry]
  | cons f q ih =>
    unfold insertEntry
    split_ifs <;> simp [ih, or_left_comm]

theorem length_insertEntry (e : ℤ × ℕ) (q : List (ℤ × ℕ)) :
    (insertEntry e q).length = q.length + 1 := by
  induction q with
  | nil => rfl
  | cons f q ih =>
    unfold insertEntry
    split_ifs <;> simp [ih]

theorem pairwise_insertEntry (e : ℤ × ℕ) {q : List (ℤ × ℕ)} (h : q.Pairwise EntryLe) :
    (insertEntry e q).Pairwise EntryLe := by
  induction q with
  | nil => simp [insertEntry]
  | cons f q ih =>
    rw [List.pairwise_cons] at h
    unfold insertEntry
    split_ifs with hef
    · refine List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons h.1 h.2)
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hef
      · exact hef.trans (h.1 a ha)
    · have hfe : EntryLe f e := (EntryLe.total e f).resolve_left hef
      refine List.Pairwise.cons (fun a ha => ?_) (ih h.2)
      rcases mem_insertEntry.1 ha with rfl | ha
      · exact hfe
      · exact h.1 a ha

/-! ## Known costs -/

theorem atMost_iff {c : Option ℤ} {b : ℤ} : AtMost c b ↔ ∃ d ∈ c, d ≤ b := by
  cases c <;> simp [AtMost]

theorem atMost_trans_le {c : Option ℤ} {b b' : ℤ} (h : AtMost c b) (hb : b ≤ b') : AtMost c b' := by
  cases c with
  | none => exact h
  | some d => exact le_trans (α := ℤ) h hb

/-- A cost at most `b` stays at most `b` when it is lowered. -/
theorem atMost_lower {c c' : Option ℤ} {b : ℤ} (h : AtMost c b) (hl : ∀ d ∈ c, AtMost c' d) :
    AtMost c' b := by
  obtain ⟨d, hd, hdb⟩ := atMost_iff.1 h
  exact atMost_trans_le (hl d hd) hdb

/-! ## Trying the arrows out of a settled vertex -/

/-- What trying the arrows `l` out of `u`, settled at cost `du`, does to a state `st`, giving `st'`.
-/
structure Relaxes (N : Network) (u : ℕ) (du : ℤ) (l : List (ℕ × ℕ)) (st st' : State) : Prop where
  net : st'.net = st.net
  source : st'.source = st.source
  settled : st'.settled = st.settled
  known_prev : ∀ x, (st'.known x = st.known x ∧ st'.prev x = st.prev x) ∨
    (x ∉ st.settled ∧ st'.prev x = some u ∧
      ∃ e ∈ l, e.1 = x ∧ st'.known x = some (du + N.arrowCost e.2))
  lowers : ∀ x, ∀ d ∈ st.known x, AtMost (st'.known x) d
  tried : ∀ e ∈ l, e.1 ∉ st.settled → AtMost (st'.known e.1) (du + N.arrowCost e.2)
  sorted : st.queue.Pairwise EntryLe → st'.queue.Pairwise EntryLe
  keeps : ∀ a ∈ st.queue, a ∈ st'.queue
  added : ∀ a ∈ st'.queue, a ∈ st.queue ∨ (a.2 < N.g.n ∧ AtMost (st'.known a.2) a.1)
  queued : ∀ x, ∀ d ∈ st'.known x, (d, x) ∈ st'.queue ∨ st'.known x = st.known x
  length : st'.queue.length + st.pushed = st.queue.length + st'.pushed
  pushed : st'.pushed ≤ st.pushed + l.length

/-- Trying arrows that change nothing. -/
theorem Relaxes.same {N : Network} {u : ℕ} {du : ℤ} {l : List (ℕ × ℕ)} {st : State}
    (h : ∀ e ∈ l, e.1 ∉ st.settled → AtMost (st.known e.1) (du + N.arrowCost e.2)) :
    Relaxes N u du l st st where
  net := rfl
  source := rfl
  settled := rfl
  known_prev _ := Or.inl ⟨rfl, rfl⟩
  lowers _ d hd := by rw [Option.mem_def] at hd; rw [hd]; exact le_refl d
  tried := h
  sorted h := h
  keeps _ h := h
  added _ h := Or.inl h
  queued _ _ _ := Or.inr rfl
  length := rfl
  pushed := by simp

theorem Relaxes.nil (N : Network) (u : ℕ) (du : ℤ) (st : State) : Relaxes N u du [] st st :=
  Relaxes.same (by simp)

theorem relaxes_tryArrow (N : Network) (u : ℕ) (du : ℤ) (st : State) {e : ℕ × ℕ}
    (he : e.1 < N.g.n) : Relaxes N u du [e] st (tryArrow N u du st e) := by
  unfold tryArrow
  split_ifs with hs hlow
  · exact Relaxes.same fun e' he' h => by
      rw [List.mem_singleton.1 he'] at h; exact absurd hs h
  · refine
      { net := rfl
        source := rfl
        settled := rfl
        known_prev := fun x => ?_
        lowers := fun x d hd => ?_
        tried := fun e' he' _ => ?_
        sorted := fun h => pairwise_insertEntry _ h
        keeps := fun a ha => mem_insertEntry.2 (Or.inr ha)
        added := fun a ha => ?_
        queued := fun x d hd => ?_
        length := by simp [length_insertEntry]; omega
        pushed := by simp }
    · by_cases hx : x = e.1
      · subst hx
        exact Or.inr ⟨hs, by simp, e, by simp, by simp⟩
      · exact Or.inl ⟨by simp [hx], by simp [hx]⟩
    · by_cases hx : x = e.1
      · subst hx
        rw [Option.mem_def] at hd
        rw [hd] at hlow
        simp only [Option.all_some, decide_eq_true_eq] at hlow
        simp only [Function.update_self, AtMost]
        exact le_of_lt hlow
      · simp only [Function.update_of_ne hx]
        rw [Option.mem_def] at hd; rw [hd]; exact le_refl d
    · rw [List.mem_singleton.1 he']
      simp only [Function.update_self, AtMost, le_refl]
    · rcases mem_insertEntry.1 ha with rfl | ha
      · exact Or.inr ⟨he, by simp [AtMost]⟩
      · exact Or.inl ha
    · by_cases hx : x = e.1
      · subst hx
        simp only [Function.update_self, Option.mem_def, Option.some.injEq] at hd
        exact Or.inl (mem_insertEntry.2 (Or.inl (by rw [hd])))
      · exact Or.inr (by simp [hx])
  · refine Relaxes.same fun e' he' _ => ?_
    rw [List.mem_singleton.1 he']
    cases hk : st.known e.1 with
    | none => rw [hk] at hlow; simp at hlow
    | some d =>
      rw [hk] at hlow
      simp only [Option.all_some, decide_eq_true_eq, not_lt] at hlow
      exact hlow

theorem Relaxes.append {N : Network} {u : ℕ} {du : ℤ} {l₁ l₂ : List (ℕ × ℕ)} {st st₁ st₂ : State}
    (h₁ : Relaxes N u du l₁ st st₁) (h₂ : Relaxes N u du l₂ st₁ st₂) :
    Relaxes N u du (l₁ ++ l₂) st st₂ where
  net := h₂.net.trans h₁.net
  source := h₂.source.trans h₁.source
  settled := h₂.settled.trans h₁.settled
  known_prev x := by
    rcases h₂.known_prev x with ⟨hk, hp⟩ | ⟨hx, hp, e, he, hex, hk⟩
    · rcases h₁.known_prev x with ⟨hk', hp'⟩ | ⟨hx', hp', e, he, hex, hk'⟩
      · exact Or.inl ⟨hk.trans hk', hp.trans hp'⟩
      · exact Or.inr ⟨hx', hp.trans hp', e, List.mem_append_left _ he, hex, hk.trans hk'⟩
    · rw [h₁.settled] at hx
      exact Or.inr ⟨hx, hp, e, List.mem_append_right _ he, hex, hk⟩
  lowers x d hd := atMost_lower (h₁.lowers x d hd) (h₂.lowers x)
  tried e he hs := by
    rcases List.mem_append.1 he with he | he
    · exact atMost_lower (h₁.tried e he hs) (h₂.lowers e.1)
    · exact h₂.tried e he (h₁.settled ▸ hs)
  sorted h := h₂.sorted (h₁.sorted h)
  keeps a ha := h₂.keeps a (h₁.keeps a ha)
  added a ha := by
    rcases h₂.added a ha with ha | ha
    · rcases h₁.added a ha with ha | ⟨hn, ha⟩
      · exact Or.inl ha
      · exact Or.inr ⟨hn, atMost_lower ha (h₂.lowers a.2)⟩
    · exact Or.inr ha
  queued x d hd := by
    rcases h₂.queued x d hd with hq | hk
    · exact Or.inl hq
    · rw [hk] at hd
      rcases h₁.queued x d hd with hq | hk'
      · exact Or.inl (h₂.keeps _ hq)
      · exact Or.inr (hk.trans hk')
  length := by have := h₁.length; have := h₂.length; omega
  pushed := by have := h₁.pushed; have := h₂.pushed; simp only [List.length_append]; omega

theorem relaxes_foldl (N : Network) (u : ℕ) (du : ℤ) :
    ∀ (l : List (ℕ × ℕ)) (st : State), (∀ e ∈ l, e.1 < N.g.n) →
      Relaxes N u du l st (l.foldl (tryArrow N u du) st)
  | [], st, _ => Relaxes.nil N u du st
  | e :: l, st, h => by
    rw [List.foldl_cons]
    exact (relaxes_tryArrow N u du st (h e (by simp))).append
      (relaxes_foldl N u du l _ fun e' he' => h e' (by simp [he']))

/-! ## One step -/

variable {N : Network} {s : ℕ}

theorem step_skip {st : State} {k : ℤ} {u : ℕ} {q : List (ℤ × ℕ)} (hq : st.queue = (k, u) :: q)
    (hu : u ∈ st.settled) : step N st = { st with queue := q } := by
  unfold step; rw [hq]; simp [hu]

theorem step_settle {st : State} {k : ℤ} {u : ℕ} {q : List (ℤ × ℕ)} (hq : st.queue = (k, u) :: q)
    (hu : u ∉ st.settled) :
    step N st = (N.g.out u).foldl (tryArrow N u k)
      { st with settled := st.settled ++ [u], queue := q } := by
  unfold step; rw [hq]; simp [hu]

/-- **A step keeps the walk's network and start vertex.** -/
theorem step_net_source (N : Network) (st : State) :
    (step N st).net = st.net ∧ (step N st).source = st.source := by
  cases hq : st.queue with
  | nil => unfold step; rw [hq]; exact ⟨rfl, rfl⟩
  | cons e q =>
    obtain ⟨k, u⟩ := e
    by_cases hu : u ∈ st.settled
    · rw [step_skip hq hu]; exact ⟨rfl, rfl⟩
    · rw [step_settle hq hu]
      have R := relaxes_foldl N u k (N.g.out u) { st with settled := st.settled ++ [u], queue := q }
        fun e he => (mem_out.1 he).1
      exact ⟨R.net, R.source⟩

@[simp] theorem step_net (N : Network) (st : State) : (step N st).net = st.net :=
  (step_net_source N st).1

@[simp] theorem step_source (N : Network) (st : State) : (step N st).source = st.source :=
  (step_net_source N st).2

/-- **The entry taken off the queue is the smallest known cost**: an unsettled vertex at the front
is a vertex of the graph, its known cost is the entry's, and no unsettled vertex is known
cheaper. -/
theorem front_spec {st : State} {k : ℤ} {u : ℕ} {q : List (ℤ × ℕ)} (hQ : QueueHoldsKnown st)
    (hq : st.queue = (k, u) :: q) (hu : u ∉ st.settled) :
    u < st.net.g.n ∧ st.known u = some k ∧
      ∀ y < st.net.g.n, y ∉ st.settled → ∀ dy ∈ st.known y, k ≤ dy := by
  have hsorted := hQ.1
  rw [hq, List.pairwise_cons] at hsorted
  have low : ∀ a ∈ st.queue, k ≤ a.1 := by
    intro a ha
    rw [hq] at ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact le_rfl
    · exact (hsorted.1 a ha).fst_le
  obtain ⟨hun, hk⟩ := hQ.2.2 (k, u) (by rw [hq]; exact List.mem_cons_self)
  obtain ⟨du, hdu, hduk⟩ := atMost_iff.1 hk
  have := low _ (hQ.2.1 u hun hu du hdu)
  refine ⟨hun, by rw [Option.mem_def] at hdu; rw [hdu]; congr 1; simp only at this; omega,
    fun y hy hyS dy hdy => low _ (hQ.2.1 y hy hyS dy hdy)⟩

theorem mem_known_start {v : ℕ} {d : ℤ} : d ∈ (start N s).known v ↔ v = s ∧ d = 0 := by
  by_cases hv : v = s
  · subst hv; simp [start, eq_comm]
  · simp [start, hv]

/-- The pieces of `Valid` and `WellFormed` that hold whatever the arrows cost. -/
def Steady (st : State) : Prop :=
  st.settled.Nodup ∧ StartSettledFirst st ∧ SettledRowsTried st ∧ QueueHoldsKnown st ∧
    PreviousLeadsBack st

theorem steady_start (hs : s < N.g.n) : Steady (start N s) := by
  refine ⟨List.nodup_nil, fun h => absurd rfl h, fun x hx => absurd hx (by simp [start]),
    ⟨List.pairwise_singleton _ _, fun v _ _ d hd => ?_, fun e he => ?_⟩, rfl, fun v _ d hd => ?_⟩
  · obtain ⟨rfl, rfl⟩ := mem_known_start.1 hd
    simp [start]
  · simp only [start, List.mem_singleton] at he
    subst he
    exact ⟨hs, by simp [start, AtMost]⟩
  · obtain ⟨rfl, rfl⟩ := mem_known_start.1 hd
    exact ⟨[], isPath_nil v, by simp [pathCost], through_nil _ _, rfl,
      by simp [visits]⟩

/-- In a settling step, the start is settled, and settled first. -/
theorem startSettledFirst_settle {st : State} {k : ℤ} {u : ℕ} (h1 : StartSettledFirst st)
    (hP : PreviousLeadsBack st) (hun : u < st.net.g.n) (hk : st.known u = some k) :
    (st.settled ++ [u]).head? = some st.source := by
  cases hS : st.settled with
  | nil =>
    obtain ⟨p, hp, -, ht, -⟩ := hP.2 u hun k hk
    rw [hS] at ht
    rw [eq_nil_of_through_nil ht] at hp
    rw [isPath_nil_iff.1 hp]
    rfl
  | cons a S =>
    have := h1 (by simp [hS])
    rw [hS] at this
    exact this

theorem steady_step {st : State} (hn : st.net = N) (h : Steady st) (hne : st.queue ≠ []) :
    Steady (step N st) := by
  subst hn
  set N := st.net with hNdef
  set s := st.source with hsdef
  obtain ⟨hnd, h1, hR, hQ, hP⟩ := h
  obtain ⟨⟨k, u⟩, q, hq⟩ := List.exists_cons_of_ne_nil hne
  by_cases hu : u ∈ st.settled
  · rw [step_skip hq hu]
    have hsorted := hQ.1
    rw [hq, List.pairwise_cons] at hsorted
    refine ⟨hnd, h1, hR, ⟨hsorted.2, fun v hv hvS d hd => ?_, fun e he => ?_⟩, hP⟩
    · have := hQ.2.1 v hv hvS d hd
      rw [hq] at this
      rcases List.mem_cons.1 this with he | he
      · simp only [Prod.mk.injEq] at he
        exact absurd (he.2 ▸ hu) hvS
      · exact he
    · exact hQ.2.2 e (by rw [hq]; exact List.mem_cons_of_mem _ he)
  · rw [step_settle hq hu]
    obtain ⟨hun, hk, -⟩ := front_spec hQ hq hu
    set st₀ : State := { st with settled := st.settled ++ [u], queue := q } with hst₀
    have R := relaxes_foldl N u k (N.g.out u) st₀ fun e he => (mem_out.1 he).1
    set st' := (N.g.out u).foldl (tryArrow N u k) st₀
    have hS' : st'.settled = st.settled ++ [u] := R.settled
    have hhead := startSettledFirst_settle h1 hP hun hk
    have hsS : s ∈ st.settled ++ [u] := List.mem_of_mem_head? hhead
    -- a settled vertex keeps its cost and its previous vertex
    have keep : ∀ x ∈ st.settled ++ [u], st'.known x = st.known x ∧ st'.prev x = st.prev x := by
      intro x hx
      rcases R.known_prev x with h | ⟨hx', -⟩
      · exact h
      · exact absurd hx hx'
    have hku : st'.known u = some k := (keep u (by simp)).1.trans hk
    have hn' : st'.net = N := R.net
    have hs' : st'.source = s := R.source
    unfold Steady StartSettledFirst SettledRowsTried QueueHoldsKnown PreviousLeadsBack
    rw [hn', hs']
    refine ⟨?_, fun _ => hS' ▸ hhead, ?_, ⟨R.sorted ?_, ?_, ?_⟩, ?_⟩
    · rw [hS']
      exact hnd.append (List.nodup_singleton u) (by simpa using hu)
    · intro x hx e he heS dx hdx
      rw [hS'] at hx heS
      rw [(keep x hx).1] at hdx
      rcases List.mem_append.1 hx with hx | hx
      · exact atMost_lower (hR x hx e he (fun h => heS (List.mem_append_left _ h)) dx hdx)
          (R.lowers e.1)
      · rw [List.mem_singleton.1 hx, hk, Option.mem_def, Option.some.injEq] at hdx
        subst hdx
        rw [List.mem_singleton.1 hx] at he
        exact R.tried e he heS
    · have hsorted := hQ.1
      rw [hq, List.pairwise_cons] at hsorted
      exact hsorted.2
    · intro v hv hvS d hd
      rw [hS'] at hvS
      rcases R.queued v d hd with h | h
      · exact h
      · rw [h] at hd
        have := hQ.2.1 v hv (fun h => hvS (List.mem_append_left _ h)) d hd
        rw [hq] at this
        rcases List.mem_cons.1 this with he | he
        · simp only [Prod.mk.injEq] at he
          exact absurd (by simp [he.2]) hvS
        · exact R.keeps _ he
    · intro e he
      rcases R.added e he with he | he
      · obtain ⟨hn, ha⟩ := hQ.2.2 e (by rw [hq]; exact List.mem_cons_of_mem _ he)
        exact ⟨hn, atMost_lower ha (R.lowers e.2)⟩
      · exact he
    · have hprev_s : st'.prev s = none := (keep s hsS).2.trans hP.1
      refine ⟨hprev_s, fun v hv d hd => ?_⟩
      rw [hS']
      rcases R.known_prev v with ⟨hkv, hpv⟩ | ⟨hvS, hpv, ⟨w, i⟩, he, hw, hkv⟩
      · rw [hkv] at hd
        obtain ⟨p, hp, hc, ht, hl⟩ := hP.2 v hv d hd
        refine ⟨p, hp, hc, through_mono ht fun x hx => List.mem_append_left _ hx, hprev_s,
          hl.2.imp_of_mem_imp fun a b _ hb hab => ?_⟩
        rw [hp.visits_eq] at hb
        rcases List.mem_append.1 hb with hb | hb
        · rw [(keep b (List.mem_append_left _ (ht b hb))).2]; exact hab
        · rw [List.mem_singleton.1 hb, hpv]; rw [List.mem_singleton.1 hb] at hab; exact hab
      · simp only at hw
        subst hw
        rw [hkv, Option.mem_def, Option.some.injEq] at hd
        subst hd
        have hi := (mem_out.1 he).2
        obtain ⟨p, hp, hc, ht, hl⟩ := hP.2 u hun k hk
        have hwp : w ∉ N.visits s p := by
          rw [hp.visits_eq]
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact hvS (List.mem_append_left _ (ht w hm))
          · rw [List.mem_singleton.1 hm] at hvS
            exact hvS (List.mem_append_right _ (List.mem_singleton_self u))
        obtain ⟨hp', hv'⟩ := hp.snoc hi hwp
        refine ⟨p ++ [i], hp', by rw [pathCost_append, hc]; simp [pathCost], fun x hx => ?_,
          hprev_s, ?_⟩
        · rw [hv', List.dropLast_concat, hp.visits_eq] at hx
          rcases List.mem_append.1 hx with hx | hx
          · exact List.mem_append_left _ (ht x hx)
          · exact List.mem_append_right _ hx
        · rw [hv']
          refine List.IsChain.append (hl.2.imp_of_mem_imp fun a b _ hb hab => ?_)
            (List.isChain_singleton w) ?_
          · have hb' : b ∈ st.settled ++ [u] := by
              rw [hp.visits_eq] at hb
              rcases List.mem_append.1 hb with hb | hb
              · exact List.mem_append_left _ (ht b hb)
              · exact List.mem_append_right _ hb
            rw [(keep b hb').2]; exact hab
          · intro x hx y hy
            rw [hp.visits_eq] at hx
            simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
              Option.mem_def, Option.some.injEq] at hx
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            rw [← hx, ← hy, hpv]

/-! ## The box's invariants -/

theorem valid_start (hs : s < N.g.n) : Valid (start N s) ∧ WellFormed (start N s) := by
  obtain ⟨-, h1, hR, hQ, hP⟩ := steady_start (N := N) hs
  refine ⟨⟨⟨List.nodup_nil, fun v hv => absurd hv (by simp [start])⟩, fun v _ _ => ⟨?_, ?_⟩⟩,
    h1, hR, hQ, hP⟩
  · intro p hp ht
    obtain rfl := eq_nil_of_through_nil ht
    rw [isPath_nil_iff.1 hp]
    simp [start, AtMost, pathCost]
  · intro d hd
    obtain ⟨rfl, rfl⟩ := mem_known_start.1 hd
    exact ⟨[], isPath_nil v, through_nil _ _, by simp [pathCost]⟩

/-- **One step keeps the box's invariants**, when no arrow is negative. -/
theorem valid_step (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) {st : State}
    (hn : st.net = N) (hsrc : st.source = s) (h : Valid st ∧ WellFormed st)
    (hne : st.queue ≠ []) : Valid (step N st) ∧ WellFormed (step N st) := by
  obtain ⟨⟨h1, h2⟩, hF, hR, hQ, hP⟩ := h
  obtain ⟨hnd', hF', hR', hQ', hP'⟩ := steady_step hn ⟨h1.1, hF, hR, hQ, hP⟩ hne
  have hsn : (step N st).net = N := (step_net N st).trans hn
  have hss : (step N st).source = s := (step_source N st).trans hsrc
  -- the pieces read on the network and the start vertex the state carries
  have hP'' := hP'
  unfold SettledAreCheapest at h1
  unfold KnownIsCheapestThroughSettled at h2
  unfold SettledRowsTried at hR
  unfold PreviousLeadsBack at hP''
  rw [hn, hsrc] at h1 h2
  rw [hn] at hR
  rw [hsn, hss] at hP''
  refine ⟨⟨⟨hnd', ?_⟩, ?_⟩, hF', hR', hQ', hP'⟩ <;>
    (try unfold KnownIsCheapestThroughSettled) <;> rw [hsn, hss] <;>
    obtain ⟨⟨k, u⟩, q, hq⟩ := List.exists_cons_of_ne_nil hne <;>
    by_cases hu : u ∈ st.settled
  · rw [step_skip hq hu]; exact h1.2
  rotate_left
  · rw [step_skip hq hu]; exact h2
  rotate_left
  all_goals
    obtain ⟨hun, hk, hsmall⟩ := front_spec hQ hq hu
    have hhd := startSettledFirst_settle hF hP hun hk
    rw [hn] at hun hsmall
    rw [hsrc] at hhd
    have R := relaxes_foldl N u k (N.g.out u) { st with settled := st.settled ++ [u], queue := q }
      fun e he => (mem_out.1 he).1
    have hS' : ((N.g.out u).foldl (tryArrow N u k)
        { st with settled := st.settled ++ [u], queue := q }).settled = st.settled ++ [u] :=
      R.settled
    have keep : ∀ x ∈ st.settled ++ [u],
        ((N.g.out u).foldl (tryArrow N u k)
          { st with settled := st.settled ++ [u], queue := q }).known x = st.known x := by
      intro x hx
      rcases R.known_prev x with h | ⟨hx', -⟩
      · exact h.1
      · exact absurd hx hx'
  · -- invariant 1: the vertex just settled has its cheapest cost
    rw [step_settle hq hu]
    intro x hx
    replace hx : x ∈ st.settled ++ [u] := hS' ▸ hx
    rw [keep x hx]
    rcases List.mem_append.1 hx with hx | hx
    · exact h1.2 x hx
    rw [List.mem_singleton.1 hx, hk]
    refine ⟨by simp, fun p hp _ => ?_, fun d hd => ?_⟩
    · obtain ⟨q', r, y, rfl, hq', hyS, ht⟩ :=
        split_first_outside hp ⟨u, hp.mem_visits, hu⟩
      obtain ⟨dy, hdy, hdyq⟩ := atMost_iff.1 ((h2 y (hq'.lt hN hs) hyS).1 q' hq' ht)
      have := hsmall y (hq'.lt hN hs) hyS dy hdy
      have := pathCost_nonneg hnn r
      change k ≤ N.pathCost (q' ++ r)
      rw [pathCost_append]
      omega
    · obtain ⟨p, hp, -, hc⟩ := (h2 u hun hu).2 d (by rw [hk]; exact hd)
      exact ⟨p, hp, trivial, hc⟩
  · -- invariant 2: the unsettled vertices, through the settled ones and the new one
    rw [step_settle hq hu]
    intro v hv hvS
    refine ⟨fun p hp ht => ?_, fun d hd => ?_⟩
    · rw [R.settled] at hvS
      have hsS := List.mem_of_mem_head? hhd
      rcases eq_or_ne p [] with rfl | hne
      · rw [isPath_nil_iff.1 hp] at hvS; exact absurd hsS hvS
      obtain ⟨q', i, x, rfl, hq', hi, -, hvis⟩ := hp.eq_snoc hne
      have ht' : ∀ y ∈ N.visits s q', y ∈ st.settled ++ [u] := by
        intro y hy
        exact hS' ▸ ht y (by rw [hvis, List.dropLast_concat]; exact hy)
      have he : (v, i) ∈ N.g.out x := mem_out.2 ⟨hv, hi⟩
      have hcost : N.pathCost (q' ++ [i]) = N.pathCost q' + N.arrowCost i := by
        rw [pathCost_append]; simp [pathCost]
      rw [hcost]
      rcases List.mem_append.1 (ht' x hq'.mem_visits) with hx | hx
      · obtain ⟨dx, hdx, hdxq⟩ := atMost_iff.1 ((h1.2 x hx).2.1 q' hq' trivial)
        have := hR x hx (v, i) he (fun h => hvS (List.mem_append_left _ h)) dx hdx
        refine atMost_trans_le (atMost_lower this (R.lowers v)) ?_
        change dx + N.arrowCost i ≤ N.pathCost q' + N.arrowCost i
        omega
      · rw [List.mem_singleton.1 hx] at hq' he
        have hthrough : Through N st.settled s q' := by
          intro y hy
          rcases List.mem_append.1 (ht' y ((List.dropLast_sublist _).subset hy)) with h | h
          · exact h
          · exact absurd (List.mem_singleton.1 h) (hq'.ne_of_mem_dropLast hy)
        have := (h2 u hun hu).1 q' hq' hthrough
        rw [hk] at this
        refine atMost_trans_le (R.tried (v, i) he hvS) ?_
        change k + N.arrowCost i ≤ N.pathCost q' + N.arrowCost i
        exact Int.add_le_add_right this _
    · obtain ⟨p, hp, hc, ht, -⟩ := hP''.2 v hv d (by rw [step_settle hq hu]; exact hd)
      rw [step_settle hq hu] at ht
      exact ⟨p, hp, ht, hc⟩

/-- **`Valid` and `WellFormed` together are the six pieces the walk keeps**, the box's two and the
four the walk needs beyond them. -/
theorem valid_and_wellFormed_iff (st : State) :
    Valid st ∧ WellFormed st ↔ SettledAreCheapest st ∧ KnownIsCheapestThroughSettled st ∧
      StartSettledFirst st ∧ SettledRowsTried st ∧ QueueHoldsKnown st ∧ PreviousLeadsBack st :=
  and_assoc

/-! ## The whole walk -/

theorem runSteps_induct (P : State → Prop) (step : State → State)
    (hstep : ∀ st, P st → st.queue ≠ [] → P (step st)) :
    ∀ f st, P st → P (runSteps step f st)
  | 0, _, h => h
  | f + 1, st, h => by
    unfold runSteps
    split_ifs with hq
    · exact h
    · exact runSteps_induct P step hstep f _ (hstep st h hq)

/-- What the cost counts: the settled vertices listed once, and at most one entry received per
arrow tried, besides the start's. -/
def Counted (N : Network) (st : State) : Prop :=
  st.settled.Nodup ∧ st.pushed ≤ 1 + (tried N st).length

theorem counted_start : Counted N (start N s) := ⟨List.nodup_nil, by simp [start, tried]⟩

theorem counted_step {st : State} (h : Counted N st) (hne : st.queue ≠ []) :
    Counted N (step N st) ∧
      (step N st).queue.length + st.pushed + 1 = st.queue.length + (step N st).pushed := by
  obtain ⟨⟨k, u⟩, q, hq⟩ := List.exists_cons_of_ne_nil hne
  by_cases hu : u ∈ st.settled
  · rw [step_skip hq hu, hq]
    exact ⟨h, by simp; omega⟩
  · rw [step_settle hq hu]
    have R := relaxes_foldl N u k (N.g.out u) { st with settled := st.settled ++ [u], queue := q }
      fun e he => (mem_out.1 he).1
    have hlen := R.length
    have hpush := R.pushed
    simp only at hlen hpush
    refine ⟨⟨?_, ?_⟩, by rw [hq]; simp; omega⟩
    · rw [R.settled]
      exact h.1.append (List.nodup_singleton u) (by simpa using hu)
    · have := h.2
      unfold tried at this ⊢
      rw [R.settled, List.flatMap_append, List.length_append]
      simp only [List.flatMap_singleton, List.length_map] at this ⊢
      omega

/-- **The walk ends with the queue empty**: each step takes one entry off it, and it receives at
most one more entry than there are arrows. -/
theorem queue_runSteps (N : Network) :
    ∀ f st, Counted N st → N.g.arrows.length + 1 - st.pushed + st.queue.length ≤ f →
      (runSteps (step N) f st).queue = []
  | 0, st, _, hf => by
    unfold runSteps
    exact List.eq_nil_of_length_eq_zero (by omega)
  | f + 1, st, h, hf => by
    unfold runSteps
    split_ifs with hq
    · exact hq
    · obtain ⟨h', hlen⟩ := counted_step h hq
      have := length_tried_le (N := N) h'.1
      have := h'.2
      exact queue_runSteps N f _ h' (by omega)

/-- The state the walk ends in. -/
abbrev final (N : Network) (s : ℕ) : State :=
  runSteps (step N) (N.g.arrows.length + 1) (start N s)

theorem final_queue (N : Network) (s : ℕ) : (final N s).queue = [] :=
  queue_runSteps N _ _ counted_start (by simp [start])

theorem final_counted (N : Network) (s : ℕ) : Counted N (final N s) :=
  runSteps_induct _ _ (fun _ h hq => (counted_step h hq).1) _ _ counted_start

/-- **The walk keeps its network and start vertex.** -/
theorem net_runSteps (N : Network) (f : ℕ) (st : State) :
    (runSteps (step N) f st).net = st.net ∧ (runSteps (step N) f st).source = st.source :=
  runSteps_induct (fun st' => st'.net = st.net ∧ st'.source = st.source) (step N)
    (fun _ h _ => ⟨(step_net _ _).trans h.1, (step_source _ _).trans h.2⟩) f st ⟨rfl, rfl⟩

theorem final_net (N : Network) (s : ℕ) : (final N s).net = N ∧ (final N s).source = s :=
  net_runSteps N _ _

theorem final_steady (hs : s < N.g.n) : Steady (final N s) :=
  (runSteps_induct (fun st => st.net = N ∧ Steady st) _
    (fun _ h hq => ⟨(step_net _ _).trans h.1, steady_step h.1 h.2 hq⟩) _ _
    ⟨rfl, steady_start hs⟩).2

theorem final_valid (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n) :
    Valid (final N s) ∧ WellFormed (final N s) :=
  (runSteps_induct (fun st => (st.net = N ∧ st.source = s) ∧ Valid st ∧ WellFormed st) _
    (fun _ h hq => ⟨⟨(step_net _ _).trans h.1.1, (step_source _ _).trans h.1.2⟩,
      valid_step hN hnn hs h.1.1 h.1.2 h.2 hq⟩) _ _ ⟨⟨rfl, rfl⟩, valid_start hs⟩).2

/-! ## The promise -/

/-- **On a legal state with an empty queue, every vertex that can be reached is settled.** -/
theorem mem_settled_of_reaches (hN : N.WellFormed) (hs : s < N.g.n) {st : State}
    (hn : st.net = N) (hsrc : st.source = s) (h : Valid st ∧ WellFormed st) (hq : st.queue = [])
    {v : ℕ} (hv : N.g.Reaches s v) : v ∈ st.settled := by
  obtain ⟨⟨h1, h2⟩, -, hR, hQ, -⟩ := h
  unfold SettledAreCheapest at h1
  unfold KnownIsCheapestThroughSettled at h2
  unfold SettledRowsTried at hR
  unfold QueueHoldsKnown at hQ
  rw [hn, hsrc] at h1 h2
  rw [hn] at hR hQ
  induction hv with
  | refl =>
    by_contra hsS
    obtain ⟨d, hd, -⟩ := atMost_iff.1 ((h2 s hs hsS).1 [] (isPath_nil s) (through_nil _ _))
    have := hQ.2.1 s hs hsS d hd
    rw [hq] at this
    exact absurd this List.not_mem_nil
  | @tail b c _ hbc ih =>
    by_contra hcS
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hbc
    have hc : c < N.g.n := (hN.1 _ hbc).2
    obtain ⟨dx, hdx⟩ := Option.ne_none_iff_exists'.1 (h1.2 b ih).1
    obtain ⟨d, hd, -⟩ := atMost_iff.1 (hR b ih (c, i) (mem_out.2 ⟨hc, hi⟩) hcS dx hdx)
    have := hQ.2.1 c hc hcS d hd
    rw [hq] at this
    exact absurd this List.not_mem_nil

/-- **On a legal state with an empty queue, every vertex that can be reached has the cost of its
cheapest path.** -/
theorem reached_of_valid (hN : N.WellFormed) (hs : s < N.g.n) {st : State} (hn : st.net = N)
    (hsrc : st.source = s) (h : Valid st ∧ WellFormed st) (hq : st.queue = []) {v : ℕ}
    (hv : N.g.Reaches s v) : ∃ d, st.known v = some d ∧ N.Cheapest s v (some d) := by
  have hm := mem_settled_of_reaches hN hs hn hsrc h hq hv
  subst hn hsrc
  obtain ⟨hne, hc⟩ := h.1.1.2 v hm
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨d, hd, hd ▸ hc⟩

/-- On a state whose steady pieces hold, the previous vertices lead back along a path of exactly
each known cost. -/
theorem previous_of_steady {st : State} (hn : st.net = N) (hsrc : st.source = s) (h : Steady st)
    {v : ℕ} (hv : v < N.g.n) :
    ∀ d ∈ st.known v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
      LeadsBack st.prev s (N.visits s p) := by
  subst hn hsrc
  intro d hd
  obtain ⟨p, hp, hc, -, hl⟩ := h.2.2.2.2.2 v hv d hd
  exact ⟨p, hp, hc, hl⟩

/-- On a state whose steady pieces hold, a vertex that cannot be reached has no known cost. -/
theorem unreached_of_steady {st : State} (hn : st.net = N) (hsrc : st.source = s)
    (h : Steady st) {v : ℕ} (hv : v < N.g.n) (hr : ¬ N.g.Reaches s v) : st.known v = none := by
  by_contra hk
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hk
  obtain ⟨p, hp, -⟩ := previous_of_steady hn hsrc h hv d hd
  exact hr (reaches_of_ends hp.1)

theorem dijkstra_reached (hN : N.WellFormed) (hnn : N.NoArrowBelowZero) (hs : s < N.g.n)
    {v : ℕ} (hv : N.g.Reaches s v) :
    ∃ d, (dijkstra N s).cost v = some d ∧ N.Cheapest s v (some d) :=
  reached_of_valid hN hs (final_net N s).1 (final_net N s).2 (final_valid hN hnn hs)
    (final_queue N s) hv

theorem dijkstra_previous (hs : s < N.g.n) {v : ℕ} (hv : v < N.g.n) :
    ∀ d ∈ (dijkstra N s).cost v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
      LeadsBack (dijkstra N s).prev s (N.visits s p) :=
  previous_of_steady (final_net N s).1 (final_net N s).2 (final_steady hs) hv

theorem dijkstra_unreached (hs : s < N.g.n) {v : ℕ} (hv : v < N.g.n) (hr : ¬ N.g.Reaches s v) :
    (dijkstra N s).cost v = none :=
  unreached_of_steady (final_net N s).1 (final_net N s).2 (final_steady hs) hv hr

/-- **Each arrow is tried once, and each try adds at most one entry to the queue.** -/
theorem dijkstra_cost (N : Network) (s : ℕ) :
    (tried N (final N s)).Nodup ∧ (final N s).pushed ≤ (tried N (final N s)).length + 1 := by
  obtain ⟨hnd, hp⟩ := final_counted N s
  exact ⟨nodup_tried hnd, by omega⟩

/-- The queue receives at most one more entry than there are arrows. -/
theorem pushed_final_le (N : Network) (s : ℕ) : (final N s).pushed ≤ N.g.arrows.length + 1 := by
  obtain ⟨hnd, hp⟩ := final_counted N s
  have := length_tried_le (N := N) hnd
  omega

end AlgoDesign.Paths.Dijkstra
