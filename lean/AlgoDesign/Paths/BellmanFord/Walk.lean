/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.BellmanFord.Basic

/-!
# Cheapest paths with negative arrows: the rounds

Source: Kleinberg and Tardos, *Algorithm Design*, §6.8 (pp. 292–297): each round, for every
arrow, lowers the cost of the vertex it points to when the cost of the vertex it leaves, as it is
now (pp. 295–296, (6.26)), plus the arrow's is less, recording that vertex as the previous one. A
round that lowers nothing ends the run (p. 297).
-/

@[expose] public section

namespace AlgoDesign.Paths.BellmanFord

open Network

/-! ## The rounds -/

/-- **Try one arrow** `(w, i)` out of `u`, reading `u`'s cost as it is now: if `u` has a cost and
`w` has none yet or the arrow gives less, record the new cost and `u`, and note `w` as lowered. -/
def tryArrow (N : Network) (u : ℕ) (st : State) (e : ℕ × ℕ) : State :=
  match st.cost u with
  | none => { st with tried := st.tried + 1 }
  | some du =>
    if (st.cost e.1).all (du + N.arrowCost e.2 < ·) then
      { st with
        cost := Function.update st.cost e.1 (some (du + N.arrowCost e.2))
        prev := Function.update st.prev e.1 (some u)
        lowered := some e.1
        tried := st.tried + 1 }
    else { st with tried := st.tried + 1 }

/-- **The start**: no rounds run; only the start vertex has a cost, 0; no previous vertices. -/
def start (N : Network) (s : ℕ) : State :=
  ⟨N, s, Function.update (fun _ => none) s (some 0), fun _ => none, 0, none, 0⟩

/-- **One round**: the vertices by increasing id, each vertex's row in order, every arrow tried
against the costs as they are now. -/
def round (N : Network) (st : State) : State :=
  (List.range N.g.n).foldl (fun acc u => (N.g.out u).foldl (tryArrow N u) acc)
    { st with rounds := st.rounds + 1, lowered := none }

/-- **The run**: rounds until one lowers nothing, at most one per vertex. -/
def bellmanFord (N : Network) (s : ℕ) : Except (List ℕ) Dijkstra.Answer :=
  answer N (runRounds (round N) N.g.n (start N s))


/-! ## What one try does -/

open Dijkstra (LeadsBack atMost_iff atMost_trans_le atMost_lower)

variable {N : Network}

/-- A try changes nothing but the count, or writes `w`'s new cost and its previous vertex `u`. -/
theorem tryArrow_cases (u : ℕ) (st : State) (w i : ℕ) :
    (tryArrow N u st (w, i) = { st with tried := st.tried + 1 } ∧
      ∀ du ∈ st.cost u, (st.cost w).all (du + N.arrowCost i < ·) = false) ∨
    ∃ du, st.cost u = some du ∧ (st.cost w).all (du + N.arrowCost i < ·) = true ∧
      tryArrow N u st (w, i) = { st with
        cost := Function.update st.cost w (some (du + N.arrowCost i))
        prev := Function.update st.prev w (some u)
        lowered := some w
        tried := st.tried + 1 } := by
  unfold tryArrow
  cases hu : st.cost u with
  | none => exact Or.inl ⟨rfl, by simp⟩
  | some du =>
    simp only
    by_cases hlt : ((st.cost w).all (du + N.arrowCost i < ·)) = true
    · exact Or.inr ⟨du, rfl, hlt, by simp only [hlt, ↓reduceIte]⟩
    · refine Or.inl ⟨by simp only [hlt, ↓reduceIte, Bool.false_eq_true], fun d hd => ?_⟩
      rw [Option.mem_def, Option.some.injEq] at hd
      subst hd
      simpa using hlt

/-- The cost a try writes is below the cost it replaces. -/
theorem lt_of_all {c : Option ℤ} {b : ℤ} (h : c.all (b < ·) = true) : ∀ e ∈ c, b < e := by
  intro e he
  rw [Option.mem_def] at he
  subst he
  simpa using h

/-- What trying the arrows `l` (each with the vertex it leaves) does to the state `st₀` a round
starts from, giving `st`: each cost only drops; every arrow tried fits the cost it points to,
from the cost its vertex had at the start; while nothing is lowered nothing changes; the last
vertex lowered has a cost below its first. -/
structure Tries (N : Network) (st₀ st : State) (l : List (ℕ × ℕ × ℕ)) : Prop where
  net : st.net = st₀.net
  source : st.source = st₀.source
  rounds : st.rounds = st₀.rounds
  drops : ∀ v, ∀ d ∈ st₀.cost v, AtMost (st.cost v) d
  tried : ∀ a ∈ l, ∀ du ∈ st₀.cost a.1, AtMost (st.cost a.2.1) (du + N.arrowCost a.2.2)
  unlowered : st.lowered = none → ∀ v, st.cost v = st₀.cost v ∧ st.prev v = st₀.prev v
  lowered : ∀ x ∈ st.lowered, x < N.g.n ∧ ∃ d ∈ st.cost x, ∀ e ∈ st₀.cost x, d < e
  count : st.tried = st₀.tried + l.length

theorem Tries.start (N : Network) (st : State) :
    Tries N { st with rounds := st.rounds + 1, lowered := none }
      { st with rounds := st.rounds + 1, lowered := none } [] where
  net := rfl
  source := rfl
  rounds := rfl
  drops _ d hd := by rw [Option.mem_def.1 hd]; exact le_refl d
  tried := by simp
  unlowered _ _ := ⟨rfl, rfl⟩
  lowered := by simp
  count := rfl

theorem Tries.step {st₀ st : State} {l : List (ℕ × ℕ × ℕ)} {u w i : ℕ} (h : Tries N st₀ st l)
    (he : (w, i) ∈ N.g.out u) : Tries N st₀ (tryArrow N u st (w, i)) (l ++ [(u, w, i)]) := by
  obtain ⟨hw, -⟩ := mem_out.1 he
  rcases tryArrow_cases u st w i with ⟨heq, hno⟩ | ⟨du, hu, hlt, heq⟩
  · rw [heq]
    refine
      { net := h.net
        source := h.source
        rounds := h.rounds
        drops := h.drops
        tried := fun a ha d hd => ?_
        unlowered := h.unlowered
        lowered := h.lowered
        count := by simp [h.count]; omega }
    rcases List.mem_append.1 ha with ha | ha
    · exact h.tried a ha d hd
    · rw [List.mem_singleton.1 ha] at hd ⊢
      obtain ⟨du, hdu, hle⟩ := atMost_iff.1 (h.drops u d hd)
      have := hno du hdu
      cases hc : st.cost w with
      | none => rw [hc] at this; simp at this
      | some c =>
        rw [hc] at this
        simp only [Option.all_some, decide_eq_false_iff_not, not_lt] at this
        change c ≤ d + N.arrowCost i
        linarith
  · rw [heq]
    have hlow : ∀ x, ∀ d ∈ st.cost x, AtMost
        (Function.update st.cost w (some (du + N.arrowCost i)) x) d := by
      intro x d hd
      by_cases hx : x = w
      · subst hx
        simp only [Function.update_self, AtMost]
        exact le_of_lt (lt_of_all hlt d hd)
      · rw [Function.update_of_ne hx, Option.mem_def.1 hd]; exact le_refl d
    refine
      { net := h.net
        source := h.source
        rounds := h.rounds
        drops := fun v d hd => atMost_lower (h.drops v d hd) (hlow v)
        tried := fun a ha d hd => ?_
        unlowered := by simp
        lowered := fun x hx => ?_
        count := by simp [h.count]; omega }
    · rcases List.mem_append.1 ha with ha | ha
      · exact atMost_lower (h.tried a ha d hd) (hlow _)
      · rw [List.mem_singleton.1 ha] at hd ⊢
        obtain ⟨du', hdu', hle⟩ := atMost_iff.1 (h.drops u d hd)
        rw [hu, Option.mem_def, Option.some.injEq] at hdu'
        subst hdu'
        simp only [Function.update_self, AtMost]
        linarith
    · simp only [Option.mem_def, Option.some.injEq] at hx
      subst hx
      refine ⟨hw, _, Function.update_self .., fun e he => ?_⟩
      obtain ⟨c, hc, hce⟩ := atMost_iff.1 (h.drops w e he)
      exact lt_of_lt_of_le (lt_of_all hlt c hc) hce

theorem Tries.row {st₀ : State} (u : ℕ) :
    ∀ (es : List (ℕ × ℕ)) {st : State} {l : List (ℕ × ℕ × ℕ)}, Tries N st₀ st l →
      (∀ e ∈ es, e ∈ N.g.out u) →
        Tries N st₀ (es.foldl (tryArrow N u) st) (l ++ es.map (u, ·))
  | [], _, _, h, _ => by simpa using h
  | e :: es, _, _, h, hes => by
    have h' := h.step (hes e (by simp))
    have := Tries.row u es h' (fun e' he' => hes e' (by simp [he']))
    simpa using this

theorem Tries.rows {st₀ : State} :
    ∀ (us : List ℕ) {st : State} {l : List (ℕ × ℕ × ℕ)}, Tries N st₀ st l →
      Tries N st₀ (us.foldl (fun acc u => (N.g.out u).foldl (tryArrow N u) acc) st)
        (l ++ us.flatMap fun u => (N.g.out u).map (u, ·))
  | [], _, _, h => by simpa using h
  | u :: us, _, _, h => by
    have h' := Tries.row u (N.g.out u) h (fun _ he => he)
    have := Tries.rows us h'
    simpa using this

/-- The arrows a round tries, each with the vertex it leaves: the vertices by increasing id, each
vertex's row in order. -/
def roundArrows (N : Network) : List (ℕ × ℕ × ℕ) :=
  (List.range N.g.n).flatMap fun u => (N.g.out u).map (u, ·)

theorem tries_round (N : Network) (st : State) :
    Tries N { st with rounds := st.rounds + 1, lowered := none } (round N st)
      (roundArrows N) := by
  simpa [round, roundArrows] using Tries.rows (List.range N.g.n) (Tries.start N st)

theorem mem_roundArrows {u w i : ℕ} :
    (u, w, i) ∈ roundArrows N ↔ u < N.g.n ∧ (w, i) ∈ N.g.out u := by
  simp [roundArrows]

variable {s : ℕ}

/-- **A round keeps the network and the start vertex.** -/
@[simp] theorem round_net (st : State) : (round N st).net = st.net :=
  (tries_round N st).net

@[simp] theorem round_source (st : State) : (round N st).source = st.source :=
  (tries_round N st).source

theorem round_rounds (st : State) : (round N st).rounds = st.rounds + 1 :=
  (tries_round N st).rounds

theorem round_tried (st : State) : (round N st).tried = st.tried + (roundArrows N).length :=
  (tries_round N st).count

/-- A round lowers costs or keeps them. -/
theorem round_lowers (st : State) (v : ℕ) : ∀ d ∈ st.cost v, AtMost ((round N st).cost v) d :=
  (tries_round N st).drops v

/-- After a round, every arrow out of a vertex with an old cost fits the new cost it points to. -/
theorem round_fits (st : State) {u w i : ℕ} (hu : u < N.g.n) (he : (w, i) ∈ N.g.out u) :
    ∀ du ∈ st.cost u, AtMost ((round N st).cost w) (du + N.arrowCost i) :=
  (tries_round N st).tried (u, w, i) (mem_roundArrows.2 ⟨hu, he⟩)

/-! ## What every try keeps -/

/-- A closed list that passes `w` after its first vertex passes it before its last. -/
theorem mem_dropLast_of_closed {c : List ℕ} {w : ℕ} (h2 : 2 ≤ c.length)
    (hc : c.head? = c.getLast?) (hw : w ∈ c) : w ∈ c.dropLast := by
  rcases List.eq_nil_or_concat' c with rfl | ⟨l, x, rfl⟩
  · simp at h2
  rw [List.dropLast_concat]
  rcases List.mem_append.1 hw with hw | hw
  · exact hw
  · obtain rfl := List.mem_singleton.1 hw
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil (show l ≠ [] by
      rintro rfl; simp at h2)
    have : a = w := by
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp)] at hc
      simpa using hc
    simp [this]

/-- **Writing a lowered cost keeps the invariants that do not count rounds**, on a well-formed
network: `w`'s cost drops to `u`'s plus the arrow's, and `w` records `u`. Around a cycle the records
now close, every recorded arrow fits and the one out of `w` fits strictly, so its arrows total
below zero (CLRS Lemma 22.16's argument). -/
theorem holds_write {st : State} (hN : st.net.WellFormed) (h : WellFormed st) {u w i : ℕ}
    {du : ℤ} (hi : st.net.g.arrows[i]? = some (u, w)) (hu : st.cost u = some du)
    (hlt : ∀ e ∈ st.cost w, du + st.net.arrowCost i < e) {cost' : ℕ → Option ℤ}
    {prev' : ℕ → Option ℕ} (hcw : cost' w = some (du + st.net.arrowCost i))
    (hcx : ∀ x, x ≠ w → cost' x = st.cost x) (hpw : prev' w = some u)
    (hpx : ∀ x, x ≠ w → prev' x = st.prev x) (r : ℕ) (lo : Option ℕ) {t : ℕ}
    (ht : st.tried + 1 ≤ t) : WellFormed ⟨st.net, st.source, cost', prev', r, lo, t⟩ := by
  set N := st.net with hNdef
  set s := st.source with hsdef
  obtain ⟨hC, hP, hR, hS⟩ := h
  have hun : u < N.g.n := (hN.1 _ (List.mem_of_getElem? hi)).1
  -- a cost only drops
  have hlow : ∀ x, ∀ d ∈ st.cost x, ∃ d' ∈ cost' x, d' ≤ d := by
    intro x d hd
    by_cases hx : x = w
    · rw [hx, hcw]; rw [hx] at hd; exact ⟨_, rfl, le_of_lt (hlt d hd)⟩
    · rw [hcx x hx]; exact ⟨d, hd, le_rfl⟩
  -- a loop on `u` that lowers its cost is negative
  have hloop : u = w → N.arrowCost i < 0 := by
    intro huw
    have := hlt du (by rw [← huw]; exact hu)
    linarith
  -- each record's arrow fits the costs as they are now, and strictly where it leaves `w`
  have hstep : ∀ a b, b < N.g.n → prev' b = some a → ∃ j, N.g.arrows[j]? = some (a, b) ∧
      (cost' a).getD 0 + N.arrowCost j ≤ (cost' b).getD 0 ∧
        (a = w → (cost' a).getD 0 + N.arrowCost j < (cost' b).getD 0) := by
    intro a b hb hab
    by_cases hbw : b = w
    · rw [hbw, hpw] at hab
      have hau : a = u := (Option.some.inj hab).symm
      rw [hbw, hau, hcw]
      refine ⟨i, hi, ?_⟩
      by_cases huw : u = w
      · have := hloop huw
        rw [huw, hcw]
        simp only [Option.getD_some]
        exact ⟨by linarith, fun _ => by linarith⟩
      · rw [hcx u huw, hu]
        simp only [Option.getD_some]
        exact ⟨le_rfl, fun h => absurd h huw⟩
    · rw [hpx b hbw] at hab
      obtain ⟨j, -, hj, da, hda, db, hdb, hle⟩ := hP b hb a hab
      refine ⟨j, hj, ?_⟩
      rw [hcx b hbw, Option.mem_def.1 hdb, Option.getD_some]
      by_cases haw : a = w
      · have := hlt da (by rw [← haw]; exact hda)
        rw [haw, hcw, Option.getD_some]
        exact ⟨by linarith, fun _ => by linarith⟩
      · rw [hcx a haw, Option.mem_def.1 hda, Option.getD_some]
        exact ⟨hle, fun h => absurd h haw⟩
  have h1 : ∀ v < N.g.n, ∀ d ∈ cost' v, ∃ p, N.IsWalk s p v ∧ p.length ≤ t ∧
      N.pathCost p = d := by
    intro v hv d hd
    by_cases hvw : v = w
    · rw [hvw, hcw, Option.mem_def, Option.some.injEq] at hd
      obtain ⟨p, hp, hl, hpc⟩ := hC u hun du hu
      refine ⟨p ++ [i], ?_, by simp; omega, by rw [pathCost_append, pathCost_singleton, hpc, hd]⟩
      rw [hvw]; exact hp.snoc hi
    · rw [hcx v hvw] at hd
      obtain ⟨p, hp, hl, hpc⟩ := hC v hv d hd
      exact ⟨p, hp, by omega, hpc⟩
  have h2 : ∀ v < N.g.n, ∀ x ∈ prev' v, ∃ j < N.g.arrows.length, N.g.arrows[j]? = some (x, v) ∧
      ∃ dx ∈ cost' x, ∃ dv ∈ cost' v, dx + N.arrowCost j ≤ dv := by
    intro v hv x hx
    obtain ⟨j, hj, hle, -⟩ := hstep x v hv hx
    -- both ends have costs now
    have hcx' : ∃ d, cost' x = some d := by
      by_cases hvw : v = w
      · rw [hvw, hpw, Option.mem_def, Option.some.injEq] at hx
        rw [← hx]
        by_cases huw : u = w
        · exact ⟨_, by rw [huw]; exact hcw⟩
        · exact ⟨du, by rw [hcx u huw]; exact hu⟩
      · rw [hpx v hvw] at hx
        obtain ⟨-, -, -, dx, hdx, -⟩ := hP v hv x hx
        obtain ⟨d', hd', -⟩ := hlow x dx hdx
        exact ⟨d', hd'⟩
    have hcv : ∃ d, cost' v = some d := by
      by_cases hvw : v = w
      · exact ⟨_, by rw [hvw]; exact hcw⟩
      · rw [hpx v hvw] at hx
        obtain ⟨-, -, -, -, -, dv, hdv, -⟩ := hP v hv x hx
        exact ⟨dv, by rw [hcx v hvw]; exact hdv⟩
    obtain ⟨dx, hdx⟩ := hcx'
    obtain ⟨dv, hdv⟩ := hcv
    refine ⟨j, (List.getElem?_eq_some_iff.1 hj).1, hj, dx, hdx, dv, hdv, ?_⟩
    rw [hdx, hdv, Option.getD_some, Option.getD_some] at hle
    exact hle
  have h3 : ∀ l, RecordsClose N prev' l →
      ∃ v p, N.IsWalk v p v ∧ N.visits v p = l ∧ N.pathCost p < 0 := by
    intro l hl
    obtain ⟨hlt', hch, hlen, hhd, hnd⟩ := hl
    by_cases hwl : w ∈ l
    · obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil (show l ≠ [] by
        rintro rfl; simp at hlen)
      have hch' := isChain_imp_of_mem (fun x y hy hxy => hstep x y (hlt' y hy) hxy) hch
      obtain ⟨p, hp, hvis, -, hneg⟩ := walk_of_fits (N := N) (fun v => (cost' v).getD 0) w l' a
        hch'
      have hlast : (a :: l').getLast (by simp) = a := by
        simp only [List.head?_cons, List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _),
          Option.some.injEq] at hhd
        exact hhd.symm
      rw [hlast] at hp hneg
      exact ⟨a, p, hp, hvis, by linarith [hneg (mem_dropLast_of_closed hlen hhd hwl)]⟩
    · refine hR l ⟨hlt', isChain_imp_of_mem (fun x y hy hxy => ?_) hch, hlen, hhd, hnd⟩
      have hyw : y ≠ w := fun h => hwl (h ▸ hy)
      rwa [hpx y hyw] at hxy
  have h4 : ∀ v < N.g.n, prev' v = none → cost' v = if v = s then some 0 else none := by
    intro v hv hpv
    by_cases hvw : v = w
    · rw [hvw, hpw] at hpv; exact absurd hpv (by simp)
    · rw [hpx v hvw] at hpv
      rw [hcx v hvw]
      exact hS v hv hpv
  exact ⟨h1, h2, h3, h4⟩

/-- **A try keeps the invariants that do not count rounds**, on a well-formed network. -/
theorem holds_tryArrow (hN : N.WellFormed) {st : State} (hn : st.net = N) (h : WellFormed st)
    {u w i : ℕ} (he : (w, i) ∈ N.g.out u) : WellFormed (tryArrow N u st (w, i)) := by
  subst hn
  obtain ⟨-, hi⟩ := mem_out.1 he
  rcases tryArrow_cases u st w i with ⟨heq, -⟩ | ⟨du, hu, hlt, heq⟩
  · rw [heq]
    refine ⟨fun v hv d hd => ?_, h.2⟩
    obtain ⟨p, hp, hl, hc⟩ := h.1 v hv d hd
    exact ⟨p, hp, by simp only; omega, hc⟩
  rw [heq]
  exact holds_write hN h hi hu (lt_of_all hlt) (Function.update_self ..)
    (fun _ hx => Function.update_of_ne hx _ _) (Function.update_self ..)
    (fun _ hx => Function.update_of_ne hx _ _) _ _ le_rfl

/-- A try keeps the network. -/
theorem tryArrow_net (u : ℕ) (st : State) (e : ℕ × ℕ) : (tryArrow N u st e).net = st.net := by
  unfold tryArrow
  split
  · rfl
  · split <;> rfl

theorem foldl_tryArrow_net (u : ℕ) :
    ∀ (es : List (ℕ × ℕ)) (st : State), (es.foldl (tryArrow N u) st).net = st.net
  | [], _ => rfl
  | e :: es, st => (foldl_tryArrow_net u es _).trans (tryArrow_net u st e)

theorem holds_row (hN : N.WellFormed) (u : ℕ) :
    ∀ (es : List (ℕ × ℕ)) {st : State}, st.net = N → WellFormed st →
      (∀ e ∈ es, e ∈ N.g.out u) → WellFormed (es.foldl (tryArrow N u) st)
  | [], _, _, h, _ => h
  | (w, i) :: es, _, hn, h, hes =>
    holds_row hN u es ((tryArrow_net _ _ _).trans hn) (holds_tryArrow hN hn h (hes _ (by simp)))
      fun e he => hes e (by simp [he])

theorem holds_rows (hN : N.WellFormed) :
    ∀ (us : List ℕ) {st : State}, st.net = N → WellFormed st →
      WellFormed (us.foldl (fun acc u => (N.g.out u).foldl (tryArrow N u) acc) st)
  | [], _, _, h => h
  | u :: us, _, hn, h =>
    holds_rows hN us ((foldl_tryArrow_net u _ _).trans hn)
      (holds_row hN u (N.g.out u) hn h fun _ he => he)

/-- **A round keeps the invariants that do not count rounds.** -/
theorem holds_round (hN : N.WellFormed) {st : State} (hn : st.net = N) (h : WellFormed st) :
    WellFormed (round N st) :=
  holds_rows hN (List.range N.g.n) (st := { st with rounds := st.rounds + 1, lowered := none }) hn
    h

theorem mem_start_cost {v : ℕ} {d : ℤ} : d ∈ (start N s).cost v ↔ v = s ∧ d = 0 := by
  simp only [start, Function.update_apply, Option.mem_def]
  split_ifs with h <;> simp [h, eq_comm]

theorem valid_start (hs : s < N.g.n) : Valid (start N s) ∧ WellFormed (start N s) := by
  refine ⟨fun v _ => ⟨fun d hd => ?_, fun p hp hl => ?_⟩, fun v _ d hd => ?_, ?_, ?_, ?_⟩
  · obtain ⟨rfl, rfl⟩ := mem_start_cost.1 hd
    exact ⟨[], isWalk_nil v, rfl⟩
  · have : p = [] := List.eq_nil_of_length_eq_zero (by simpa [start] using hl)
    subst this
    rw [isWalk_nil_iff.1 hp]
    simp [start, AtMost, pathCost]
  · obtain ⟨rfl, rfl⟩ := mem_start_cost.1 hd
    exact ⟨[], isWalk_nil v, by simp [start], rfl⟩
  · intro v _ u hu
    simp [start] at hu
  · rintro c ⟨-, hch, hlen, -⟩
    rcases c with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hlen
    · simp at hlen
    · simp [start] at hch
  · intro v _ _
    change Function.update (fun _ => none) s (some 0) v = if v = s then some 0 else none
    simp only [Function.update_apply]

/-- **A round keeps the invariants.** -/
theorem valid_round (hN : N.WellFormed) (hs : s < N.g.n) {st : State} (hn : st.net = N)
    (hsrc : st.source = s) (h : Valid st ∧ WellFormed st) :
    Valid (round N st) ∧ WellFormed (round N st) := by
  obtain ⟨hC, hH⟩ := h
  obtain ⟨hW', hP', hR', hS'⟩ := holds_round hN hn hH
  subst hn hsrc
  set N := st.net with hNdef
  set s := st.source with hsdef
  refine ⟨?_, hW', hP', hR', hS'⟩
  have hW := hW'
  unfold PathWithinTries at hW
  unfold Valid CostIsWalkAtMostCheapest
  rw [round_net, round_source] at hW ⊢
  refine fun v hv => ⟨fun d hd => ?_, fun p hp hl => ?_⟩
  · obtain ⟨p, hp, -, hc⟩ := hW v hv d hd
    exact ⟨p, hp, hc⟩
  rcases eq_or_ne p [] with rfl | hne
  · rw [isWalk_nil_iff.1 hp] at hv ⊢
    have := (hC s hs).2 [] (isWalk_nil s) (by simp)
    obtain ⟨d, hd, hd0⟩ := atMost_iff.1 this
    exact atMost_trans_le (round_lowers st s d hd) hd0
  · obtain ⟨q, i, x, rfl, hq, hi⟩ := hp.eq_snoc hne
    have hx : x < N.g.n := hq.lt hN hs
    have hlq : q.length ≤ st.rounds := by simp [round_rounds] at hl; omega
    obtain ⟨dx, hdx, hdxq⟩ := atMost_iff.1 ((hC x hx).2 q hq hlq)
    have := round_fits st hx (mem_out.2 ⟨hv, hi⟩) dx hdx
    refine atMost_trans_le this ?_
    rw [pathCost_append, pathCost_singleton]
    linarith

/-- Box invariant 1 read on the network and the start vertex the state carries. -/
theorem cost_on {st : State} (hn : st.net = N) (hsrc : st.source = s)
    (h : CostIsWalkAtMostCheapest st) : ∀ v < N.g.n,
      (∀ d ∈ st.cost v, ∃ p, N.IsWalk s p v ∧ N.pathCost p = d) ∧
        ∀ p, N.IsWalk s p v → p.length ≤ st.rounds → AtMost (st.cost v) (N.pathCost p) := by
  subst hn hsrc
  exact h

/-- **`Valid` and `WellFormed` together are the five pieces the rounds keep**, the box's one and
the four the rounds need beyond it. -/
theorem valid_and_wellFormed_iff (st : State) :
    Valid st ∧ WellFormed st ↔ CostIsWalkAtMostCheapest st ∧ PathWithinTries st ∧
      PreviousArrowFits st ∧ RecordedCyclesBelowZero st ∧ NoPreviousKeepsStart st :=
  Iff.rfl

/-! ## A round that lowers nothing -/

/-- Every arrow out of a vertex with a cost fits the cost of the vertex it points to. -/
def ArrowsFit (N : Network) (st : State) : Prop :=
  ∀ u < N.g.n, ∀ e ∈ N.g.out u, ∀ du ∈ st.cost u, AtMost (st.cost e.1) (du + N.arrowCost e.2)

/-- After a round that lowers nothing, every arrow fits. -/
theorem arrowsFit_round (st : State) (h : (round N st).lowered = none) :
    ArrowsFit N (round N st) := by
  intro u hu e he du hdu
  have hc := fun v => ((tries_round N st).unlowered h v).1
  rw [hc] at hdu
  exact round_fits st hu he du hdu

/-- When every arrow fits, a vertex's cost is at most the cost of any path to it from a vertex
with a cost, added to that cost. -/
theorem atMost_of_walk (hN : N.WellFormed) {st : State} (hF : ArrowsFit N st) {u : ℕ}
    {du : ℤ} (hdu : du ∈ st.cost u) :
    ∀ {p : List ℕ} {v : ℕ}, N.IsWalk u p v → AtMost (st.cost v) (du + N.pathCost p) := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
    intro v hp
    rw [isWalk_nil_iff.1 hp, Option.mem_def.1 hdu]
    simp [AtMost, pathCost]
  | append_singleton p i ih =>
    intro v hp
    obtain ⟨x, hx, hi⟩ := ends_append_singleton.1 hp
    obtain ⟨dx, hdx, hle⟩ := atMost_iff.1 (ih hx)
    have hxv := hN.1 _ (List.mem_of_getElem? hi)
    refine atMost_trans_le (hF x hxv.1 (v, i) (mem_out.2 ⟨hxv.2, hi⟩) dx hdx) ?_
    rw [pathCost_append, pathCost_singleton]
    simp only
    linarith

/-- **When every arrow fits, no negative cycle is reached**: going round it once more would
lower the cost of its first vertex. -/
theorem no_cycle_of_fit (hN : N.WellFormed) (hs : s < N.g.n) {st : State} (hn : st.net = N)
    (hsrc : st.source = s) (hV : Valid st ∧ WellFormed st) (hF : ArrowsFit N st) :
    ¬ ∃ c, CycleBelowZero N s c := by
  subst hn hsrc
  set N := st.net with hNdef
  set s := st.source with hsdef
  rintro ⟨-, v, p, ⟨-, hp, -⟩, -, hneg, hr⟩
  obtain ⟨d₀, hd₀, -⟩ := atMost_iff.1 ((hV.1 s hs).2 [] (isWalk_nil s) (by simp))
  obtain ⟨q, hq⟩ := exists_isWalk_of_reaches hr
  obtain ⟨dv, hdv, -⟩ := atMost_iff.1 (atMost_of_walk hN hF hd₀ hq)
  obtain ⟨dv', hdv', hle⟩ := atMost_iff.1 (atMost_of_walk hN hF hdv hp)
  rw [Option.mem_unique hdv' hdv] at hle
  linarith

/-! ## The run -/

theorem runRounds_cases (hN : N.WellFormed) (hs : s < N.g.n) :
    ∀ f {st : State}, st.net = N → st.source = s → Valid st ∧ WellFormed st →
      ∃ st', (st'.net = N ∧ st'.source = s ∧ Valid st' ∧ WellFormed st') ∧
        runRounds (round N) (f + 1) st = round N st' ∧
          ((round N st').lowered = none ∨ (round N st').rounds = st.rounds + f + 1)
  | 0, st, hn, hsrc, h => ⟨st, ⟨hn, hsrc, h⟩, by simp only [runRounds]; split_ifs <;> rfl,
      Or.inr (by rw [round_rounds])⟩
  | f + 1, st, hn, hsrc, h => by
    rw [runRounds]
    split_ifs with hl
    · exact ⟨st, ⟨hn, hsrc, h⟩, rfl, Or.inl hl⟩
    · obtain ⟨st', h', he, hor⟩ := runRounds_cases hN hs f ((round_net _).trans hn)
        ((round_source _).trans hsrc) (valid_round hN hs hn hsrc h)
      refine ⟨st', h', he, hor.imp_right fun h => ?_⟩
      rw [h, round_rounds]; omega

theorem runRounds_count (N : Network) :
    ∀ f (st : State), (runRounds (round N) f st).rounds ≤ st.rounds + f ∧
      (runRounds (round N) f st).tried + st.rounds * (roundArrows N).length =
        st.tried + (runRounds (round N) f st).rounds * (roundArrows N).length
  | 0, st => by simp [runRounds]
  | f + 1, st => by
    rw [runRounds]
    have hr := round_rounds (N := N) st
    have ht := round_tried (N := N) st
    split_ifs with hl
    · refine ⟨by omega, ?_⟩
      rw [hr, ht, Nat.add_mul, one_mul]; omega
    · obtain ⟨h1, h2⟩ := runRounds_count N f (round N st)
      rw [hr] at h1
      rw [hr, ht] at h2
      refine ⟨by omega, ?_⟩
      rw [Nat.add_mul, one_mul] at h2
      omega

/-- On a well-formed network a round tries every arrow once. -/
theorem length_roundArrows (hN : N.WellFormed) : (roundArrows N).length = N.g.arrows.length := by
  have hids : (roundArrows N).map (·.2.2) =
      Dijkstra.tried N ⟨N, 0, List.range N.g.n, fun _ => none, fun _ => none, [], 0⟩ := by
    simp [roundArrows, Dijkstra.tried, List.map_flatMap, Function.comp_def]
  have hnd : ((roundArrows N).map (·.2.2)).Nodup := by
    rw [hids]; exact Dijkstra.nodup_tried List.nodup_range
  rw [← List.length_map (f := (·.2.2))]
  refine le_antisymm ?_ ?_
  · rw [hids]; exact Dijkstra.length_tried_le List.nodup_range
  · have := (List.nodup_range (n := N.g.arrows.length)).length_le_of_subset
      (l₂ := (roundArrows N).map (·.2.2)) (fun i hi => ?_)
    · simpa using this
    · have hlt := List.mem_range.1 hi
      have hmem := List.getElem_mem hlt
      have hab := hN.1 _ hmem
      refine List.mem_map.2 ⟨(N.g.arrows[i].1, N.g.arrows[i].2, i), mem_roundArrows.2 ⟨hab.1, ?_⟩,
        rfl⟩
      exact mem_out.2 ⟨hab.2, by simp [List.getElem?_eq_getElem hlt]⟩

/-! ## The answer -/

/-- The state the run ends in. -/
def final (N : Network) (s : ℕ) : State := runRounds (round N) N.g.n (start N s)

theorem final_cases (hN : N.WellFormed) (hs : s < N.g.n) :
    ∃ st', (st'.net = N ∧ st'.source = s ∧ Valid st' ∧ WellFormed st') ∧
      final N s = round N st' ∧ ((round N st').lowered = none ∨ (round N st').rounds = N.g.n) := by
  obtain ⟨f, hf⟩ : ∃ f, N.g.n = f + 1 := ⟨N.g.n - 1, by omega⟩
  obtain ⟨st', h, he, hor⟩ := runRounds_cases hN hs f rfl rfl (valid_start hs)
  refine ⟨st', h, by rw [final, hf]; exact he, hor.imp_right fun h => ?_⟩
  rw [h, hf]; simp [start]

theorem final_valid (hN : N.WellFormed) (hs : s < N.g.n) :
    Valid (final N s) ∧ WellFormed (final N s) := by
  obtain ⟨st', ⟨hn, hsrc, h⟩, he, -⟩ := final_cases hN hs
  rw [he]; exact valid_round hN hs hn hsrc h

/-- **The run keeps the network and the start vertex.** -/
theorem final_net (N : Network) (s : ℕ) : (final N s).net = N ∧ (final N s).source = s := by
  suffices ∀ f (st : State), (runRounds (round N) f st).net = st.net ∧
      (runRounds (round N) f st).source = st.source from this _ _
  intro f
  induction f with
  | zero => exact fun _ => ⟨rfl, rfl⟩
  | succ f ih =>
    intro st
    rw [runRounds]
    split_ifs
    · exact ⟨round_net st, round_source st⟩
    · exact ⟨(ih _).1.trans (round_net st), (ih _).2.trans (round_source st)⟩

/-- **A run that ends on a round still lowering a cost answers a negative cycle.** -/
theorem final_cycle (hN : N.WellFormed) (hs : s < N.g.n) {x : ℕ}
    (hx : (final N s).lowered = some x) :
    CycleBelowZero N s (cycleFrom (final N s).prev N.g.n x) := by
  obtain ⟨st', ⟨hn, hsrc, hV'⟩, he, hor⟩ := final_cases hN hs
  have hV := final_valid hN hs
  rw [he] at hx hV ⊢
  subst hn hsrc
  set N := st'.net with hNdef
  set s := st'.source with hsdef
  have hT := tries_round N st'
  obtain ⟨hxn, dx, hdx, hbelow⟩ := hT.lowered x hx
  have hrounds : st'.rounds + 1 = N.g.n := by
    rcases hor with h | h
    · rw [hx] at h; exact absurd h (by simp)
    · rw [round_rounds] at h; exact h
  by_cases h : ∃ t, (round N st').prev ((stepBack (round N st').prev)^[t] x) = none
  · exfalso
    obtain ⟨p, hp, -, hc⟩ := path_of_none hN (round_net st') (round_source st') hV hxn
      (by rw [Option.mem_def.1 hdx]; simp) h
    have hl := hp.length_lt hN hs
    obtain ⟨e, he, hep⟩ := atMost_iff.1 ((hV'.1 x hxn).2 p hp.isWalk (by omega))
    have := hbelow e he
    have := hc dx hdx
    linarith
  · push Not at h
    exact cycle_of_defined hN (round_net st') (round_source st') hV hxn
      (by rw [Option.mem_def.1 hdx]; simp) h

theorem bellmanFord_eq (N : Network) (s : ℕ) : bellmanFord N s = answer N (final N s) := rfl

theorem bellmanFord_error (hN : N.WellFormed) (hs : s < N.g.n) {c : List ℕ}
    (h : bellmanFord N s = .error c) : CycleBelowZero N s c := by
  rw [bellmanFord_eq, answer] at h
  split at h
  · exact absurd h (by simp)
  · rename_i x hx
    simp only [Except.error.injEq] at h
    subst h
    exact final_cycle hN hs hx

theorem bellmanFord_cycle_exists (hN : N.WellFormed) (hs : s < N.g.n)
    (h : ∃ c, CycleBelowZero N s c) : ∃ c, bellmanFord N s = .error c := by
  rw [bellmanFord_eq, answer]
  split
  · rename_i hl
    exfalso
    obtain ⟨st', ⟨hn, hsrc, hV'⟩, he, -⟩ := final_cases hN hs
    rw [he] at hl
    have hF := arrowsFit_round st' hl
    exact no_cycle_of_fit hN hs ((round_net _).trans hn) ((round_source _).trans hsrc)
      (valid_round hN hs hn hsrc hV') hF h
  · exact ⟨_, rfl⟩

/-- **Without a negative cycle that the start reaches, the answer is each vertex's cheapest
cost**, with the path its previous vertices lead back along. -/
theorem bellmanFord_cheapest (hN : N.WellFormed) (hs : s < N.g.n)
    (hno : ¬ ∃ c, CycleBelowZero N s c) :
    ∃ a, bellmanFord N s = .ok a ∧ ∀ v < N.g.n, N.Cheapest s v (a.cost v) ∧
      ∀ d ∈ a.cost v, ∃ p, N.IsPath s p v ∧ N.pathCost p = d ∧
        LeadsBack a.prev s (N.visits s p) := by
  have hV := final_valid hN hs
  obtain ⟨hfn, hfs⟩ := final_net N s
  have hl : (final N s).lowered = none := by
    cases hx : (final N s).lowered with
    | none => rfl
    | some x => exact absurd ⟨_, final_cycle hN hs hx⟩ hno
  have hF : ArrowsFit N (final N s) := by
    obtain ⟨st', -, he, -⟩ := final_cases hN hs
    rw [he] at hl ⊢
    exact arrowsFit_round st' hl
  obtain ⟨ds, hds, hds0⟩ := atMost_iff.1 ((cost_on hfn hfs hV.1 s hs).2 [] (isWalk_nil s)
    (by simp))
  simp only [pathCost, List.map_nil, List.sum_nil] at hds0
  have hle : ∀ {p v}, N.IsWalk s p v → AtMost ((final N s).cost v) (N.pathCost p) :=
    fun hp => atMost_trans_le (atMost_of_walk hN hF hds hp) (by linarith)
  have hback : ∀ v < N.g.n, ∀ d ∈ (final N s).cost v, ∃ p, N.IsPath s p v ∧
      N.pathCost p = d ∧ LeadsBack (final N s).prev s (N.visits s p) := by
    intro v hv d hd
    by_cases h : ∃ t, (final N s).prev ((stepBack (final N s).prev)^[t] v) = none
    · obtain ⟨p, hp, hlb, hc⟩ :=
        path_of_none hN hfn hfs hV hv (by rw [Option.mem_def.1 hd]; simp) h
      obtain ⟨d', hd', hd'p⟩ := atMost_iff.1 (hle hp.isWalk)
      rw [Option.mem_unique hd' hd] at hd'p
      exact ⟨p, hp, le_antisymm (hc d hd) hd'p, hlb⟩
    · push Not at h
      exact absurd ⟨_, cycle_of_defined hN hfn hfs hV hv (by rw [Option.mem_def.1 hd]; simp) h⟩
        hno
  refine ⟨⟨(final N s).cost, (final N s).prev⟩, by rw [bellmanFord_eq, answer, hl], fun v hv =>
    ⟨⟨fun p hp _ => hle hp.isWalk, fun d hd => ?_⟩, hback v hv⟩⟩
  obtain ⟨p, hp, hc, -⟩ := hback v hv d hd
  exact ⟨p, hp, trivial, hc⟩

/-- **At most one round per vertex, each trying every arrow.** -/
theorem bellmanFord_cost (hN : N.WellFormed) (s : ℕ) :
    (final N s).rounds ≤ N.g.n ∧
      (final N s).tried = (final N s).rounds * N.g.arrows.length := by
  obtain ⟨h1, h2⟩ := runRounds_count N N.g.n (start N s)
  rw [length_roundArrows hN] at h2
  simp only [start, zero_mul, add_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

end AlgoDesign.Paths.BellmanFord
