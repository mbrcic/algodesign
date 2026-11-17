/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.Steps
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Assignment: what the search keeps

Sources: Kleinberg and Tardos, *Algorithm Design*, §7.13, (7.65), p. 409; Ahuja, Magnanti and
Orlin, *Network Flows* (1993), §12.4, p. 471.

While one person's search runs, the labels fit every pair of the people already placed, and are
exact on their pairs (`Inv`). Each object not visited keeps its best changed cost, at most the
changed cost from any person reached and equal to it from the person recorded. A pick's value is
the smallest of these, so moving the labels by it keeps every pair fitting, and the picked object's
pair with its recorded person becomes exact (`update_inv`); the pairs of the visited objects with
their recorded persons stay exact, since both labels move by the same value. Each visited object's
recorded person is the new person or the holder of an object visited before it (`Inv.chain`), so
the walk back from the free object ends at the new person.
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-! ## Lists built entry by entry -/

theorem ite_yes {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_no {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem length_build {α : Type} (n : ℕ) (f : ℕ → α) : (build n f).length = n := by
  simp [build]

theorem at_build {n j : ℕ} (f : ℕ → ℤ) (h : j < n) : Labels.at (build n f) j = f j := by
  simp [build, Labels.at, List.getD_eq_getElem?_getD, h]

theorem getD_build {n j : ℕ} (f : ℕ → ℕ) (h : j < n) : (build n f).getD j 0 = f j := by
  simp [build, List.getD_eq_getElem?_getD, h]

theorem getD_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_mem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [getD_of_lt h]; exact List.getElem_mem h

theorem reached_iff (obj : List ℕ) (cur : ℕ) (vis : List ℕ) (r : ℕ) :
    reached obj cur vis r = true ↔ r = cur ∨ (r < obj.length ∧ obj.getD r 0 ∈ vis) := by
  simp [reached]

theorem reached_mono {obj : List ℕ} {cur : ℕ} {vis : List ℕ} {r : ℕ} (x : ℕ)
    (h : reached obj cur vis r = true) : reached obj cur (vis ++ [x]) r = true := by
  rw [reached_iff] at h ⊢
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, List.mem_append_left _ h2⟩

/-! ## A pick -/

theorem pickFrom_spec (obj : List ℕ) (s : Search) : ∀ (cands : List ℕ) (acc : Option ℕ) (j : ℕ),
    pickFrom obj s cands acc = some j →
      (j ∈ cands ∨ acc = some j) ∧ (∀ x ∈ cands, s.best.at j ≤ s.best.at x) ∧
        ∀ b, acc = some b → s.best.at j ≤ s.best.at b
  | [], acc, j, h => by
    simp only [pickFrom] at h
    exact ⟨Or.inr h, by simp, fun b hb => by rw [h] at hb; cases hb; exact le_rfl⟩
  | x :: xs, none, j, h => by
    simp only [pickFrom] at h
    obtain ⟨h1, h2, h3⟩ := pickFrom_spec obj s xs (some x) j h
    refine ⟨?_, ?_, by simp⟩
    · rcases h1 with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · cases h1; exact Or.inl (List.mem_cons_self ..)
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h3 _ rfl
      · exact h2 y hy
  | x :: xs, some b, j, h => by
    simp only [pickFrom] at h
    have hle : ∀ c, (if before obj s x b = true then some x else some b) = some c →
        s.best.at c ≤ s.best.at x ∧ s.best.at c ≤ s.best.at b := by
      intro c hc
      by_cases hx : before obj s x b = true
      · simp only [hx, ↓reduceIte] at hc; cases hc
        refine ⟨le_rfl, ?_⟩
        simp only [before, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | ⟨⟨hx, _⟩, _⟩ <;> omega
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hc; cases hc
        refine ⟨?_, le_rfl⟩
        simp only [before, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or] at hx
        omega
    obtain ⟨h1, h2, h3⟩ := pickFrom_spec obj s xs _ j h
    obtain ⟨c, hc⟩ : ∃ c, (if before obj s x b = true then some x else some b) = some c := by
      split <;> exact ⟨_, rfl⟩
    have hjc := h3 c hc
    have hcxb := hle c hc
    refine ⟨?_, ?_, fun b' hb' => ?_⟩
    · rcases h1 with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · rw [hc] at h1; cases h1
        by_cases hx : before obj s x b = true
        · simp only [hx, ↓reduceIte] at hc; cases hc; exact Or.inl (List.mem_cons_self ..)
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hc; cases hc; exact Or.inr rfl
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact h2 y hy
    · cases hb'; omega

theorem pickFrom_isSome (obj : List ℕ) (s : Search) : ∀ (cands : List ℕ) (b : ℕ),
    (pickFrom obj s cands (some b)).isSome
  | [], b => rfl
  | x :: xs, b => by
    simp only [pickFrom]
    split <;> exact pickFrom_isSome obj s xs _

/-- **What a pick gives**: an object of the table not yet visited, with the smallest best changed
cost among those not visited. -/
theorem pick_spec {P : Problem} {obj : List ℕ} {s : Search} {j : ℕ}
    (h : pick P obj s = some j) :
    j < P.n ∧ j ∉ s.visited ∧ ∀ x < P.n, x ∉ s.visited → s.best.at j ≤ s.best.at x := by
  obtain ⟨h1, h2, -⟩ := pickFrom_spec obj s _ none j h
  have h1 : j ∈ (List.range P.n).filter fun j => j ∉ s.visited := by simpa using h1
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at h1
  refine ⟨h1.1, h1.2, fun x hx hxv => h2 x ?_⟩
  simp [hx, hxv]

/-- A pick finds an object whenever one is not yet visited. -/
theorem pick_isSome {P : Problem} {obj : List ℕ} {s : Search} {x : ℕ} (hx : x < P.n)
    (hxv : x ∉ s.visited) : (pick P obj s).isSome := by
  unfold pick
  obtain ⟨c, cs, hc⟩ : ∃ c cs, ((List.range P.n).filter fun j => j ∉ s.visited) = c :: cs := by
    refine List.exists_cons_of_ne_nil fun h => ?_
    have : x ∈ (List.range P.n).filter fun j => j ∉ s.visited := by simp [hx, hxv]
    rw [h] at this; simp at this
  rw [hc]
  exact pickFrom_isSome obj s cs c

/-! ## The search's invariants -/

/-- **What the search keeps**, from the state a step starts with: the people placed hold
different objects; the labels fit every pair of a person placed and are exact on their pairs; the
object labels are at most 0, and 0 on the free objects; every object not visited holds the smallest
changed cost from the persons reached, recorded with the person it came from; the new person fits
the visited objects; after the first pick no best changed cost is below 0; every visited object is
exact with its recorded person, who is the new person or the holder of an object visited before. -/
structure Inv (P : Problem) (obj : List ℕ) (s : Search) : Prop where
  assign : IsAssignmentOf P obj
  short : obj.length < P.n
  nodup : s.visited.Nodup
  held : ∀ j ∈ s.visited, j ∈ obj
  fit : ∀ i < obj.length, ∀ j < P.n, s.u.at i + s.v.at j ≤ P.costAt i j
  exact : ∀ i < obj.length, s.u.at i + s.v.at (obj.getD i 0) = P.costAt i (obj.getD i 0)
  nonpos : ∀ j < P.n, s.v.at j ≤ 0
  free : ∀ j < P.n, j ∉ obj → s.v.at j = 0
  below : ∀ j < P.n, j ∉ s.visited → ∀ r, reached obj obj.length s.visited r = true →
    s.best.at j ≤ changed P s.u s.v r j
  viaReached : ∀ j < P.n, j ∉ s.visited →
    reached obj obj.length s.visited (s.via.getD j 0) = true
  bestEq : ∀ j < P.n, j ∉ s.visited → s.best.at j = changed P s.u s.v (s.via.getD j 0) j
  curFit : ∀ j ∈ s.visited, s.u.at obj.length + s.v.at j ≤ P.costAt obj.length j
  bestNonneg : s.visited ≠ [] → ∀ j < P.n, j ∉ s.visited → 0 ≤ s.best.at j
  tight : ∀ j ∈ s.visited, s.u.at (s.via.getD j 0) + s.v.at j = P.costAt (s.via.getD j 0) j
  chain : ∀ t (h : t < s.visited.length), s.via.getD s.visited[t] 0 = obj.length ∨
    (s.via.getD s.visited[t] 0 < obj.length ∧
      obj.getD (s.via.getD s.visited[t] 0) 0 ∈ s.visited.take t)

namespace Inv

variable {P : Problem} {obj : List ℕ} {s : Search}

theorem reached_lt (hI : Inv P obj s) {r : ℕ} (h : reached obj obj.length s.visited r = true) :
    r < P.n := by
  rcases (reached_iff ..).1 h with rfl | ⟨h, -⟩
  · exact hI.short
  · exact h.trans hI.short

theorem obj_lt (hI : Inv P obj s) {i : ℕ} (h : i < obj.length) : obj.getD i 0 < P.n :=
  hI.assign.1 _ (getD_mem h)

theorem visited_lt (hI : Inv P obj s) {j : ℕ} (h : j ∈ s.visited) : j < P.n :=
  hI.assign.1 _ (hI.held j h)

theorem cur_reached (obj : List ℕ) (vis : List ℕ) :
    reached obj obj.length vis obj.length = true := (reached_iff ..).2 (Or.inl rfl)

/-- The recorded person of a visited object is reached. -/
theorem via_reached (hI : Inv P obj s) {j : ℕ} (h : j ∈ s.visited) :
    reached obj obj.length s.visited (s.via.getD j 0) = true := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 h
  rw [reached_iff]
  rcases hI.chain t ht with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, List.mem_of_mem_take h2⟩

/-- A person placed is reached exactly when their object is visited. -/
theorem reached_placed {i : ℕ} (hi : i < obj.length) (vis : List ℕ) :
    reached obj obj.length vis i = true ↔ obj.getD i 0 ∈ vis := by
  rw [reached_iff]
  constructor
  · rintro (h | ⟨-, h⟩)
    · omega
    · exact h
  · exact fun h => Or.inr ⟨hi, h⟩

end Inv

/-! ## Moving the labels by a pick's value -/

section update

variable {P : Problem} {obj : List ℕ} {s : Search} {δ : ℤ}

theorem update_visited : (update P obj obj.length s δ).visited = s.visited := rfl
theorem update_via : (update P obj obj.length s δ).via = s.via := rfl

theorem update_u {r : ℕ} (h : r < P.n) : (update P obj obj.length s δ).u.at r =
    s.u.at r + if reached obj obj.length s.visited r then δ else 0 := at_build _ h

theorem update_v {j : ℕ} (h : j < P.n) : (update P obj obj.length s δ).v.at j =
    s.v.at j - if j ∈ s.visited then δ else 0 := at_build _ h

theorem update_best {j : ℕ} (h : j < P.n) : (update P obj obj.length s δ).best.at j =
    s.best.at j - if j ∈ s.visited then 0 else δ := at_build _ h

theorem update_changed {r j : ℕ} (hr : r < P.n) (hj : j < P.n) :
    changed P (update P obj obj.length s δ).u (update P obj obj.length s δ).v r j =
      changed P s.u s.v r j - (if reached obj obj.length s.visited r then δ else 0) +
        (if j ∈ s.visited then δ else 0) := by
  simp only [changed, update_u hr, update_v hj]
  ring

end update

/-- **A pick keeps the invariants**: moving the labels by the picked value `δ`, the smallest best
changed cost of an object not visited, keeps every pair fitting and every exact pair exact; no
best changed cost of an object not visited is below 0 afterwards, and the picked one's is 0. -/
theorem update_inv {P : Problem} {obj : List ℕ} {s : Search} {j₁ : ℕ} (hI : Inv P obj s)
    (hj₁ : j₁ < P.n) (hv₁ : j₁ ∉ s.visited)
    (hmin : ∀ x < P.n, x ∉ s.visited → s.best.at j₁ ≤ s.best.at x) :
    Inv P obj (update P obj obj.length s (s.best.at j₁)) ∧
      (∀ j < P.n, j ∉ s.visited → 0 ≤ (update P obj obj.length s (s.best.at j₁)).best.at j) ∧
      (update P obj obj.length s (s.best.at j₁)).best.at j₁ = 0 := by
  set δ := s.best.at j₁ with hδ
  -- the value is at least 0 once an object is visited
  have hδpos : s.visited ≠ [] → 0 ≤ δ := fun h => hI.bestNonneg h j₁ hj₁ hv₁
  have hpos : ∀ j < P.n, j ∉ s.visited →
      0 ≤ (update P obj obj.length s δ).best.at j := by
    intro j hj hjv
    rw [update_best hj, ite_no hjv]
    linarith [hmin j hj hjv]
  refine ⟨⟨hI.assign, hI.short, hI.nodup, hI.held, ?fit, ?exact, ?nonpos, ?free, ?below, ?via,
    ?bestEq, ?curFit, fun _ => hpos, ?tight, hI.chain⟩, hpos, ?zero⟩
  case fit =>
    intro i hi j hj
    have hin : i < P.n := hi.trans hI.short
    rw [update_u hin, update_v hj]
    have := hI.fit i hi j hj
    by_cases hr : reached obj obj.length s.visited i = true
    · by_cases hjv : j ∈ s.visited
      · simp only [hr, hjv, ↓reduceIte]; linarith
      · simp only [hr, hjv, ↓reduceIte]
        have h1 := hI.below j hj hjv i hr
        have h2 := hmin j hj hjv
        simp only [changed] at h1
        linarith
    · by_cases hjv : j ∈ s.visited
      · simp only [hr, hjv, Bool.false_eq_true, ↓reduceIte]
        have := hδpos (List.ne_nil_of_mem hjv); linarith
      · simp only [hr, hjv, Bool.false_eq_true, ↓reduceIte]; linarith
  case exact =>
    intro i hi
    rw [update_u (hi.trans hI.short), update_v (hI.obj_lt hi)]
    have := hI.exact i hi
    by_cases hjv : obj.getD i 0 ∈ s.visited
    · have hr := (Inv.reached_placed hi s.visited).2 hjv
      simp only [hr, hjv, ↓reduceIte]; linarith
    · have hr : ¬ reached obj obj.length s.visited i = true :=
        fun h => hjv ((Inv.reached_placed hi s.visited).1 h)
      simp only [hr, hjv, Bool.false_eq_true, ↓reduceIte]; linarith
  case nonpos =>
    intro j hj
    rw [update_v hj]
    have := hI.nonpos j hj
    split_ifs with hjv
    · have := hδpos (List.ne_nil_of_mem hjv); linarith
    · linarith
  case free =>
    intro j hj hjo
    have hjv : j ∉ s.visited := fun h => hjo (hI.held j h)
    rw [update_v hj, ite_no hjv, hI.free j hj hjo]; simp
  case below =>
    intro j hj hjv r hr
    rw [update_visited] at hjv hr
    rw [update_best hj, update_changed (hI.reached_lt hr) hj, ite_no hjv, ite_yes hr, ite_no hjv]
    linarith [hI.below j hj hjv r hr]
  case via =>
    intro j hj hjv
    exact hI.viaReached j hj hjv
  case bestEq =>
    intro j hj hjv
    rw [update_visited] at hjv
    have hr := hI.viaReached j hj hjv
    rw [update_via, update_best hj, update_changed (hI.reached_lt hr) hj, ite_no hjv, ite_yes hr,
      ite_no hjv, hI.bestEq j hj hjv]
    ring
  case curFit =>
    intro j hjv
    rw [update_visited] at hjv
    rw [update_u hI.short, update_v (hI.visited_lt hjv), ite_yes (Inv.cur_reached obj _),
      ite_yes hjv]
    linarith [hI.curFit j hjv]
  case tight =>
    intro j hjv
    rw [update_visited] at hjv
    have hr := hI.via_reached hjv
    rw [update_via, update_u (hI.reached_lt hr), update_v (hI.visited_lt hjv), ite_yes hr,
      ite_yes hjv]
    linarith [hI.tight j hjv]
  case zero =>
    rw [update_best hj₁, ite_no hv₁]; ring

/-! ## Visiting a held object -/

section visit

variable {P : Problem} {obj : List ℕ} {s : Search} {j₁ : ℕ}

theorem visit_visited : (visit P obj s j₁).visited = s.visited ++ [j₁] := rfl
theorem visit_u : (visit P obj s j₁).u = s.u := rfl
theorem visit_v : (visit P obj s j₁).v = s.v := rfl

theorem visit_best {j : ℕ} (h : j < P.n) : (visit P obj s j₁).best.at j =
    if improves P s (s.visited ++ [j₁]) (obj.idxOf j₁) j then
      changed P s.u s.v (obj.idxOf j₁) j else s.best.at j := at_build _ h

theorem visit_via {j : ℕ} (h : j < P.n) : (visit P obj s j₁).via.getD j 0 =
    if improves P s (s.visited ++ [j₁]) (obj.idxOf j₁) j then obj.idxOf j₁
    else s.via.getD j 0 := getD_build _ h

theorem improves_iff (vis : List ℕ) (i j : ℕ) :
    improves P s vis i j = true ↔ j ∉ vis ∧ changed P s.u s.v i j < s.best.at j := by
  simp [improves]

end visit

/-- The holder of a held object: a person placed, holding it. -/
theorem idxOf_spec {obj : List ℕ} {j : ℕ} (h : j ∈ obj) :
    obj.idxOf j < obj.length ∧ obj.getD (obj.idxOf j) 0 = j := by
  have hl := List.idxOf_lt_length_iff.2 h
  exact ⟨hl, by rw [getD_of_lt hl]; exact List.getElem_idxOf hl⟩

/-- The persons reached after visiting `j₁`: those reached before, and the holder of `j₁`. -/
theorem reached_visit {obj : List ℕ} (hnd : obj.Nodup) {vis : List ℕ} {j₁ : ℕ} (h : j₁ ∈ obj)
    (r : ℕ) : reached obj obj.length (vis ++ [j₁]) r = true ↔
      reached obj obj.length vis r = true ∨ r = obj.idxOf j₁ := by
  obtain ⟨hl, he⟩ := idxOf_spec h
  simp only [reached_iff, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | ⟨h1, h2 | h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · refine Or.inr ?_
      rw [← he, getD_of_lt h1, getD_of_lt hl] at h2
      exact (hnd.getElem_inj_iff).1 h2
  · rintro ((h | ⟨h1, h2⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨hl, Or.inr he⟩

/-- **Visiting a held object keeps the invariants**, after the labels moved by its pick. -/
theorem visit_inv {P : Problem} {obj : List ℕ} {s : Search} {j₁ : ℕ} (hI : Inv P obj s)
    (hpos : ∀ j < P.n, j ∉ s.visited → 0 ≤ s.best.at j) (hj₁ : j₁ < P.n)
    (hv₁ : j₁ ∉ s.visited) (hzero : s.best.at j₁ = 0) (hheld : j₁ ∈ obj) :
    Inv P obj (visit P obj s j₁) := by
  obtain ⟨hil, hie⟩ := idxOf_spec hheld
  set i₁ := obj.idxOf j₁ with hi₁
  have hR := reached_visit (vis := s.visited) hI.assign.2 hheld
  have hi₁r : reached obj obj.length (s.visited ++ [j₁]) i₁ = true := (hR i₁).2 (Or.inr rfl)
  have hnv : ∀ j, j ∉ s.visited ++ [j₁] → j ∉ s.visited :=
    fun j h h' => h (List.mem_append_left _ h')
  refine ⟨hI.assign, hI.short, ?nodup, ?held, hI.fit, hI.exact, hI.nonpos, hI.free, ?below, ?via,
    ?bestEq, ?curFit, ?bestNonneg, ?tight, ?chain⟩
  case nodup =>
    rw [visit_visited, List.nodup_append]
    refine ⟨hI.nodup, List.nodup_singleton _, ?_⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    exact hv₁ ha
  case held =>
    intro j hj
    rw [visit_visited, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact hI.held j hj
    · exact hheld
  case below =>
    intro j hj hjv r hr
    rw [visit_visited] at hjv hr
    rw [visit_best hj, visit_u, visit_v]
    have hjv' := hnv j hjv
    by_cases himp : improves P s (s.visited ++ [j₁]) i₁ j = true
    · rw [ite_yes himp]
      have hlt := ((improves_iff _ _ _).1 himp).2
      rcases (hR r).1 hr with hr | rfl
      · linarith [hI.below j hj hjv' r hr]
      · exact le_rfl
    · rw [ite_no himp]
      rcases (hR r).1 hr with hr | rfl
      · exact hI.below j hj hjv' r hr
      · rw [improves_iff] at himp
        push Not at himp
        exact himp hjv
  case via =>
    intro j hj hjv
    rw [visit_visited] at hjv ⊢
    rw [visit_via hj]
    split_ifs
    · exact hi₁r
    · exact reached_mono _ (hI.viaReached j hj (hnv j hjv))
  case bestEq =>
    intro j hj hjv
    rw [visit_visited] at hjv
    rw [visit_best hj, visit_via hj, visit_u, visit_v]
    split_ifs
    · rfl
    · exact hI.bestEq j hj (hnv j hjv)
  case curFit =>
    intro j hj
    rw [visit_visited, List.mem_append, List.mem_singleton] at hj
    rw [visit_u, visit_v]
    rcases hj with hj | rfl
    · exact hI.curFit j hj
    · have := hI.below j hj₁ hv₁ _ (Inv.cur_reached obj _)
      simp only [changed] at this
      linarith
  case bestNonneg =>
    intro _ j hj hjv
    rw [visit_visited] at hjv
    rw [visit_best hj]
    split_ifs
    · have := hI.fit i₁ hil j hj
      simp only [changed]; linarith
    · exact hpos j hj (hnv j hjv)
  case tight =>
    intro j hj
    rw [visit_visited] at hj
    have hjn : j < P.n := by
      rcases List.mem_append.1 hj with h | h
      · exact hI.visited_lt h
      · rw [List.mem_singleton.1 h]; exact hj₁
    have hni : ¬ improves P s (s.visited ++ [j₁]) i₁ j = true := by
      rw [improves_iff]; exact fun h => h.1 hj
    rw [visit_via hjn, ite_no hni, visit_u, visit_v]
    rcases List.mem_append.1 hj with hj | hj
    · exact hI.tight j hj
    · rw [List.mem_singleton.1 hj]
      have := hI.bestEq j₁ hj₁ hv₁
      rw [hzero] at this
      simp only [changed] at this
      linarith
  case chain =>
    intro t ht
    simp only [visit_visited, List.length_append, List.length_singleton] at ht
    have hjn : ∀ j ∈ s.visited ++ [j₁], j < P.n := by
      intro j hj
      rcases List.mem_append.1 hj with h | h
      · exact hI.visited_lt h
      · rw [List.mem_singleton.1 h]; exact hj₁
    have hmem : (visit P obj s j₁).visited[t]'(by rw [visit_visited]; simpa using ht) ∈
        s.visited ++ [j₁] := List.getElem_mem _
    have hni : ¬ improves P s (s.visited ++ [j₁]) i₁
        ((visit P obj s j₁).visited[t]'(by rw [visit_visited]; simpa using ht)) = true := by
      rw [improves_iff]; exact fun h => h.1 hmem
    rw [visit_via (hjn _ hmem), ite_no hni]
    simp only [visit_visited]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [List.getElem_append_left ht, List.take_append_of_le_length ht.le]
      exact hI.chain t ht
    · rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, List.take_left']
      rcases (reached_iff ..).1 (hI.viaReached j₁ hj₁ hv₁) with h | h
      · exact Or.inl h
      · exact Or.inr h

/-! ## The search ends at a free object -/

/-- **What the search leaves**: its invariants, a free object `j` of the table, every pair of the
new person fitting, and `j` exact with its recorded person, who is reached. -/
structure Found (P : Problem) (obj : List ℕ) (s : Search) (j : ℕ) : Prop where
  inv : Inv P obj s
  lt : j < P.n
  notHeld : j ∉ obj
  curFit : ∀ j' < P.n, s.u.at obj.length + s.v.at j' ≤ P.costAt obj.length j'
  viaReached : reached obj obj.length s.visited (s.via.getD j 0) = true
  tight : s.u.at (s.via.getD j 0) + s.v.at j = P.costAt (s.via.getD j 0) j

/-- A table with more objects than people placed has a free object. -/
theorem exists_free {P : Problem} {obj : List ℕ} (h : obj.length < P.n) :
    ∃ x < P.n, x ∉ obj := by
  by_contra hc
  push Not at hc
  have := List.Nodup.length_le_of_subset (List.nodup_range (n := P.n))
    fun x hx => hc x (List.mem_range.1 hx)
  simp at this; omega

theorem visited_length_le {P : Problem} {obj : List ℕ} {s : Search} (hI : Inv P obj s) :
    s.visited.length ≤ obj.length :=
  List.Nodup.length_le_of_subset hI.nodup hI.held

/-- **The search's picks end at a free object** with enough fuel: each pick of a held object
visits one more of the held objects. -/
theorem searchLoop_spec {P : Problem} {obj : List ℕ} : ∀ (fuel : ℕ) (s : Search), Inv P obj s →
    obj.length < s.visited.length + fuel →
      ∃ s' j, searchLoop P obj obj.length fuel s = some (s', j) ∧ Found P obj s' j
  | 0, s, hI, hf => by have := visited_length_le hI; omega
  | fuel + 1, s, hI, hf => by
    obtain ⟨x, hx, hxo⟩ := exists_free hI.short
    have hxv : x ∉ s.visited := fun h => hxo (hI.held x h)
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (pick_isSome (obj := obj) hx hxv)
    obtain ⟨hjn, hjv, hmin⟩ := pick_spec hj
    obtain ⟨hI1, hpos, hzero⟩ := update_inv hI hjn hjv hmin
    simp only [searchLoop, hj]
    by_cases hjo : j ∈ obj
    · rw [ite_yes hjo]
      refine searchLoop_spec fuel _ (visit_inv hI1 hpos hjn hjv hzero hjo) ?_
      rw [visit_visited, List.length_append, update_visited]
      simp only [List.length_singleton]; omega
    · rw [ite_no hjo]
      refine ⟨_, j, rfl, hI1, hjn, hjo, ?_, hI1.viaReached j hjn hjv, ?_⟩
      · intro j' hj'
        by_cases hv : j' ∈ s.visited
        · exact hI1.curFit j' hv
        · have h1 := hI1.below j' hj' hv _ (Inv.cur_reached obj _)
          have h2 := hpos j' hj' hv
          simp only [changed] at h1
          linarith
      · have := hI1.bestEq j hjn hjv
        rw [hzero] at this
        simp only [changed] at this
        linarith

/-- **A state of the steps**: the people placed hold different objects; the labels fit every
pair of a person placed and are exact on their pairs; the object labels are at most 0, and 0 on
every free object. -/
structure Placed (st : State) : Prop where
  assign : IsAssignmentOf st.prob st.obj
  fit : ∀ i < st.obj.length, ∀ j < st.prob.n,
    st.personLabel.at i + st.objectLabel.at j ≤ st.prob.costAt i j
  exact : ∀ i < st.obj.length, st.personLabel.at i + st.objectLabel.at (st.obj.getD i 0) =
    st.prob.costAt i (st.obj.getD i 0)
  nonpos : ∀ j < st.prob.n, st.objectLabel.at j ≤ 0
  free : ∀ j < st.prob.n, j ∉ st.obj → st.objectLabel.at j = 0

/-- The search starts with its invariants: only the new person is reached, and every object's
best changed cost is the new person's. -/
theorem start_inv {st : State} (hst : Placed st) (hk : st.obj.length < st.prob.n) :
    Inv st.prob st.obj (startSearch st) := by
  have hR : ∀ r, reached st.obj st.obj.length [] r = true ↔ r = st.obj.length := by
    intro r; simp [reached_iff]
  have hv : (startSearch st).visited = [] := rfl
  refine ⟨hst.assign, hk, List.nodup_nil, by simp [hv], hst.fit, hst.exact, hst.nonpos, hst.free,
    ?_, ?_, ?_, by simp [hv], by simp [hv], by simp [hv], by simp [hv]⟩
  · intro j hj _ r hr
    rw [hv, hR r] at hr
    rw [hr]
    exact le_of_eq (at_build _ hj)
  · intro j hj _
    rw [hv, hR]
    exact getD_build _ hj
  · intro j hj _
    change Labels.at (build _ _) j = _
    rw [at_build _ hj]
    change _ = changed st.prob st.personLabel st.objectLabel ((build _ _).getD j 0) j
    rw [getD_build _ hj]

/-- **The per-pick search of a step ends at a free object** when someone is still to be placed. -/
theorem pickSearch_spec {st : State} (hst : Placed st) (hk : st.obj.length < st.prob.n) :
    ∃ s j, pickSearch st = some (s, j) ∧ Found st.prob st.obj s j :=
  searchLoop_spec _ _ (start_inv hst hk) (by change _ < 0 + _; omega)

end AlgoDesign.Flows.Assignment
