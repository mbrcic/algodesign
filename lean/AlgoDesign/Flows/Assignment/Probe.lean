/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.SearchKeeps

/-!
# Assignment: the search the library runs is the per-pick search

`search` keeps the labels fixed while it runs and moves them once at the end (`settle`);
`pickSearch` moves them after every pick (`update`). The two pick the same objects, record the
same persons, and end with the same labels (`search_agrees`).

The reason, step by step: let `D` be the distance of the last pick, which is the sum of the values
the per-pick search has added so far. Then the per-pick search's best changed cost of an object not
visited is the distance less `D`; its label of the new person is the start label plus `D`; its label
of the holder of a visited object `k` is the start label plus `D` less `k`'s distance; and its
label of a visited object `k` is the start label less `D` less `k`'s distance (`Agree`). Both
searches then order the objects not visited alike, so they pick alike; a held object brings the
same objects
closer in both, by the same amounts less `D`; and at the free object, whose distance is the new
`D`, the per-pick search's labels are the settled ones.
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-- **The per-pick search `o` and the search `s` agree**, `D` the distance of the last pick:
the same objects visited and persons recorded, and `o`'s values those of `s` moved by `D`. -/
structure Agree (P : Problem) (obj : List ℕ) (D : ℤ) (o s : Search) : Prop where
  visited : o.visited = s.visited
  via : o.via = s.via
  lt : ∀ k ∈ s.visited, k < P.n
  best : ∀ k < P.n, k ∉ s.visited → o.best.at k = s.best.at k - D
  u : ∀ r < P.n, o.u.at r = s.u.at r +
      if r = obj.length then D
      else if reached obj obj.length s.visited r then D - s.best.at (obj.getD r 0) else 0
  v : ∀ k < P.n, o.v.at k = s.v.at k - if k ∈ s.visited then D - s.best.at k else 0

/-- Two lists of `n` entries built from functions that agree below `n` are equal. -/
theorem build_congr {α : Type} {n : ℕ} {f g : ℕ → α} (h : ∀ i < n, f i = g i) :
    build n f = build n g := by
  unfold build
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

/-- The per-pick search's order of the objects not visited is the search's. -/
theorem before_agree {P : Problem} {obj : List ℕ} {D : ℤ} {o s : Search}
    (A : Agree P obj D o s) {j b : ℕ} (hj : j < P.n) (hjv : j ∉ s.visited) (hb : b < P.n)
    (hbv : b ∉ s.visited) : before obj o j b = before obj s j b := by
  unfold before
  rw [A.best j hj hjv, A.best b hb hbv]
  have h1 : s.best.at j - D < s.best.at b - D ↔ s.best.at j < s.best.at b := by
    constructor <;> intro h <;> linarith
  have h2 : s.best.at j - D = s.best.at b - D ↔ s.best.at j = s.best.at b := by
    constructor <;> intro h <;> linarith
  simp only [h1, h2]

/-- The two searches' scans over candidates not visited agree. -/
theorem pickFrom_agree {P : Problem} {obj : List ℕ} {D : ℤ} {o s : Search}
    (A : Agree P obj D o s) : ∀ (cands : List ℕ) (acc : Option ℕ),
      (∀ j ∈ cands, j < P.n ∧ j ∉ s.visited) →
      (∀ b, acc = some b → b < P.n ∧ b ∉ s.visited) →
      pickFrom obj o cands acc = pickFrom obj s cands acc
  | [], acc, _, _ => rfl
  | j :: js, none, hc, _ => by
    simp only [pickFrom]
    refine pickFrom_agree A js (some j) (fun x hx => hc x (List.mem_cons_of_mem _ hx)) ?_
    rintro b ⟨⟩
    exact hc j List.mem_cons_self
  | j :: js, some b, hc, ha => by
    simp only [pickFrom]
    obtain ⟨hj, hjv⟩ := hc j List.mem_cons_self
    obtain ⟨hb, hbv⟩ := ha b rfl
    rw [before_agree A hj hjv hb hbv]
    refine pickFrom_agree A js _ (fun x hx => hc x (List.mem_cons_of_mem _ hx)) ?_
    rintro c hc'
    split at hc'
    · cases hc'; exact ⟨hj, hjv⟩
    · cases hc'; exact ⟨hb, hbv⟩

/-- **The two searches pick alike.** -/
theorem pick_agree {P : Problem} {obj : List ℕ} {D : ℤ} {o s : Search}
    (A : Agree P obj D o s) : pick P obj o = pick P obj s := by
  unfold pick
  rw [A.visited]
  refine pickFrom_agree A _ none (fun j hj => ?_) (by simp)
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
  exact hj

/-- What both searches end with: the labels, the persons recorded, the objects visited, and the
free object. -/
def key (x : Search × ℕ) : Labels × Labels × List ℕ × List ℕ × ℕ :=
  (x.1.u, x.1.v, x.1.via, x.1.visited, x.2)

/-- At the free object `j`, the per-pick search's labels after its last pick are the settled
ones. -/
theorem settle_agree {P : Problem} {obj : List ℕ} {D : ℤ} {o s : Search}
    (A : Agree P obj D o s) {j : ℕ} (hj : j < P.n) (hjv : j ∉ s.visited) :
    key (update P obj obj.length o (o.best.at j), j) = key (settle P obj obj.length s j, j) := by
  have hδ := A.best j hj hjv
  simp only [key, update, settle, Prod.mk.injEq, A.via, A.visited, and_true]
  constructor
  · refine build_congr fun r hr => ?_
    rw [A.u r hr, hδ]
    by_cases hc : r = obj.length
    · have hre : reached obj obj.length s.visited r = true := by
        rw [reached_iff]; exact Or.inl hc
      simp only [ite_eq_left hc, ite_eq_left hre]; ring
    · by_cases hre : reached obj obj.length s.visited r = true
      · simp only [ite_eq_right hc, ite_eq_left hre]; ring
      · simp only [ite_eq_right hc, ite_eq_right hre]; ring
  · refine build_congr fun k hk => ?_
    rw [A.v k hk, hδ]
    by_cases hkv : k ∈ s.visited
    · simp only [ite_eq_left hkv]; ring
    · simp only [ite_eq_right hkv]; ring

/-- An object already visited does not come closer. -/
theorem closer_visited {P : Problem} {s : Search} {vis : List ℕ} {j₁ i₁ k : ℕ} (h : k ∈ vis) :
    closer P s vis j₁ i₁ k = false := by
  simp [closer, h]

/-- A visit leaves the distance of an object already visited as it was. -/
theorem probeVisit_best_visited {P : Problem} {s : Search} {vis : List ℕ} {j₁ i₁ k : ℕ}
    (hk : k < P.n) (h : k ∈ vis) :
    Labels.at (build P.n fun x => if closer P s vis j₁ i₁ x then
      s.best.at j₁ + changed P s.u s.v i₁ x else s.best.at x) k = s.best.at k := by
  rw [at_build _ hk, closer_visited h]
  rfl

/-- After a held object `j` is picked and visited, the two searches agree at its distance. -/
theorem visit_agree {P : Problem} {obj : List ℕ} {D : ℤ} {o s : Search}
    (A : Agree P obj D o s) (hk : obj.length < P.n) {j : ℕ} (hj : j < P.n) (hjv : j ∉ s.visited)
    (hjo : j ∈ obj) :
    Agree P obj (s.best.at j) (visit P obj (update P obj obj.length o (o.best.at j)) j)
      (probeVisit P obj s j) := by
  have hδ := A.best j hj hjv
  obtain ⟨hi1, hgj⟩ := idxOf_spec hjo
  set i₁ := obj.idxOf j with hi
  set o' := update P obj obj.length o (o.best.at j) with ho'
  -- the holder of `j` is not yet reached, so its label is unmoved; likewise the objects not visited
  have hi1n : i₁ < P.n := by omega
  have hnr : reached obj obj.length s.visited i₁ = false := by
    rw [Bool.eq_false_iff, Ne, reached_iff]
    rintro (h | ⟨-, h⟩)
    · omega
    · exact hjv (hgj ▸ h)
  have hu1 : o'.u.at i₁ = s.u.at i₁ := by
    rw [ho', update_u hi1n, A.visited, hnr, A.u i₁ hi1n, hnr]
    simp [show i₁ ≠ obj.length by omega]
  have hvk : ∀ k < P.n, k ∉ s.visited → o'.v.at k = s.v.at k := by
    intro k hk' hkv
    rw [ho', update_v hk', A.visited, A.v k hk']
    simp [hkv]
  have hbk : ∀ k < P.n, k ∉ s.visited → o'.best.at k = s.best.at k - s.best.at j := by
    intro k hk' hkv
    rw [ho', update_best hk', A.visited, A.best k hk' hkv, hδ]
    simp only [ite_eq_right hkv]; ring
  -- the two visits bring the same objects closer
  have himp : ∀ k < P.n, improves P o' (s.visited ++ [j]) i₁ k =
      closer P s (s.visited ++ [j]) j i₁ k := by
    intro k hk'
    unfold improves closer
    by_cases hkv : k ∈ s.visited ++ [j]
    · simp [hkv]
    · have hkv' : k ∉ s.visited := fun h => hkv (List.mem_append_left _ h)
      simp only [hkv, not_false_eq_true, decide_true, Bool.true_and, decide_eq_decide]
      unfold changed
      rw [hu1, hvk k hk' hkv', hbk k hk' hkv']
      constructor <;> intro h <;> linarith
  have hvis : (visit P obj o' j).visited = (probeVisit P obj s j).visited := by
    simp [visit, probeVisit, ho', update, A.visited]
  refine ⟨hvis, ?_, ?_, ?_, ?_, ?_⟩
  · -- the persons recorded
    simp only [visit, probeVisit]
    refine build_congr fun k hk' => ?_
    rw [show (update P obj obj.length o (o.best.at j)).visited = s.visited from A.visited]
    rw [himp k hk', show (update P obj obj.length o (o.best.at j)).via = s.via from A.via]
  · intro k hkv
    simp only [probeVisit, List.mem_append, List.mem_singleton] at hkv
    rcases hkv with h | rfl
    · exact A.lt k h
    · exact hj
  · intro k hk' hkv
    simp only [probeVisit, List.mem_append, List.mem_singleton, not_or] at hkv
    rw [visit_best hk']
    simp only [probeVisit]
    rw [at_build _ hk', show o'.visited = s.visited from A.visited, himp k hk']
    have hkv' : k ∉ s.visited ++ [j] := by simp [hkv.1, hkv.2]
    split
    · unfold changed; rw [hu1, hvk k hk' hkv.1, ← hi]; ring
    · rw [hbk k hk' hkv.1]
  · intro r hr
    rw [visit_u, ho', update_u hr, A.visited, A.u r hr, hδ]
    simp only [probeVisit, ← hi]
    by_cases hc : r = obj.length
    · have hre : reached obj obj.length s.visited r = true := by
        rw [reached_iff]; exact Or.inl hc
      simp only [ite_eq_left hc, ite_eq_left hre]; ring
    · by_cases hre : reached obj obj.length s.visited r = true
      · have hre' := reached_mono j hre
        have hlt : r < obj.length ∧ obj.getD r 0 ∈ s.visited := by
          rcases (reached_iff ..).1 hre with h | h
          · exact absurd h hc
          · exact h
        rw [ite_eq_right hc, ite_eq_left hre, ite_eq_left hre, ite_eq_right hc, ite_eq_left hre',
          probeVisit_best_visited (A.lt _ hlt.2) (List.mem_append_left _ hlt.2)]
        ring
      · by_cases hre' : reached obj obj.length (s.visited ++ [j]) r = true
        · -- the holder of `j`, reached by this visit: its label is unmoved, and `j`'s distance is
          -- the new `D`
          have hlt : r < obj.length ∧ obj.getD r 0 = j := by
            rcases (reached_iff ..).1 hre' with h | ⟨h1, h2⟩
            · exact absurd h hc
            · simp only [List.mem_append, List.mem_singleton] at h2
              rcases h2 with h2 | h2
              · exact absurd ((reached_iff ..).2 (Or.inr ⟨h1, h2⟩)) hre
              · exact ⟨h1, h2⟩
          rw [ite_eq_right hc, ite_eq_right hre, ite_eq_right hre, ite_eq_right hc,
            ite_eq_left hre', hlt.2,
            probeVisit_best_visited hj (by simp)]
          ring
        · rw [ite_eq_right hc, ite_eq_right hre, ite_eq_right hre, ite_eq_right hc,
            ite_eq_right hre']
          ring
  · intro k hk'
    rw [visit_v, ho', update_v hk', A.visited, A.v k hk', hδ]
    simp only [probeVisit, ← hi]
    by_cases hkv : k ∈ s.visited
    · have hkv' : k ∈ s.visited ++ [j] := List.mem_append_left _ hkv
      rw [ite_eq_left hkv, ite_eq_left hkv, ite_eq_left hkv',
        probeVisit_best_visited hk' hkv']
      ring
    · by_cases hkj : k = j
      · subst hkj
        have hkv' : k ∈ s.visited ++ [k] := by simp
        rw [ite_eq_right hkv, ite_eq_right hkv, ite_eq_left hkv',
          probeVisit_best_visited hk' hkv']
        ring
      · have hkv' : k ∉ s.visited ++ [j] := by simp [hkv, hkj]
        rw [ite_eq_right hkv, ite_eq_right hkv, ite_eq_right hkv']
        ring

/-- **The two loops end alike**, from searches that agree. -/
theorem loop_agree {P : Problem} {obj : List ℕ} (hk : obj.length < P.n) :
    ∀ (fuel : ℕ) (D : ℤ) (o s : Search), Agree P obj D o s →
      (searchLoop P obj obj.length fuel o).map key =
        (probeLoop P obj obj.length fuel s).map key
  | 0, _, _, _, _ => rfl
  | fuel + 1, D, o, s, A => by
    simp only [searchLoop, probeLoop, pick_agree A]
    cases hp : pick P obj s with
    | none => rfl
    | some j =>
      obtain ⟨hj, hjv, -⟩ := pick_spec hp
      simp only
      by_cases hjo : j ∈ obj
      · simp only [hjo, ite_true]
        exact loop_agree hk fuel _ _ _ (visit_agree A hk hj hjv hjo)
      · simp only [hjo, ite_false, Option.map_some]
        exact congrArg some (settle_agree A hj hjv)

/-- **The search the library runs ends as the per-pick search does**: the same labels, persons
recorded, objects visited and free object. -/
theorem search_agrees (st : State) (hk : st.obj.length < st.prob.n) :
    (search st).map key = (pickSearch st).map key := by
  refine (loop_agree hk _ 0 _ _ ⟨rfl, rfl, by simp [startSearch], fun k _ _ => by ring,
    fun r _ => ?_, fun k _ => by simp [startSearch]⟩).symm
  by_cases h : r = st.obj.length
  · rw [ite_eq_left h]; ring
  · have hre : ¬ reached st.obj st.obj.length [] r = true := by
      rw [reached_iff]; simp [h]
    rw [ite_eq_right h]
    change _ = _ + if reached st.obj st.obj.length [] r = true then _ else _
    rw [ite_eq_right hre]; ring

end AlgoDesign.Flows.Assignment
