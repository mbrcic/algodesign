/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Check
public import Mathlib.Data.List.Sigma

/-!
# Strong components: the condensation

Source: Tarjan and Zwick, *Finding strong components using depth-first search*, European Journal
of Combinatorics 119 (2024), arXiv 2201.07197v3, §3.3, p. 10: "We use an extra bit per vertex,
initially false. … If the bit of y is false, we set it to true and add to the condensation an arc
from x to y. Once the component with leader x is constructed, we do a pass through the arcs out of
x in the condensation to reset to false the bits of the tips of these arcs."

`condensation g r` takes the groups in id order; for each, it walks its members' rows, member by
member, each row in its order, and emits an arrow to the head's group when that group is another
and its mark is clear, setting the mark; then a pass over the arrows just emitted clears their
marks. The graph of groups has one vertex per group.

[proved] `condensation_spec`: given the strong components' member lists (or any grouping whose
member lists agree with it), the condensation's arrows are exactly the derived graph of groups'
arrows (`quotient`), each once, none a loop.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

/-- Group `i`'s pass over the heads of its members' arrows: emit `(i, j)` for a head in another
group `j` whose mark is clear, and set the mark. The state is the marks and the arrows emitted
for this group so far. -/
def emit (c : List ℕ) (i : ℕ) : (ℕ → Bool) × List (ℕ × ℕ) → List ℕ → (ℕ → Bool) × List (ℕ × ℕ)
  | st, [] => st
  | (mark, fresh), w :: ws =>
    if gid c w ≠ i ∧ mark (gid c w) = false then
      emit c i (Function.update mark (gid c w) true, fresh ++ [(i, gid c w)]) ws
    else emit c i (mark, fresh) ws

/-- The reset pass: clear the mark of the head of each arrow emitted for the group. -/
def reset (mark : ℕ → Bool) (fresh : List (ℕ × ℕ)) : ℕ → Bool :=
  fresh.foldl (fun m a => Function.update m a.2 false) mark

/-- One group: its pass over its members' rows, then the reset; the marks after it, and every
arrow emitted so far. -/
def condenseGroup (g : Digraph) (c : List ℕ) (st : (ℕ → Bool) × List (ℕ × ℕ))
    (grp : List ℕ × ℕ) : (ℕ → Bool) × List (ℕ × ℕ) :=
  let r := emit c grp.2 (st.1, []) (grp.1.flatMap (forward g))
  (reset r.1 r.2, st.2 ++ r.2)

/-- **The condensation** (Tarjan–Zwick §3.3): one vertex per group, the arrows between groups
taken from the original arrows, each once. -/
def condensation (g : Digraph) (r : Components) : Digraph :=
  ⟨r.groups.length,
    (r.groups.zipIdx.foldl (condenseGroup g r.groupOf) (fun _ => false, [])).2⟩

/-! ## One group's pass -/

/-- During group `i`'s pass, a mark is set exactly for the groups an arrow has been emitted to. -/
def MarksEmitted (i : ℕ) (mark : ℕ → Bool) (fresh : List (ℕ × ℕ)) : Prop :=
  (∀ j, mark j = true ↔ (i, j) ∈ fresh) ∧ (∀ a ∈ fresh, a.1 = i ∧ a.2 ≠ i) ∧ fresh.Nodup

theorem emit_spec {c : List ℕ} {i : ℕ} :
    ∀ (ws : List ℕ) (mark : ℕ → Bool) (fresh : List (ℕ × ℕ)), MarksEmitted i mark fresh →
      MarksEmitted i (emit c i (mark, fresh) ws).1 (emit c i (mark, fresh) ws).2 ∧
        ∀ a, a ∈ (emit c i (mark, fresh) ws).2 ↔
          a ∈ fresh ∨ ∃ w ∈ ws, gid c w ≠ i ∧ a = (i, gid c w)
  | [], mark, fresh, h => ⟨h, fun a => by simp [emit]⟩
  | w :: ws, mark, fresh, h => by
    unfold emit
    split_ifs with hw
    · have h' : MarksEmitted i (Function.update mark (gid c w) true)
          (fresh ++ [(i, gid c w)]) := by
        refine ⟨fun j => ?_, fun a ha => ?_, ?_⟩
        · by_cases hj : j = gid c w
          · subst hj; simp
          · rw [Function.update_of_ne hj, h.1 j]
            simp [hj]
        · rcases List.mem_append.mp ha with ha | ha
          · exact h.2.1 a ha
          · simp only [List.mem_singleton] at ha
            subst ha
            exact ⟨rfl, hw.1⟩
        · refine List.nodup_append.mpr ⟨h.2.2, List.nodup_singleton _, ?_⟩
          intro a ha b hb hab
          simp only [List.mem_singleton] at hb
          subst hb hab
          have := (h.1 (gid c w)).mpr ha
          simp [hw.2] at this
      obtain ⟨hinv, hmem⟩ := emit_spec ws _ _ h'
      refine ⟨hinv, fun a => ?_⟩
      rw [hmem a]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((ha | rfl) | ⟨x, hx, hxi, rfl⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨w, Or.inl rfl, hw.1, rfl⟩
        · exact Or.inr ⟨x, Or.inr hx, hxi, rfl⟩
      · rintro (ha | ⟨x, rfl | hx, hxi, rfl⟩)
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr ⟨x, hx, hxi, rfl⟩
    · obtain ⟨hinv, hmem⟩ := emit_spec ws mark fresh h
      refine ⟨hinv, fun a => ?_⟩
      rw [hmem a]
      simp only [List.mem_cons]
      constructor
      · rintro (ha | ⟨x, hx, hxi, rfl⟩)
        · exact Or.inl ha
        · exact Or.inr ⟨x, Or.inr hx, hxi, rfl⟩
      · rintro (ha | ⟨x, rfl | hx, hxi, rfl⟩)
        · exact Or.inl ha
        · by_cases hm : mark (gid c x) = true
          · exact Or.inl ((h.1 _).mp hm)
          · exact absurd ⟨hxi, by simpa using hm⟩ hw
        · exact Or.inr ⟨x, hx, hxi, rfl⟩

/-- The reset pass clears exactly the marks of the heads it walks. -/
theorem reset_apply (mark : ℕ → Bool) :
    ∀ (fresh : List (ℕ × ℕ)) (j : ℕ), reset mark fresh j = (mark j && !(fresh.any (·.2 = j)))
  | [], j => by simp [reset]
  | a :: fresh, j => by
    simp only [reset, List.foldl_cons] at reset_apply ⊢
    rw [reset_apply (Function.update mark a.2 false) fresh j]
    by_cases h : j = a.2
    · subst h; simp
    · simp [Function.update_of_ne h, Ne.symm h]

/-- After a group's pass and the reset, every mark is clear again. -/
theorem reset_clear {i : ℕ} {mark : ℕ → Bool} {fresh : List (ℕ × ℕ)}
    (h : MarksEmitted i mark fresh) (j : ℕ) : reset mark fresh j = false := by
  rw [reset_apply]
  cases hm : mark j
  · rfl
  · have := (h.1 j).mp hm
    simp only [Bool.true_and, Bool.not_eq_false', List.any_eq_true, decide_eq_true_eq]
    exact ⟨_, this, rfl⟩

/-! ## The whole run -/

theorem foldl_condenseGroup {g : Digraph} {c : List ℕ} :
    ∀ (L : List (List ℕ × ℕ)) (mark : ℕ → Bool) (out : List (ℕ × ℕ)),
      (L.map Prod.snd).Nodup → (∀ j, mark j = false) → out.Nodup →
      (∀ a ∈ out, a.1 ∉ L.map Prod.snd) →
      let res := L.foldl (condenseGroup g c) (mark, out)
      (∀ j, res.1 j = false) ∧ res.2.Nodup ∧
        ∀ a, a ∈ res.2 ↔ a ∈ out ∨
          ∃ p ∈ L, ∃ v ∈ p.1, ∃ w ∈ forward g v, gid c w ≠ p.2 ∧ a = (p.2, gid c w)
  | [], mark, out, _, hm, hn, _ => ⟨hm, hn, fun a => by simp⟩
  | p :: L, mark, out, hL, hm, hn, hout => by
    simp only [List.foldl_cons]
    have hstart : MarksEmitted p.2 mark [] := ⟨fun j => by simp [hm j], by simp, by simp⟩
    obtain ⟨hinv, hmem⟩ := emit_spec (c := c) (p.1.flatMap (forward g)) mark [] hstart
    set r := emit c p.2 (mark, []) (p.1.flatMap (forward g)) with hr
    rw [List.map_cons] at hL
    have hL' := (List.nodup_cons.mp hL).2
    have hpL : p.2 ∉ L.map Prod.snd := (List.nodup_cons.mp hL).1
    have hn' : (out ++ r.2).Nodup := by
      refine List.nodup_append.mpr ⟨hn, hinv.2.2, ?_⟩
      intro a ha b hb hab
      subst hab
      exact hout a ha (by simp [(hinv.2.1 a hb).1])
    have hout' : ∀ a ∈ out ++ r.2, a.1 ∉ L.map Prod.snd := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact fun h => hout a ha (by simp_all)
      · rw [(hinv.2.1 a ha).1]; exact hpL
    obtain ⟨h1, h2, h3⟩ := foldl_condenseGroup L (reset r.1 r.2) (out ++ r.2) hL'
      (reset_clear hinv) hn' hout'
    refine ⟨h1, h2, fun a => ?_⟩
    simp only [condenseGroup] at h3 ⊢
    rw [← hr, h3 a, List.mem_append, hmem a]
    simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_cons]
    constructor
    · rintro ((ha | ⟨w, ⟨v, hv, hw⟩, hwi, rfl⟩) | ⟨q, hq, v, hv, w, hw, hwi, rfl⟩)
      · exact Or.inl ha
      · exact Or.inr ⟨p, Or.inl rfl, v, hv, w, hw, hwi, rfl⟩
      · exact Or.inr ⟨q, Or.inr hq, v, hv, w, hw, hwi, rfl⟩
    · rintro (ha | ⟨q, rfl | hq, v, hv, w, hw, hwi, rfl⟩)
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ⟨w, ⟨v, hv, hw⟩, hwi, rfl⟩)
      · exact Or.inr ⟨q, hq, v, hv, w, hw, hwi, rfl⟩

/-- **The condensation is the graph of groups** (Tarjan–Zwick §3.3): on a well-formed graph,
given member lists that agree with the grouping, it has one vertex per group, and its arrows are
exactly the derived graph of groups' arrows, each once; none is a loop. -/
theorem condensation_spec {g : Digraph} {r : Components} (hg : g.WellFormed)
    (hc : r.groupOf.length = g.n) (hr : MembersAgree g r) :
    (condensation g r).n = numGroups r.groupOf ∧ (condensation g r).arrows.Nodup ∧
      ∀ a, a ∈ (condensation g r).arrows ↔ a ∈ (quotient g r.groupOf).arrows := by
  have hL : (r.groups.zipIdx.map Prod.snd).Nodup := List.nodup_zipIdx_map_snd _
  obtain ⟨-, h2, h3⟩ := foldl_condenseGroup (g := g) (c := r.groupOf) r.groups.zipIdx
    (fun _ => false) [] hL (fun _ => rfl) List.nodup_nil (by simp)
  refine ⟨hr.1, h2, fun a => ?_⟩
  simp only [condensation]
  rw [h3 a, mem_quotient_arrows]
  simp only [List.not_mem_nil, false_or]
  constructor
  · rintro ⟨p, hp, v, hv, w, hw, hwi, rfl⟩
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hp)
    have hvi := ((hr.2.1 p.2 hlt).2 v (hget ▸ hv)).2
    exact ⟨v, w, (mem_forward.mp hw).2, by rw [hvi]; exact Ne.symm hwi, by rw [hvi]⟩
  · rintro ⟨x, y, hxy, hne, rfl⟩
    have hx := (hg _ hxy).1
    have hy := (hg _ hxy).2
    have hlt : gid r.groupOf x < r.groups.length := hr.1 ▸ gid_lt (hc ▸ hx)
    refine ⟨(r.groups[gid r.groupOf x], gid r.groupOf x), ?_, x, ?_, y,
      mem_forward.mpr ⟨hy, hxy⟩, Ne.symm hne, rfl⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hlt)
    · have := hr.2.2 x hx
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at this

end AlgoDesign.Graphs.Scc
