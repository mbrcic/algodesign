/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.SearchKeeps

/-!
# Assignment: the walk back

The walk back starts at the free object the search ended at; the new person's place holds `n`,
no object. Each move gives the current object to its recorded person, whose old object is free
now and is the next; the objects stay different. Every object a person takes is exact with them,
so after the walk the labels are exact on every chosen pair (`walk_spec`). Each person moved
holds an object visited before the current one, so the walk ends at the new person.
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-! ## Lists read and changed by place -/

theorem getD_set {o : List ℕ} {p i x : ℕ} (hp : p < o.length) :
    (o.set p x).getD i 0 = if p = i then x else o.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> rfl

theorem mem_iff_getD {o : List ℕ} {x : ℕ} : x ∈ o ↔ ∃ i < o.length, o.getD i 0 = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, getD_of_lt hi⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, (getD_of_lt hi).symm⟩

theorem getD_inj {o : List ℕ} (h : o.Nodup) {i i' : ℕ} (hi : i < o.length)
    (hi' : i' < o.length) (e : o.getD i 0 = o.getD i' 0) : i = i' := by
  rw [getD_of_lt hi, getD_of_lt hi'] at e
  exact (h.getElem_inj_iff).1 e

theorem mem_set_iff {o : List ℕ} {p x y : ℕ} (hp : p < o.length) :
    y ∈ o.set p x ↔ ∃ i < o.length, (if p = i then x else o.getD i 0) = y := by
  rw [mem_iff_getD, List.length_set]
  simp only [getD_set hp]

/-! ## What the walk keeps -/

/-- **The walk's state**: the objects `o` of the people, the new person's place `k` still holding
`n`; the current object `j`, free, exact with its recorded person, who is the new person or the
holder of an object visited among the first `b`; the holders of those objects not moved yet; every
object held before held still, or `j`. -/
structure WalkInv (P : Problem) (obj : List ℕ) (s : Search) (o : List ℕ) (j b : ℕ) : Prop where
  len : o.length = obj.length + 1
  nodup : o.Nodup
  le : ∀ x ∈ o, x ≤ P.n
  curSlot : o.getD obj.length 0 = P.n
  exact : ∀ i < obj.length + 1, o.getD i 0 ≠ P.n →
    s.u.at i + s.v.at (o.getD i 0) = P.costAt i (o.getD i 0)
  jlt : j < P.n
  jnot : j ∉ o
  jtight : s.u.at (s.via.getD j 0) + s.v.at j = P.costAt (s.via.getD j 0) j
  jvia : s.via.getD j 0 = obj.length ∨
    (s.via.getD j 0 < obj.length ∧ obj.getD (s.via.getD j 0) 0 ∈ s.visited.take b)
  same : ∀ i < obj.length, obj.getD i 0 ∈ s.visited.take b → o.getD i 0 = obj.getD i 0
  keep : ∀ x ∈ obj, x ∈ o ∨ x = j

/-- **What the walk gives**: one different object of the table for every person, the new one
included, each exact with its person, and every object held before still held. -/
structure WalkDone (P : Problem) (obj : List ℕ) (s : Search) (o : List ℕ) : Prop where
  len : o.length = obj.length + 1
  assign : IsAssignmentOf P o
  exact : ∀ i < obj.length + 1, s.u.at i + s.v.at (o.getD i 0) = P.costAt i (o.getD i 0)
  keep : ∀ x ∈ obj, x ∈ o

/-- The place holding `n` is the new person's. -/
theorem WalkInv.ne_n {P : Problem} {obj : List ℕ} {s : Search} {o : List ℕ} {j b : ℕ}
    (W : WalkInv P obj s o j b) {i : ℕ} (hi : i < o.length) (hik : i ≠ obj.length) :
    o.getD i 0 ≠ P.n := by
  intro h
  rw [← W.curSlot] at h
  exact hik (getD_inj W.nodup hi (by rw [W.len]; omega) h)

theorem walkBack_spec {P : Problem} {obj : List ℕ} {s : Search} (hI : Inv P obj s) :
    ∀ (fuel : ℕ) (o : List ℕ) (j b : ℕ), WalkInv P obj s o j b → b < fuel →
      WalkDone P obj s (walkBack obj.length s.via fuel o j).1
  | 0, _, _, _, _, hb => absurd hb (Nat.not_lt_zero _)
  | fuel + 1, o, j, b, W, hb => by
    have hkl : obj.length < o.length := by rw [W.len]; omega
    simp only [walkBack]
    split_ifs with hp
    · -- the new person takes `j`
      have hpl : s.via.getD j 0 < o.length := by rw [hp]; exact hkl
      refine ⟨by rw [List.length_set, W.len], ⟨?_, W.nodup.set W.jnot⟩, ?_, ?_⟩
      · intro y hy
        obtain ⟨i, hi, rfl⟩ := (mem_set_iff hpl).1 hy
        split_ifs with hpi
        · exact W.jlt
        · exact lt_of_le_of_ne (W.le _ (getD_mem hi)) (W.ne_n hi (by omega))
      · intro i hi
        rw [getD_set hpl]
        split_ifs with hpi
        · rw [← hpi]; exact W.jtight
        · exact W.exact i hi (W.ne_n (by rw [W.len]; exact hi) (by omega))
      · intro x hx
        rcases W.keep x hx with hx' | rfl
        · obtain ⟨i, hi, rfl⟩ := mem_iff_getD.1 hx'
          refine (mem_set_iff hpl).2 ⟨i, hi, ?_⟩
          rw [ite_no]
          intro hpi
          have := hI.assign.1 _ hx
          rw [← hpi, hp, W.curSlot] at this
          omega
        · exact (mem_set_iff hpl).2 ⟨_, hpl, ite_yes rfl⟩
    · -- a person placed moves to `j`; their old object is next
      obtain ⟨hpk, hpv⟩ := W.jvia.resolve_left hp
      set p := s.via.getD j 0 with hpdef
      have hpl : p < o.length := by rw [W.len]; omega
      obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.1 hpv
      rw [List.getElem_take] at hte
      have htb : t < b := by simp at ht; omega
      have htv : t < s.visited.length := by simp at ht; omega
      have hop : o.getD p 0 = s.visited[t] := by
        rw [W.same p hpk hpv, ← hte]
      have hjv : s.visited[t] ∈ s.visited := List.getElem_mem htv
      have hnotTake : ∀ i < obj.length, obj.getD i 0 ∈ s.visited.take t → i ≠ p := by
        intro i _ hi hip
        rw [hip, ← hte] at hi
        obtain ⟨t', ht', he⟩ := List.mem_iff_getElem.1 hi
        rw [List.getElem_take] at he
        have := (hI.nodup.getElem_inj_iff).1 he
        simp at ht'; omega
      refine walkBack_spec hI fuel _ _ t ⟨?_, W.nodup.set W.jnot, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩ (by omega)
      · rw [List.length_set, W.len]
      · intro y hy
        obtain ⟨i, hi, rfl⟩ := (mem_set_iff hpl).1 hy
        split_ifs
        · exact W.jlt.le
        · exact W.le _ (getD_mem hi)
      · rw [getD_set hpl, ite_no (by omega)]; exact W.curSlot
      · intro i hi
        rw [getD_set hpl]
        split_ifs with hpi
        · intro _; rw [← hpi]; exact W.jtight
        · exact W.exact i hi
      · rw [hop]; exact hI.visited_lt hjv
      · rw [hop]
        intro hm
        obtain ⟨i, hi, he⟩ := (mem_set_iff hpl).1 hm
        split_ifs at he with hpi
        · exact W.jnot (he ▸ hop ▸ getD_mem hpl)
        · rw [← hop] at he
          exact hpi (getD_inj W.nodup hpl hi he.symm)
      · rw [hop]; exact hI.tight _ hjv
      · rw [hop]; exact hI.chain t htv
      · intro i hi hit
        rw [getD_set hpl, ite_no (Ne.symm (hnotTake i hi hit))]
        exact W.same i hi (List.take_subset_take_left _ htb.le hit)
      · intro x hx
        rcases W.keep x hx with hx' | rfl
        · obtain ⟨i, hi, rfl⟩ := mem_iff_getD.1 hx'
          by_cases hpi : p = i
          · right; rw [← hpi, hop]
          · left; exact (mem_set_iff hpl).2 ⟨i, hi, ite_no hpi⟩
        · left; exact (mem_set_iff hpl).2 ⟨_, hpl, ite_yes rfl⟩

/-- **The walk back gives every person a different object, each exact with its person**, after
a search that found a free object. -/
theorem walk_spec {P : Problem} {obj : List ℕ} {s : Search} {j : ℕ} (hF : Found P obj s j) :
    WalkDone P obj s (walkBack obj.length s.via (obj.length + 1) (obj ++ [P.n]) j).1 := by
  have hI := hF.inv
  have hnot : P.n ∉ obj := fun h => by have := hI.assign.1 _ h; omega
  have hget : ∀ i < obj.length, (obj ++ [P.n]).getD i 0 = obj.getD i 0 := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  refine walkBack_spec hI _ _ j s.visited.length ⟨by simp, ?_, ?_, ?_, ?_, hF.lt, ?_, hF.tight, ?_,
    ?_, ?_⟩ (by have := visited_length_le hI; omega)
  · rw [List.nodup_append]
    refine ⟨hI.assign.2, List.nodup_singleton _, ?_⟩
    simp only [List.mem_singleton]
    rintro a ha b rfl rfl
    exact hnot ha
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact (hI.assign.1 x h).le
    · rw [List.mem_singleton.1 h]
  · simp [List.getD_eq_getElem?_getD]
  · intro i hi hn
    have hik : i < obj.length := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h
      · simp [List.getD_eq_getElem?_getD] at hn
    rw [hget i hik]
    exact hI.exact i hik
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact hF.notHeld h
    · have := hF.lt; rw [List.mem_singleton.1 h] at this; omega
  · rw [List.take_length]
    exact (reached_iff ..).1 hF.viaReached
  · intro i hi _
    exact hget i hi
  · intro x hx
    exact Or.inl (List.mem_append_left _ hx)

end AlgoDesign.Flows.Assignment
