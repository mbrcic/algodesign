/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie.Basic

/-!
# Trie: insertion
`insert` edits one child per level through `updateChild`: after inserting `a` at `k`, `k` maps to
`a` and every other key to what it did before (`get_insert`, `get_insert_other`, `insertSpec`),
and `DistinctLetters` and `NoDeadBranches` are kept (`distinctLetters_insert`,
`noDeadBranches_insert`), so `Valid` is (`valid_insert`, from `valid_empty`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Trie

/-- **What any insertion owes**: afterwards `k` maps to `a` and every other key maps to what it did
before. -/
def InsertSpec {α : Type} (k : List Nat) (a : α) (before after : Trie α) : Prop :=
  ∀ k', Trie.get after k' = if k' = k then some a else Trie.get before k'

/-- Replace the child filed under symbol `c` by `f` applied to it, leaving every other child
alone. Written as an explicit walk rather than a `map` with an `if`, so that looking `c` up in the
result is a one-line induction — see `find?_updateChild`. -/
def updateChild {α : Type} (c : Nat) (f : Trie α → Trie α) :
    List (Nat × Trie α) → List (Nat × Trie α)
  | [] => []
  | p :: rest => if p.1 == c then (p.1, f p.2) :: rest else p :: updateChild c f rest

/-- Store `a` at key `k`, creating the missing spine as it descends. -/
def insert {α : Type} : Trie α → List Nat → α → Trie α
  | .node _ cs, [], a => .node (some a) cs
  | .node v cs, c :: rest, a =>
      if cs.any (fun p => p.1 == c) then
        .node v (updateChild c (fun t => insert t rest a) cs)
      else
        .node v (cs ++ [(c, insert empty rest a)])
termination_by structural _ k _ => k

/-- The child-list update `insert` performs never touches a child's symbol, so looking the symbol
up afterwards finds the same child with `f` applied. This is the whole content of the `some`
branch of `get_insert`. -/
theorem find?_updateChild {α : Type} (cs : List (Nat × Trie α)) (c : Nat)
    (f : Trie α → Trie α) :
    (updateChild c f cs).find? (fun p => p.1 == c)
      = (cs.find? (fun p => p.1 == c)).map (fun p => (p.1, f p.2)) := by
  induction cs with
  | nil => rfl
  | cons p ps ih =>
      by_cases hp : p.1 = c
      · simp [updateChild, hp]
      · simp [updateChild, hp, ih]

/-- **Insertion stores what it was given**, at the key it was given, whatever was there before.
Half of `InsertSpec`; `get_insert_other` is the other half. -/
theorem get_insert {α : Type} (t : Trie α) (k : List Nat) (a : α) :
    Trie.get (Trie.insert t k a) k = some a := by
  induction k generalizing t with
  | nil => cases t; simp [Trie.insert, Trie.get]
  | cons c rest ih =>
      cases t with
      | node v cs =>
          by_cases h : cs.any (fun p => p.1 == c)
          · have hs : (cs.find? (fun p => p.1 == c)).isSome := by
              rw [List.isSome_find?]; exact h
            obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
            simp [Trie.insert, Trie.get, h, find?_updateChild, hq, ih]
          · have hnone : cs.find? (fun p => p.1 == c) = none := by
              cases hq : cs.find? (fun p => p.1 == c) with
              | none => rfl
              | some q => exact absurd (by rw [← List.isSome_find?, hq]; rfl) h
            simp [Trie.insert, Trie.get, h, hnone, ih]

/-- Updating the child under `c` leaves the lookup of any other symbol exactly as it was. -/
theorem find?_updateChild_other {α : Type} (cs : List (Nat × Trie α)) {c c' : Nat}
    (h : c ≠ c') (f : Trie α → Trie α) :
    (updateChild c f cs).find? (fun p => p.1 == c') = cs.find? (fun p => p.1 == c') := by
  induction cs with
  | nil => rfl
  | cons p ps ih =>
      by_cases hp : p.1 = c
      · have : p.1 ≠ c' := hp ▸ h
        simp [updateChild, hp, h]
      · have hb : (p.1 == c) = false := by simp [hp]
        simp only [updateChild, hb, Bool.false_eq_true, ite_false, List.find?_cons, ih]

/-- **Every other key is untouched.** `get_insert` alone is met by an insert that stores the new
value and throws the rest of the trie away; this is the half that rules it out. -/
theorem get_insert_other {α : Type} (t : Trie α) {k k' : List Nat} (hk : k' ≠ k) (a : α) :
    Trie.get (Trie.insert t k a) k' = Trie.get t k' := by
  induction k generalizing t k' with
  | nil =>
      cases t with
      | node v cs =>
          cases k' with
          | nil => exact absurd rfl hk
          | cons c' rest' => simp [Trie.insert, Trie.get]
  | cons c rest ih =>
      cases t with
      | node v cs =>
          cases k' with
          | nil => simp only [Trie.insert]; split <;> simp [Trie.get]
          | cons c' rest' =>
              by_cases hc : c' = c
              · subst hc
                have hr : rest' ≠ rest := fun h => hk (by rw [h])
                by_cases h : cs.any (fun p => p.1 == c')
                · have hs : (cs.find? (fun p => p.1 == c')).isSome := by
                    rw [List.isSome_find?]; exact h
                  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
                  simp [Trie.insert, Trie.get, h, find?_updateChild, hq, ih _ hr]
                · have hnone : cs.find? (fun p => p.1 == c') = none := by
                    cases hq : cs.find? (fun p => p.1 == c') with
                    | none => rfl
                    | some q => exact absurd (by rw [← List.isSome_find?, hq]; rfl) h
                  have he : Trie.get (Trie.empty : Trie α) rest' = none := by
                    cases rest' <;> simp [Trie.empty, Trie.get]
                  simp [Trie.insert, Trie.get, h, hnone, List.find?_append, ih _ hr, he]
              · have hne : c ≠ c' := fun h => hc h.symm
                by_cases h : cs.any (fun p => p.1 == c)
                · simp [Trie.insert, Trie.get, h, find?_updateChild_other cs hne]
                · simp [Trie.insert, Trie.get, h, List.find?_append, hne]

/-- **`insert` discharges `InsertSpec`.** -/
theorem insertSpec {α : Type} (t : Trie α) (k : List Nat) (a : α) :
    InsertSpec k a t (Trie.insert t k a) := by
  intro k'
  by_cases h : k' = k
  · subst h; simp [get_insert]
  · simp [h, get_insert_other t h]

theorem distinctLetters_empty {α : Type} : DistinctLetters (Trie.empty : Trie α) := by
  simp [Trie.empty, DistinctLetters, DistinctLettersChildren]

theorem map_fst_updateChild {α : Type} (c : Nat) (f : Trie α → Trie α) :
    ∀ cs : List (Nat × Trie α), (updateChild c f cs).map (·.1) = cs.map (·.1)
  | [] => rfl
  | p :: rest => by
      by_cases hp : p.1 = c
      · simp [updateChild, hp]
      · have hb : (p.1 == c) = false := by simp [hp]
        simp only [updateChild, hb, Bool.false_eq_true, ite_false, List.map_cons,
          map_fst_updateChild c f rest]

theorem distinctLettersChildren_updateChild {α : Type} (c : Nat) (f : Trie α → Trie α)
    (hf : ∀ t, DistinctLetters t → DistinctLetters (f t)) :
    ∀ cs : List (Nat × Trie α), DistinctLettersChildren cs →
      DistinctLettersChildren (updateChild c f cs)
  | [] => fun _ => trivial
  | p :: rest => fun h => by
      by_cases hp : p.1 = c
      · simp only [updateChild, hp, beq_self_eq_true, ite_true, DistinctLettersChildren]
        exact ⟨hf _ h.1, h.2⟩
      · have hb : (p.1 == c) = false := by simp [hp]
        simp only [updateChild, hb, Bool.false_eq_true, ite_false, DistinctLettersChildren]
        exact ⟨h.1, distinctLettersChildren_updateChild c f hf rest h.2⟩

private theorem distinctLettersChildren_append {α : Type} :
    ∀ (cs : List (Nat × Trie α)) (p : Nat × Trie α),
      DistinctLettersChildren cs → DistinctLetters p.2 → DistinctLettersChildren (cs ++ [p])
  | [], _, _, hp => ⟨hp, trivial⟩
  | _ :: rest, p, h, hp => ⟨h.1, distinctLettersChildren_append rest p h.2 hp⟩

/-- **`insert` keeps the invariant.** A new symbol is appended only when no child carries it yet;
an existing one is descended into, never duplicated. -/
theorem distinctLetters_insert {α : Type} (a : α) :
    ∀ (k : List Nat) (t : Trie α), DistinctLetters t → DistinctLetters (Trie.insert t k a)
  | [], .node _ cs, h => by simpa [Trie.insert, DistinctLetters] using h
  | c :: rest, .node v cs, h => by
      obtain ⟨hnd, haux⟩ := h
      by_cases hc : cs.any (fun p => p.1 == c)
      · simp only [Trie.insert, hc, ite_true, DistinctLetters]
        exact ⟨by rw [map_fst_updateChild]; exact hnd,
          distinctLettersChildren_updateChild c _ (fun t ht => distinctLetters_insert a rest t ht)
            cs haux⟩
      · simp only [Trie.insert, hc, Bool.false_eq_true, ite_false, DistinctLetters]
        refine ⟨?_, distinctLettersChildren_append cs _ haux
            (distinctLetters_insert a rest _ distinctLetters_empty)⟩
        have hnot : c ∉ cs.map (·.1) := by
          intro hm
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          exact hc (List.any_eq_true.mpr ⟨q, hq, by simp⟩)
        rw [List.map_append]
        refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
        intro x hx y hy
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
        subst hy
        exact fun hxy => hnot (hxy ▸ hx)

/-- `updateChild` keeps the child list's length: it rewrites one child in place. -/
theorem length_updateChild {α : Type} (c : Nat) (f : Trie α → Trie α) :
    (cs : List (Nat × Trie α)) → (Trie.updateChild c f cs).length = cs.length
  | [] => rfl
  | p :: rest => by
      simp only [Trie.updateChild]
      split
      · rfl
      · simp only [List.length_cons, length_updateChild c f rest]

private theorem noDeadBranchesChildren_updateChild {α : Type} (c : Nat) (f : Trie α → Trie α)
    (hf : ∀ s, NoDeadBranchesNode s → NoDeadBranchesNode (f s)) :
    (cs : List (Nat × Trie α)) → NoDeadBranchesChildren cs →
      NoDeadBranchesChildren (Trie.updateChild c f cs)
  | [], _ => trivial
  | p :: rest, ⟨h1, h2⟩ => by
      simp only [Trie.updateChild]
      split
      · exact ⟨hf _ h1, h2⟩
      · exact ⟨h1, noDeadBranchesChildren_updateChild c f hf rest h2⟩

private theorem noDeadBranchesChildren_append {α : Type} (p : Nat × Trie α)
    (hp : NoDeadBranchesNode p.2) :
    (cs : List (Nat × Trie α)) → NoDeadBranchesChildren cs → NoDeadBranchesChildren (cs ++ [p])
  | [], _ => ⟨hp, trivial⟩
  | _ :: rest, ⟨h1, h2⟩ => ⟨h1, noDeadBranchesChildren_append p hp rest h2⟩

/-- Insertion into a `NoDeadBranches` trie leaves a `NoDeadBranchesNode`: the node either takes the
value or gains the child the key passes through. -/
theorem noDeadBranchesNode_insert {α : Type} (a : α) :
    (k : List Nat) → (t : Trie α) → NoDeadBranches t → NoDeadBranchesNode (Trie.insert t k a)
  | [], .node _ cs, h => by
      simp only [Trie.insert]
      exact ⟨fun _ => by simp, h⟩
  | c :: rest, .node v cs, h => by
      simp only [Trie.insert]
      split
      · rename_i hc
        refine ⟨fun he => ?_, noDeadBranchesChildren_updateChild c _
          (fun s hs => noDeadBranchesNode_insert a rest s hs.noDeadBranches) cs h⟩
        have hl := length_updateChild c (fun t => Trie.insert t rest a) cs
        rw [he] at hl
        cases cs with
        | nil => simp at hc
        | cons _ _ => simp at hl
      · exact ⟨fun he => by simp at he, noDeadBranchesChildren_append _
          (noDeadBranchesNode_insert a rest _ noDeadBranches_empty) cs h⟩

/-- **`Trie.insert` keeps `NoDeadBranches`**, so every trie built by insertions from empty has
it. -/
theorem noDeadBranches_insert {α : Type} {t : Trie α} (k : List Nat) (a : α)
    (h : NoDeadBranches t) :
    NoDeadBranches (Trie.insert t k a) :=
  (noDeadBranchesNode_insert a k t h).noDeadBranches

/-- The empty trie is `Valid`: one root, no children, nothing to collide or dangle. -/
theorem valid_empty {α : Type} : Valid (Trie.empty : Trie α) :=
    ⟨distinctLetters_empty, noDeadBranches_empty⟩

/-- **`insert` keeps the invariant**: `distinctLetters_insert` and `noDeadBranches_insert`. -/
theorem valid_insert {α : Type} {t : Trie α} (k : List Nat) (a : α) (h : Valid t) :
    Valid (Trie.insert t k a) :=
  ⟨distinctLetters_insert a k t h.1, noDeadBranches_insert k a h.2⟩

end Trie

end AlgoDesign.Strings
