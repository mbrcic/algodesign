/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie.Insert

/-!
# Trie: removal
`remove`, Sedgewick–Wayne's `TrieST.delete` as `trie.rs` runs it: on a `DistinctLetters` trie it
removes exactly its key (`get_remove`, `get_remove_other`, `words_remove` through `mem_words_iff`)
and keeps `DistinctLetters` (`distinctLetters_remove`) and `NoDeadBranches`
(`noDeadBranches_remove`), so `Valid` (`valid_remove`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Trie

/-! ### Removal

Sedgewick–Wayne's `TrieST.delete`, as `trie.rs` and `trie.py` run it: a key that holds no value
changes nothing; otherwise its value is cleared and every node the key's path leaves with no value
and no child is cut away, walking back up until a node keeps a value or another child, or the
root, which always stays. `erase` states that walk recursively: a child that comes back bare is
dropped from its parent's list. -/

/-- A node with no value and no child: what `remove` cuts away. -/
def isBare {α : Type} : Trie α → Bool
  | .node none [] => true
  | _ => false

/-- Drop the first child filed under `c`. -/
def dropChild {α : Type} (c : Nat) : List (Nat × Trie α) → List (Nat × Trie α)
  | [] => []
  | p :: rest => if p.1 == c then rest else p :: dropChild c rest

/-- Clear the value at `k` and cut every child the clearing leaves bare. -/
def erase {α : Type} : Trie α → List Nat → Trie α
  | .node _ cs, [] => .node none cs
  | .node v cs, c :: rest =>
      match cs.find? (fun p => p.1 == c) with
      | none => .node v cs
      | some p =>
          if isBare (erase p.2 rest) then .node v (dropChild c cs)
          else .node v (updateChild c (fun t => erase t rest) cs)
termination_by structural _ k => k

/-- `TrieST.delete`: nothing changes unless `k` holds a value. -/
def remove {α : Type} (t : Trie α) (k : List Nat) : Trie α :=
  if (get t k).isSome then erase t k else t

private theorem get_bare {α : Type} {t : Trie α} (h : isBare t = true) (k : List Nat) :
    get t k = none := by
  match t, h with
  | .node none [], _ => cases k <;> rfl

/-- Two children of a `DistinctLetters` child list filed under one symbol are the same child. -/
theorem eq_of_fst_eq {α : Type} :
    ∀ {cs : List (Nat × Trie α)}, (cs.map (·.1)).Nodup →
      ∀ {p q : Nat × Trie α}, p ∈ cs → q ∈ cs → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | r :: rest, hnd, p, q, hp, hq, hpq => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hp with rfl | hp' <;> rcases List.mem_cons.mp hq with rfl | hq'
      · rfl
      · exact absurd (hpq ▸ List.mem_map_of_mem hq') hnd.1
      · exact absurd (hpq.symm ▸ List.mem_map_of_mem hp') hnd.1
      · exact eq_of_fst_eq hnd.2 hp' hq' hpq

/-- Every child of a `DistinctLetters` child list is `DistinctLetters`. -/
theorem distinctLetters_of_mem {α : Type} :
    ∀ {cs : List (Nat × Trie α)}, DistinctLettersChildren cs →
      ∀ {p}, p ∈ cs → DistinctLetters p.2
  | [], _, _, hp => by simp at hp
  | r :: rest, h, p, hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact h.1
      · exact distinctLetters_of_mem h.2 hp'

private theorem find?_dropChild_self {α : Type} (c : Nat) :
    ∀ {cs : List (Nat × Trie α)}, (cs.map (·.1)).Nodup →
      (dropChild c cs).find? (fun p => p.1 == c) = none
  | [], _ => rfl
  | p :: rest, hnd => by
      rw [List.map_cons, List.nodup_cons] at hnd
      by_cases hp : p.1 = c
      · simp only [dropChild, hp, beq_self_eq_true, ite_true]
        rw [List.find?_eq_none]
        intro q hq hqc
        exact hnd.1 (by rw [hp, ← (beq_iff_eq.mp hqc)]; exact List.mem_map_of_mem hq)
      · have hb : (p.1 == c) = false := by simp [hp]
        simp only [dropChild, hb, Bool.false_eq_true, ite_false, List.find?_cons]
        exact find?_dropChild_self c hnd.2

private theorem find?_dropChild_other {α : Type} {c d : Nat} (hcd : d ≠ c) :
    ∀ cs : List (Nat × Trie α),
      (dropChild c cs).find? (fun p => p.1 == d) = cs.find? (fun p => p.1 == d)
  | [] => rfl
  | p :: rest => by
      by_cases hp : p.1 = c
      · have hcd' : c ≠ d := Ne.symm hcd
        simp [dropChild, hp, hcd']
      · have hb : (p.1 == c) = false := by simp [hp]
        simp only [dropChild, hb, Bool.false_eq_true, ite_false, List.find?_cons]
        split
        · rfl
        · exact find?_dropChild_other hcd rest

private theorem sublist_dropChild {α : Type} (c : Nat) :
    ∀ cs : List (Nat × Trie α), (dropChild c cs).Sublist cs
  | [] => List.Sublist.slnil
  | p :: rest => by
      simp only [dropChild]
      split
      · exact List.sublist_cons_self _ _
      · exact (sublist_dropChild c rest).cons_cons _

private theorem distinctLettersChildren_sublist {α : Type} :
    ∀ {cs ds : List (Nat × Trie α)}, cs.Sublist ds →
      DistinctLettersChildren ds → DistinctLettersChildren cs
  | _, _, .slnil, _ => trivial
  | _, _, .cons _ h, hd => distinctLettersChildren_sublist h hd.2
  | _, _, .cons_cons _ h, hd => ⟨hd.1, distinctLettersChildren_sublist h hd.2⟩

/-- **What `erase` does to lookups**, on a `DistinctLetters` trie: `k` maps to nothing, every other
key to what it did before. -/
theorem get_erase {α : Type} :
    ∀ (k : List Nat) (t : Trie α), DistinctLetters t → ∀ k',
      get (erase t k) k' = if k' = k then none else get t k'
  | [], .node v cs, _, k' => by
      cases k' <;> simp [erase, get]
  | c :: rest, .node v cs, ⟨hnd, haux⟩, k' => by
      rcases hq : cs.find? (fun p => p.1 == c) with _ | q
      · simp only [erase, hq]
        split
        · subst_vars; simp [get, hq]
        · rfl
      · have hqm := List.mem_of_find?_eq_some hq
        have hqc : q.1 = c := by simpa using List.find?_some hq
        have ih := get_erase rest q.2 (distinctLetters_of_mem haux hqm)
        simp only [erase, hq]
        split
        · rename_i hbare
          cases k' with
          | nil => simp [get]
          | cons d rest' =>
              by_cases hdc : d = c
              · subst hdc
                simp only [get, find?_dropChild_self d hnd, hq]
                have := ih rest'
                rw [get_bare hbare] at this
                split
                · rfl
                · rename_i hne
                  have : rest' ≠ rest := fun h => hne (by rw [h])
                  simp_all
              · simp only [get, find?_dropChild_other hdc]
                simp [hdc]
        · cases k' with
          | nil => simp [get]
          | cons d rest' =>
              by_cases hdc : d = c
              · subst hdc
                simp only [get, find?_updateChild, hq, Option.map_some]
                rw [ih rest']
                simp
              · simp only [get, find?_updateChild_other cs (Ne.symm hdc)]
                simp [hdc]

/-- `erase` keeps the invariant: it drops a child or rewrites one in place. -/
theorem distinctLetters_erase {α : Type} :
    ∀ (k : List Nat) (t : Trie α), DistinctLetters t → DistinctLetters (erase t k)
  | [], .node _ cs, h => by simpa [erase, DistinctLetters] using h
  | c :: rest, .node v cs, ⟨hnd, haux⟩ => by
      simp only [erase]
      split
      · exact ⟨hnd, haux⟩
      · split
        · exact ⟨(sublist_dropChild c cs).map (·.1) |>.nodup hnd,
            distinctLettersChildren_sublist (sublist_dropChild c cs) haux⟩
        · exact ⟨by rw [map_fst_updateChild]; exact hnd,
            distinctLettersChildren_updateChild c _ (fun t ht => distinctLetters_erase rest t ht)
              cs haux⟩

/-- **Removal removes the key**: afterwards `k` maps to nothing. -/
theorem get_remove {α : Type} (t : Trie α) (h : DistinctLetters t) (k : List Nat) :
    get (remove t k) k = none := by
  unfold remove
  split
  · simp [get_erase k t h]
  · rename_i hs; simpa using hs

/-- **And nothing else**: every other key maps to what it did before. -/
theorem get_remove_other {α : Type} (t : Trie α) (h : DistinctLetters t) {k k' : List Nat}
    (hk : k' ≠ k) : get (remove t k) k' = get t k' := by
  unfold remove
  split
  · simp [get_erase k t h, hk]
  · rfl

/-- `remove` keeps the invariant. -/
theorem distinctLetters_remove {α : Type} (t : Trie α) (h : DistinctLetters t) (k : List Nat) :
    DistinctLetters (remove t k) := by
  unfold remove
  split
  · exact distinctLetters_erase k t h
  · exact h

/-- A key of a child list is a child's symbol followed by one of that child's words. -/
theorem mem_wordsAux {α : Type} :
    ∀ (cs : List (Nat × Trie α)) (x : List Nat),
      x ∈ wordsAux cs ↔ ∃ p ∈ cs, ∃ y ∈ words p.2, x = p.1 :: y
  | [], x => by simp [wordsAux]
  | p :: rest, x => by
      rw [wordsAux, List.mem_append, mem_wordsAux rest x, List.mem_map]
      constructor
      · rintro (⟨y, hy, rfl⟩ | ⟨q, hq, y, hy, rfl⟩)
        · exact ⟨p, List.mem_cons_self .., y, hy, rfl⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, y, hy, rfl⟩
      · rintro ⟨q, hq, y, hy, rfl⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr ⟨q, hq', y, hy, rfl⟩

/-- **The words are the words that hold a value**, on a `DistinctLetters` trie: `words` lists a path
exactly when `get` answers it. -/
theorem mem_words_iff {α : Type} :
    ∀ (x : List Nat) (t : Trie α), DistinctLetters t → (x ∈ words t ↔ (get t x).isSome)
  | [], .node v cs, _ => by
      have : [] ∉ wordsAux cs := by
        rw [mem_wordsAux]; rintro ⟨_, _, _, _, h⟩; cases h
      cases v <;> simp [words, get, this]
  | c :: rest, .node v cs, ⟨hnd, haux⟩ => by
      have hx : c :: rest ∈ words (.node v cs) ↔ c :: rest ∈ wordsAux cs := by
        cases v <;> simp [words]
      rw [hx, mem_wordsAux]
      rcases hq : cs.find? (fun p => p.1 == c) with _ | q
      · simp only [get, hq, Option.isSome_none, Bool.false_eq_true, iff_false]
        rintro ⟨p, hp, y, _, hpy⟩
        have := List.find?_eq_none.mp hq p hp
        simp_all
      · have hqm := List.mem_of_find?_eq_some hq
        have hqc : q.1 = c := by simpa using List.find?_some hq
        simp only [get, hq]
        rw [← mem_words_iff rest q.2 (distinctLetters_of_mem haux hqm)]
        constructor
        · rintro ⟨p, hp, y, hy, hpy⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj hpy
          rw [eq_of_fst_eq hnd hp hqm (by rw [hqc])] at hy
          exact hy
        · intro hy
          exact ⟨q, hqm, rest, hy, by rw [hqc]⟩

/-- **The key set loses exactly the removed key**, on a `DistinctLetters` trie. -/
theorem words_remove {α : Type} (t : Trie α) (h : DistinctLetters t) (k x : List Nat) :
    x ∈ words (remove t k) ↔ x ∈ words t ∧ x ≠ k := by
  rw [mem_words_iff x _ (distinctLetters_remove t h k), mem_words_iff x t h]
  by_cases hx : x = k
  · subst hx; simp [get_remove t h]
  · simp [get_remove_other t h hx, hx]

private theorem noDeadBranchesNode_of_mem {α : Type} :
    ∀ {cs : List (Nat × Trie α)}, NoDeadBranchesChildren cs → ∀ {p}, p ∈ cs → NoDeadBranchesNode p.2
  | [], _, _, hp => by simp at hp
  | _ :: rest, h, p, hp => by
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact h.1
      · exact noDeadBranchesNode_of_mem h.2 hp'

private theorem noDeadBranchesChildren_sublist {α : Type} :
    ∀ {cs ds : List (Nat × Trie α)}, cs.Sublist ds → NoDeadBranchesChildren ds →
        NoDeadBranchesChildren cs
  | _, _, .slnil, _ => trivial
  | _, _, .cons _ h, hd => noDeadBranchesChildren_sublist h hd.2
  | _, _, .cons_cons _ h, hd => ⟨hd.1, noDeadBranchesChildren_sublist h hd.2⟩

/-- `updateChild` touches only the first child filed under `c`, which is the one `find?` names. -/
private theorem noDeadBranchesChildren_updateChild_at {α : Type} (c : Nat) (f : Trie α → Trie α) :
    ∀ {cs : List (Nat × Trie α)} {q}, cs.find? (fun p => p.1 == c) = some q →
      NoDeadBranchesNode (f q.2) → NoDeadBranchesChildren cs →
        NoDeadBranchesChildren (Trie.updateChild c f cs)
  | [], _, hq, _, _ => by simp at hq
  | p :: rest, q, hq, hf, ⟨h1, h2⟩ => by
      simp only [Trie.updateChild]
      by_cases hp : p.1 = c
      · have : q = p := by simp [hp] at hq; exact hq.symm
        subst this
        simp only [hp, beq_self_eq_true, ite_true]
        exact ⟨hf, h2⟩
      · have hb : (p.1 == c) = false := by simp [hp]
        simp only [List.find?_cons, hb] at hq
        simp only [hb, Bool.false_eq_true, ite_false]
        exact ⟨h1, noDeadBranchesChildren_updateChild_at c f hq hf h2⟩

/-- Below the root, `erase` leaves either a bare node, which its parent cuts, or a
`NoDeadBranchesNode`. -/
theorem noDeadBranchesNode_erase {α : Type} :
    ∀ (k : List Nat) (t : Trie α), NoDeadBranchesNode t →
      Trie.isBare (Trie.erase t k) = true ∨ NoDeadBranchesNode (Trie.erase t k)
  | [], .node _ cs, ⟨_, h⟩ => by
      cases cs with
      | nil => exact Or.inl rfl
      | cons p rest => exact Or.inr ⟨fun he => by simp at he, h⟩
  | c :: rest, .node v cs, ⟨hv, h⟩ => by
      simp only [Trie.erase]
      split
      · exact Or.inr ⟨hv, h⟩
      · rename_i q hq
        have hqm := List.mem_of_find?_eq_some hq
        split
        · have hsub := noDeadBranchesChildren_sublist (sublist_dropChild c cs) h
          cases v with
          | some a => exact Or.inr ⟨fun _ => by simp, hsub⟩
          | none =>
              cases hd : Trie.dropChild c cs with
              | nil => exact Or.inl rfl
              | cons x xs => exact Or.inr ⟨fun he => by simp at he, hd ▸ hsub⟩
        · rename_i hbare
          have hq2 := (noDeadBranchesNode_erase rest q.2 (noDeadBranchesNode_of_mem h
              hqm)).resolve_left hbare
          refine Or.inr ⟨fun he => ?_, noDeadBranchesChildren_updateChild_at c _ hq hq2 h⟩
          have hl := length_updateChild c (fun t => Trie.erase t rest) cs
          rw [he] at hl
          cases cs with
          | nil => simp at hqm
          | cons _ _ => simp at hl

/-- **`Trie.remove` keeps `NoDeadBranches`**: the cut takes every node the key's path leaves with no
value and no child, and stops at the root, which is exempt. -/
theorem noDeadBranches_remove {α : Type} {t : Trie α} (k : List Nat) (h : NoDeadBranches t) :
    NoDeadBranches (Trie.remove t k) := by
  unfold Trie.remove
  split
  · match k, t, h with
    | [], .node _ cs, h => exact h
    | c :: rest, .node v cs, h =>
        simp only [Trie.erase]
        split
        · exact h
        · rename_i q hq
          have hqm := List.mem_of_find?_eq_some hq
          split
          · exact noDeadBranchesChildren_sublist (sublist_dropChild c cs) h
          · rename_i hbare
            exact noDeadBranchesChildren_updateChild_at c _ hq
              ((noDeadBranchesNode_erase rest q.2 (noDeadBranchesNode_of_mem h hqm)).resolve_left
                  hbare) h
  · exact h

/-- **`remove` keeps the invariant**: `distinctLetters_remove` and `noDeadBranches_remove`. -/
theorem valid_remove {α : Type} {t : Trie α} (k : List Nat) (h : Valid t) :
    Valid (Trie.remove t k) :=
  ⟨distinctLetters_remove t h.1 k, noDeadBranches_remove k h.2⟩

end Trie

end AlgoDesign.Strings
