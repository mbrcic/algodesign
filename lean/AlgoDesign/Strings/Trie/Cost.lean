/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie.Remove

/-!
# Trie: cost

`getM`, `get` with one tick per child step, returns `get`'s answer (`ret_getM`) after at most
`|key|` steps (`time_getM_le`), exactly `|key|` when the key is present (`time_getM_of_isSome`).
`insertM` takes exactly `|key|` (`time_insertM`), `removeM` at most `2·|key|`
(`time_removeM_le`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Trie

/-! ### The cost of a lookup -/

/-- `get` with one tick per child step: per edge descended, the unit the Rust's `get` pays as one
`next[byte]` slot read per byte of the key. Finding the child in the association list is the
representation's business and is not charged. -/
def getM {α : Type} : Trie α → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (Option α)
  | .node v _, [] => ⟨v, 0⟩
  | .node _ cs, c :: rest =>
      match cs.find? (fun p => p.1 == c) with
      | some p =>
          let r := getM p.2 rest
          ⟨r.ret, r.time + 1⟩
      | none => ⟨none, 0⟩
termination_by structural _ k => k

/-- Cost erasure: the timed lookup answers what `get` answers. -/
theorem ret_getM {α : Type} (t : Trie α) (k : List Nat) : (getM t k).ret = get t k := by
  induction k generalizing t with
  | nil => cases t; rfl
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [getM, get]
          split <;> split <;> simp_all

/-- **A lookup takes at most `|key|` edge steps**, found or not, on any trie. -/
theorem time_getM_le {α : Type} (t : Trie α) (k : List Nat) : (getM t k).time ≤ k.length := by
  induction k generalizing t with
  | nil => cases t; simp [getM]
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [getM, List.length_cons]
          split
          · rename_i p _
            have := ih p.2
            simp only
            omega
          · simp

/-- **A successful lookup takes exactly `|key|` edge steps**: the key is the path, and a value is
only read at its end. -/
theorem time_getM_of_isSome {α : Type} (t : Trie α) (k : List Nat) (h : (get t k).isSome) :
    (getM t k).time = k.length := by
  induction k generalizing t with
  | nil => cases t; simp [getM]
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [get] at h
          simp only [getM, List.length_cons]
          split
          · rename_i p hp
            rw [hp] at h
            simp only at h
            simp [ih _ h]
          · rename_i hp
            rw [hp] at h
            simp at h

/-! ### The cost of an update

Insert walks the word's path once, creating the missing nodes; remove looks the word up, then
walks its path once more to clear it, as the Rust does. One tick per child step, as for `getM`. -/

/-- Updating the child `find?` finds depends only on what the update does to that child. -/
theorem updateChild_congr {α : Type} {c : Nat} {p : Nat × Trie α} :
    ∀ {cs : List (Nat × Trie α)}, cs.find? (fun q => q.1 == c) = some p →
      ∀ {f g : Trie α → Trie α}, f p.2 = g p.2 → updateChild c f cs = updateChild c g cs
  | [], h, _, _, _ => by simp at h
  | q :: qs, h, f, g, hfg => by
      by_cases hq : q.1 = c
      · simp only [List.find?_cons, hq, beq_self_eq_true, Option.some.injEq] at h
        subst h
        simp [updateChild, hq, hfg]
      · have hq' : (q.1 == c) = false := by simpa using hq
        simp only [List.find?_cons, hq'] at h
        simp only [updateChild, hq', Bool.false_eq_true, ↓reduceIte]
        rw [updateChild_congr h hfg]

/-- `insert` with one tick per child step, descended or created. -/
def insertM {α : Type} : Trie α → List Nat → α → Cslib.Algorithms.Lean.TimeM ℕ (Trie α)
  | .node _ cs, [], a => ⟨.node (some a) cs, 0⟩
  | .node v cs, c :: rest, a =>
      match cs.find? (fun p => p.1 == c) with
      | some p =>
          let r := insertM p.2 rest a
          ⟨.node v (updateChild c (fun _ => r.ret) cs), r.time + 1⟩
      | none =>
          let r := insertM empty rest a
          ⟨.node v (cs ++ [(c, r.ret)]), r.time + 1⟩
termination_by structural _ k _ => k

/-- Cost erasure: the counted insert stores what `insert` stores. -/
theorem ret_insertM {α : Type} (t : Trie α) (k : List Nat) (a : α) :
    (insertM t k a).ret = insert t k a := by
  induction k generalizing t with
  | nil => cases t; rfl
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [insertM, insert]
          split
          · rename_i p hp
            have hany : cs.any (fun q => q.1 == c) = true :=
              List.any_eq_true.2
                ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩
            simp only [hany, ↓reduceIte, Trie.node.injEq, true_and]
            exact updateChild_congr hp (ih p.2)
          · rename_i hp
            have hany : cs.any (fun q => q.1 == c) = false := by
              rw [List.find?_eq_none] at hp
              simpa using hp
            simp [hany, ih]

/-- **Insert takes exactly `|key|` child steps**: it walks the key's path once. -/
theorem time_insertM {α : Type} (t : Trie α) (k : List Nat) (a : α) :
    (insertM t k a).time = k.length := by
  induction k generalizing t with
  | nil => cases t; rfl
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [insertM, List.length_cons]
          split <;> simp [ih]

/-- `erase` with one tick per child step descended. -/
def eraseM {α : Type} : Trie α → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (Trie α)
  | .node _ cs, [] => ⟨.node none cs, 0⟩
  | .node v cs, c :: rest =>
      match cs.find? (fun p => p.1 == c) with
      | none => ⟨.node v cs, 0⟩
      | some p =>
          let r := eraseM p.2 rest
          if isBare r.ret then ⟨.node v (dropChild c cs), r.time + 1⟩
          else ⟨.node v (updateChild c (fun _ => r.ret) cs), r.time + 1⟩
termination_by structural _ k => k

/-- Cost erasure: the counted erase leaves what `erase` leaves. -/
theorem ret_eraseM {α : Type} (t : Trie α) (k : List Nat) : (eraseM t k).ret = erase t k := by
  induction k generalizing t with
  | nil => cases t; rfl
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [eraseM, erase]
          cases hp : cs.find? (fun p => p.1 == c) with
          | none => rfl
          | some p =>
              simp only [ih p.2]
              split
              · rfl
              · exact congrArg (Trie.node v)
                  (updateChild_congr hp (f := fun _ => p.2.erase rest) (g := (erase · rest)) rfl)

/-- Erase takes at most `|key|` child steps. -/
theorem time_eraseM_le {α : Type} (t : Trie α) (k : List Nat) : (eraseM t k).time ≤ k.length := by
  induction k generalizing t with
  | nil => cases t; simp [eraseM]
  | cons c rest ih =>
      cases t with
      | node v cs =>
          simp only [eraseM, List.length_cons]
          split
          · simp
          · rename_i p _
            have := ih p.2
            split <;> simp only <;> omega

/-- `remove`, counted: the lookup's child steps (`getM`), then erase's when the word is there. -/
def removeM {α : Type} (t : Trie α) (k : List Nat) : Cslib.Algorithms.Lean.TimeM ℕ (Trie α) :=
  if (getM t k).ret.isSome then ⟨(eraseM t k).ret, (getM t k).time + (eraseM t k).time⟩
  else ⟨t, (getM t k).time⟩

/-- Cost erasure: the counted remove leaves what `remove` leaves. -/
theorem ret_removeM {α : Type} (t : Trie α) (k : List Nat) : (removeM t k).ret = remove t k := by
  unfold removeM remove
  rw [ret_getM]
  split <;> simp [ret_eraseM]

/-- **Remove takes at most `2·|key|` child steps**: one walk to look the word up, one to clear
it. -/
theorem time_removeM_le {α : Type} (t : Trie α) (k : List Nat) :
    (removeM t k).time ≤ 2 * k.length := by
  have h1 := time_getM_le t k
  have h2 := time_eraseM_le t k
  unfold removeM
  split <;> simp only <;> omega

/-! ### Memory: up to a node per letter stored -/

mutual

/-- A subtrie that keeps `NoDeadBranches` holds a word, and has at most one node per letter of its
words plus one per word. -/
private theorem nodeCount_le_node {α : Type} : (c : Trie α) → NoDeadBranchesNode c →
    nodeCount c ≤ ((words c).map List.length).sum + (words c).length ∧ 0 < (words c).length
  | .node v cs, ⟨hleaf, hcs⟩ => by
      obtain ⟨hle, hne⟩ := nodeCount_le_children cs hcs
      cases v with
      | some a =>
          simp only [nodeCount, words, List.cons_append, List.nil_append, List.map_cons,
            List.length_nil, List.sum_cons, List.length_cons]
          omega
      | none =>
          have hpos := hne (fun h => hleaf h rfl)
          simp only [nodeCount, words, List.nil_append]
          omega

/-- The child-list half: the subtries below a child list have at most one node per letter of the
words they hold (each word carrying its child's letter), and a non-empty list holds a word. -/
private theorem nodeCount_le_children {α : Type} : (cs : List (Nat × Trie α)) →
    NoDeadBranchesChildren cs →
    nodeCountChildren cs ≤ ((wordsAux cs).map List.length).sum ∧
      (cs ≠ [] → 0 < (wordsAux cs).length)
  | [], _ => by simp [nodeCountChildren, wordsAux]
  | (c, t) :: rest, ⟨ht, hrest⟩ => by
      obtain ⟨h1, h2⟩ := nodeCount_le_node t ht
      obtain ⟨h3, -⟩ := nodeCount_le_children rest hrest
      have hsum : (((words t).map (c :: ·)).map List.length).sum =
          ((words t).map List.length).sum + (words t).length := by
        rw [List.map_map]
        induction words t with
        | nil => simp
        | cons w ws ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
            Function.comp_apply, List.length_cons] at ih ⊢; omega
      simp only [nodeCountChildren, wordsAux, List.map_append, List.sum_append, hsum,
        List.length_append, List.length_map]
      constructor
      · omega
      · intro _; omega

end

/-- **The box's memory line**, "up to a node per letter stored": a valid trie has at most one node
per letter of its stored words, besides the root. -/
theorem nodeCount_le {α : Type} (t : Trie α) (h : Valid t) :
    nodeCount t ≤ (t.words.map List.length).sum + 1 := by
  obtain ⟨-, hnd⟩ := h
  match t, hnd with
  | .node v cs, hnd =>
      obtain ⟨hle, -⟩ := nodeCount_le_children cs hnd
      cases v <;> simp only [nodeCount, words, List.cons_append, List.nil_append, List.map_cons,
        List.sum_cons, List.length_nil] <;> omega

end Trie

end AlgoDesign.Strings
