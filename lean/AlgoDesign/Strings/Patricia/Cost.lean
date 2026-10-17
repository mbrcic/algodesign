/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Remove

/-!
# Patricia: cost

The cost of a lookup: `getM`, counted through `Cslib.Algorithms.Lean.TimeM`, erases to `get`
(`ret_getM`) and is bounded by `time_getM_le`.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-! ### The cost of a lookup

One tick per **key symbol compared against an edge label**. A descent through the edge `c' :: lbl`
compares all `1 + |lbl|` of its symbols with the key's and consumes them; a failing label test is
charged `1 + min |lbl| |rest|`, the most a comparison of `lbl` with what is left of the key can
make. **Choosing the child is not charged**: `getAux` scans the siblings for the one whose label
begins with the key's next symbol, the Rust binary-searches them by that byte, and either is a
lookup in the node's child table, as `Trie.getM` does not charge its association-list scan. -/

mutual

/-- `get`, timed in key symbols compared against labels. -/
def getM {α : Type} : Patricia α → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (Option α)
  | .node v _, [] => ⟨v, 0⟩
  | .node _ cs, c :: rest => getAuxM cs c rest

/-- `getAux`, timed: the sibling scan is free, the chosen label's comparison is not. -/
def getAuxM {α : Type} :
    List (List Nat × Patricia α) → Nat → List Nat → Cslib.Algorithms.Lean.TimeM ℕ (Option α)
  | [], _, _ => ⟨none, 0⟩
  | ([], _) :: ps, c, rest => getAuxM ps c rest
  | (c' :: lbl, t) :: ps, c, rest =>
      if c' = c then
        if lbl.isPrefixOf rest then
          let r := getM t (rest.drop lbl.length)
          ⟨r.ret, r.time + (1 + lbl.length)⟩
        else ⟨none, 1 + min lbl.length rest.length⟩
      else getAuxM ps c rest

end

mutual

/-- Cost erasure: the timed lookup answers what `get` answers. -/
theorem ret_getM {α : Type} : (t : Patricia α) → (k : List Nat) → (getM t k).ret = get t k
  | .node _ _, [] => rfl
  | .node _ cs, c :: rest => ret_getAuxM cs c rest

theorem ret_getAuxM {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → (getAuxM cs c rest).ret = getAux cs c rest
  | [], _, _ => rfl
  | ([], _) :: ps, c, rest => by
      simp only [getAuxM, getAux]
      exact ret_getAuxM ps c rest
  | (c' :: lbl, t) :: ps, c, rest => by
      simp only [getAuxM, getAux]
      split
      · split
        · exact ret_getM t _
        · rfl
      · exact ret_getAuxM ps c rest

end

mutual

/-- **A lookup compares at most `|key|` key symbols against labels**, found or not, on any
tree: every symbol charged is a symbol of the key, and each is charged once. -/
theorem time_getM_le {α : Type} : (t : Patricia α) → (k : List Nat) →
    (getM t k).time ≤ k.length
  | .node _ _, [] => by simp [getM]
  | .node _ cs, c :: rest => by
      simp only [getM, List.length_cons]
      exact time_getAuxM_le cs c rest

theorem time_getAuxM_le {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → (getAuxM cs c rest).time ≤ rest.length + 1
  | [], _, _ => by simp [getAuxM]
  | ([], _) :: ps, c, rest => by
      simp only [getAuxM]
      exact time_getAuxM_le ps c rest
  | (c' :: lbl, t) :: ps, c, rest => by
      simp only [getAuxM]
      split
      · split
        · rename_i hpre
          have hle : lbl.length ≤ rest.length :=
            (List.isPrefixOf_iff_prefix.mp hpre).length_le
          have := time_getM_le t (rest.drop lbl.length)
          simp only [List.length_drop] at this
          change (getM t (rest.drop lbl.length)).time + (1 + lbl.length) ≤ rest.length + 1
          omega
        · simp only
          omega
      · exact time_getAuxM_le ps c rest

end

/-! ### Memory: at most two nodes per word -/

mutual

/-- A subtree below the root that keeps `BranchesUnlessWordEnds` has fewer than two nodes per word
it holds. -/
private theorem nodeCount_le_node {α : Type} : (c : Patricia α) → BranchesUnlessWordEndsNode c →
    nodeCount c + 1 ≤ 2 * (words c).length
  | .node v cs, ⟨hbranch, hcs⟩ => by
      have hle := nodeCount_le_children cs hcs
      cases v with
      | some a =>
          simp only [nodeCount, words, List.cons_append, List.nil_append, List.length_cons]
          omega
      | none =>
          have h2 : 2 ≤ cs.length := hbranch.resolve_left (fun h => h rfl)
          simp only [nodeCount, words, List.nil_append]
          omega

/-- The child-list half: the subtrees below a child list have, with one more per child, at most
two nodes per word they hold. -/
private theorem nodeCount_le_children {α : Type} : (cs : List (List Nat × Patricia α)) →
    BranchesUnlessWordEndsChildren cs →
    nodeCountChildren cs + cs.length ≤ 2 * (wordsAux cs).length
  | [], _ => by simp [nodeCountChildren, wordsAux]
  | (l, t) :: rest, ⟨ht, hrest⟩ => by
      have h1 := nodeCount_le_node t ht
      have h2 := nodeCount_le_children rest hrest
      simp only [nodeCountChildren, wordsAux, List.length_append, List.length_map,
        List.length_cons]
      omega

end

/-- **The box's cost line**, "at most two nodes per word, however long the words are, once one
word is stored": a valid tree holding at least one word has at most twice as many nodes as
words. -/
theorem nodeCount_le {α : Type} (t : Patricia α) (h : Valid t) (hne : t.words ≠ []) :
    nodeCount t ≤ 2 * t.words.length := by
  obtain ⟨-, hb, -⟩ := h
  match t, hb, hne with
  | .node v cs, hb, hne =>
      have hle := nodeCount_le_children cs hb
      cases v with
      | some a =>
          simp only [nodeCount, words, List.cons_append, List.nil_append, List.length_cons]
          omega
      | none =>
          have hcs : cs ≠ [] := by
            rintro rfl
            exact hne (by simp [words, wordsAux])
          have := List.length_pos_iff.mpr hcs
          simp only [nodeCount, words, List.nil_append]
          omega

end Patricia

end AlgoDesign.Strings
