/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Compress

/-!
# Patricia: insertion

The incremental `insert`, which splits an edge at the first mismatch. `insertSpec`: it discharges
`InsertSpec` on every tree. It keeps each piece of `Valid` on its own — `DistinctFirstLetters`,
`BranchesUnlessWordEnds` and `NoEmptyBranches` — and the key list gains the inserted key and loses
none.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-- **What any insertion owes**: afterwards `k` maps to `a` and every other key maps to what it did
before. -/
def InsertSpec {α : Type} (k : List Nat) (a : α) (before after : Patricia α) : Prop :=
  ∀ k', get after k' = if k' = k then some a else get before k'

/-! ## Incremental insertion by splitting edges

Walk down while a whole edge label matches the key. Where a label diverges from the key part-way,
**split the edge** at the first mismatch: the common part becomes the label of a fresh node, with
the rest of the old label and, if the key continues, the rest of the key as its children. With no
child to follow, the rest of the key becomes one new leaf edge. A new edge is appended at the end
of the child list. -/

/-- Split two lists at their longest common prefix: the common part, what is left of the first,
and what is left of the second. -/
def splitCommon : List Nat → List Nat → List Nat × List Nat × List Nat
  | x :: xs, y :: ys =>
      if x = y then
        let r := splitCommon xs ys
        (x :: r.1, r.2.1, r.2.2)
      else ([], x :: xs, y :: ys)
  | xs, ys => ([], xs, ys)

/-- What `splitCommon` returns: both lists rebuilt from the common part, and the two remainders
disagreeing on their first symbol whenever both have one. -/
theorem splitCommon_spec (l k : List Nat) :
    l = (splitCommon l k).1 ++ (splitCommon l k).2.1 ∧
      k = (splitCommon l k).1 ++ (splitCommon l k).2.2 ∧
      ∀ d e ls ks, (splitCommon l k).2.1 = d :: ls → (splitCommon l k).2.2 = e :: ks → d ≠ e := by
  induction l generalizing k with
  | nil => simp [splitCommon]
  | cons x xs ih =>
      cases k with
      | nil => simp [splitCommon]
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            obtain ⟨h1, h2, h3⟩ := ih ys
            simp only [splitCommon, ↓reduceIte, List.cons_append]
            exact ⟨congrArg _ h1, congrArg _ h2, h3⟩
          · simp only [splitCommon, hxy, ↓reduceIte, List.nil_append]
            refine ⟨by simp, by simp, ?_⟩
            rintro d e ls ks ⟨rfl, -⟩ ⟨rfl, -⟩
            exact hxy

mutual

/-- **Incremental insertion**, splitting an edge at the first mismatch. An empty key sets the
current node's value; any other key is handed to `insertAux`, which finds the child whose label
begins with the key's first symbol. -/
def insert {α : Type} : Patricia α → List Nat → α → Patricia α
  | .node _ cs, [], a => .node (some a) cs
  | .node v cs, c :: rest, a => .node v (insertAux cs c rest a)

/-- Insert `c :: rest` below a child list. The first child whose label begins with `c` is the one
changed, as `getAux` reads the first such child; with none, a new leaf edge carrying the whole
key is appended. At that child, with label `c :: lbl`, `splitCommon lbl rest` decides the case:
the whole label matches, and the insertion descends; or the key ends inside the label, and the
fresh node takes the value; or both continue and disagree, and the fresh node branches. -/
def insertAux {α : Type} :
    List (List Nat × Patricia α) → Nat → List Nat → α → List (List Nat × Patricia α)
  | [], c, rest, a => [(c :: rest, .node (some a) [])]
  | ([], t) :: ps, c, rest, a => ([], t) :: insertAux ps c rest a
  | (c' :: lbl, t) :: ps, c, rest, a =>
      if c' = c then
        match splitCommon lbl rest with
        | (_, [], keyRest) => (c' :: lbl, insert t keyRest a) :: ps
        | (pre, d :: lr, []) => (c :: pre, .node (some a) [(d :: lr, t)]) :: ps
        | (pre, d :: lr, f :: kr) =>
            (c :: pre, .node none [(d :: lr, t), (f :: kr, .node (some a) [])]) :: ps
      else (c' :: lbl, t) :: insertAux ps c rest a

end

/-- The answer an edge labelled `c :: lbl` over `t` gives for `c :: r`: `lbl` must be a prefix of
`r`, and `t` answers what is left. The inner step of `getAux`, named so the split can be
reasoned about one label piece at a time. -/
def edge {α : Type} (lbl : List Nat) (t : Patricia α) (r : List Nat) : Option α :=
  if lbl.isPrefixOf r then get t (r.drop lbl.length) else none

theorem getAux_cons_cons {α : Type} (c' c : Nat) (lbl r : List Nat) (t : Patricia α)
    (ps : List (List Nat × Patricia α)) :
    getAux ((c' :: lbl, t) :: ps) c r = if c' = c then edge lbl t r else getAux ps c r := rfl

theorem edge_append {α : Type} (pre s r : List Nat) (t : Patricia α) :
    edge (pre ++ s) t (pre ++ r) = edge s t r := by
  simp [edge]

theorem edge_of_not_prefix {α : Type} {pre r : List Nat} (h : ¬ pre <+: r)
    (s : List Nat) (t : Patricia α) : edge (pre ++ s) t r = none := by
  have : (pre ++ s).isPrefixOf r = false := by
    rw [Bool.eq_false_iff]
    intro hp
    exact h ((List.prefix_append pre s).trans (List.isPrefixOf_iff_prefix.mp hp))
  simp [edge, this]

private theorem edge_nil {α : Type} (t : Patricia α) (r : List Nat) : edge [] t r = get t r := by
  simp [edge, List.isPrefixOf]

/-- Through an edge labelled `pre`, a key `pre ++ r` asks the subtree for `r`. -/
theorem edge_prefix {α : Type} (pre r : List Nat) (t : Patricia α) :
    edge pre t (pre ++ r) = get t r := by
  rw [← edge_nil, ← edge_append pre [] r, List.append_nil]

theorem edge_self {α : Type} (pre : List Nat) (t : Patricia α) :
    edge pre t pre = get t [] := by
  simpa using edge_prefix pre [] t

/-- A leaf answers only the key that ends exactly at it. -/
private theorem edge_leaf_ne {α : Type} {kr s : List Nat} (h : s ≠ kr) (a : α) :
    edge kr (.node (some a) []) s = none := by
  by_cases hp : kr <+: s
  · obtain ⟨u, rfl⟩ := hp
    cases u with
    | nil => exact absurd (List.append_nil _) h
    | cons x u => rw [edge_prefix]; rfl
  · simpa using edge_of_not_prefix hp [] (.node (some a) [])

theorem edge_leaf_self {α : Type} (kr : List Nat) (a : α) :
    edge kr (.node (some a) []) kr = some a := by
  rw [edge_self]; rfl

theorem edge_none {α : Type} {pre r : List Nat} (h : ¬ pre <+: r) (t : Patricia α) :
    edge pre t r = none := by
  simpa using edge_of_not_prefix h [] t

/-- An edge whose label begins with `d` answers a key beginning with `e` only if `d = e`. -/
theorem edge_cons {α : Type} (d e : Nat) (lr r : List Nat) (t : Patricia α) :
    edge (d :: lr) t (e :: r) = if d = e then edge lr t r else none := by
  by_cases hde : d = e
  · subst hde; simp [edge, List.isPrefixOf]
  · simp [edge, List.isPrefixOf, hde]

mutual

/-- **Insertion stores the key.** Half of `InsertSpec`; no invariant is needed, because `insert`
changes exactly the child `get` will read — the first whose label begins with the key's next
symbol. -/
theorem get_insert {α : Type} : (t : Patricia α) → (k : List Nat) → (a : α) →
    get (insert t k a) k = some a
  | .node _ _, [], _ => rfl
  | .node _ cs, c :: rest, a => getAux_insertAux cs c rest a

/-- The child-list half of `get_insert`. -/
theorem getAux_insertAux {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → (a : α) → getAux (insertAux cs c rest a) c rest = some a
  | [], c, rest, a => by
      simp only [insertAux, getAux_cons_cons, ↓reduceIte]
      exact edge_leaf_self rest a
  | ([], _) :: ps, c, rest, a => getAux_insertAux ps c rest a
  | (c' :: lbl, t) :: ps, c, rest, a => by
      by_cases hc : c' = c
      · subst hc
        obtain ⟨hl, hr, hne⟩ := splitCommon_spec lbl rest
        simp only [insertAux, ↓reduceIte]
        rcases hs : splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
          rw [hs] at hl hr hne <;> simp only [List.append_nil] at hl hr hne ⊢ <;> subst hl hr <;>
          simp only [getAux_cons_cons, ↓reduceIte]
        · rw [edge_self]
          exact get_insert t [] a
        · rw [edge_prefix]
          exact get_insert t (f :: kr) a
        · rw [edge_self]
          rfl
        · rw [edge_prefix]
          have hdf := hne d f lr kr rfl rfl
          change getAux _ f kr = some a
          simp only [getAux_cons_cons, hdf, ↓reduceIte]
          exact edge_leaf_self kr a
      · simp only [insertAux, hc, ↓reduceIte, getAux_cons_cons]
        exact getAux_insertAux ps c rest a

end

mutual

/-- **Insertion disturbs no other key.** The other half of `InsertSpec`. Where the key's path
leaves the tree, a new leaf edge is added that no other key reaches; where an edge is split, the
fresh node passes every other key through to the old subtree exactly as the whole label did. -/
theorem get_insert_other {α : Type} : (t : Patricia α) → (k k' : List Nat) → k' ≠ k →
    (a : α) → get (insert t k a) k' = get t k'
  | .node _ _, [], [], h, _ => absurd rfl h
  | .node _ _, [], _ :: _, _, _ => rfl
  | .node _ _, _ :: _, [], _, _ => rfl
  | .node _ cs, c :: rest, c' :: r', h, a => getAux_insertAux_other cs c rest a c' r' h

/-- The child-list half of `get_insert_other`. -/
theorem getAux_insertAux_other {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → (a : α) → (c' : Nat) → (r' : List Nat) → c' :: r' ≠ c :: rest →
      getAux (insertAux cs c rest a) c' r' = getAux cs c' r'
  | [], c, rest, a, c', r', h => by
      simp only [insertAux, getAux_cons_cons]
      by_cases hc : c = c'
      · subst hc
        simp only [↓reduceIte]
        exact edge_leaf_ne (fun e => h (by rw [e])) a
      · simp only [hc, ↓reduceIte]
  | ([], _) :: ps, c, rest, a, c', r', h => getAux_insertAux_other ps c rest a c' r' h
  | (c'' :: lbl, t) :: ps, c, rest, a, c', r', h => by
      by_cases hc : c = c''
      · subst hc
        simp only [insertAux, ↓reduceIte]
        by_cases hc' : c = c'
        · subst hc'
          have hr : r' ≠ rest := fun e => h (by rw [e])
          obtain ⟨hl, hr', hne⟩ := splitCommon_spec lbl rest
          rcases hs : splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
            rw [hs] at hl hr' hne <;> simp only [List.append_nil] at hl hr' hne ⊢ <;>
            subst lbl rest <;> simp only [getAux_cons_cons, ↓reduceIte]
          · by_cases hp : pre <+: r'
            · obtain ⟨u, rfl⟩ := hp
              rw [edge_prefix, edge_prefix]
              exact get_insert_other t [] u (fun e => hr (by rw [e, List.append_nil])) a
            · rw [edge_none hp, edge_none hp]
          · by_cases hp : pre <+: r'
            · obtain ⟨u, rfl⟩ := hp
              rw [edge_prefix, edge_prefix]
              exact get_insert_other t (f :: kr) u (fun e => hr (by rw [e])) a
            · rw [edge_none hp, edge_none hp]
          · by_cases hp : pre <+: r'
            · obtain ⟨u, rfl⟩ := hp
              rw [edge_prefix, edge_append]
              cases u with
              | nil => exact absurd (List.append_nil pre) hr
              | cons e u =>
                  change getAux _ e u = _
                  rw [getAux_cons_cons, edge_cons]
                  rfl
            · rw [edge_none hp, edge_of_not_prefix hp]
          · by_cases hp : pre <+: r'
            · obtain ⟨u, rfl⟩ := hp
              rw [edge_prefix, edge_append]
              cases u with
              | nil => rfl
              | cons e u =>
                  change getAux _ e u = _
                  rw [getAux_cons_cons, getAux_cons_cons, edge_cons]
                  by_cases hde : d = e
                  · simp only [hde, ↓reduceIte]
                  · by_cases hfe : f = e
                    · subst hfe
                      simp only [hde, ↓reduceIte]
                      exact edge_leaf_ne (fun e => hr (by rw [e])) a
                    · simp only [hde, hfe, ↓reduceIte]
                      rfl
            · rw [edge_none hp, edge_of_not_prefix hp]
        · rcases splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
            simp only [getAux_cons_cons, hc', ↓reduceIte]
      · have hc₂ : ¬ c'' = c := fun e => hc e.symm
        simp only [insertAux, hc₂, ↓reduceIte, getAux_cons_cons]
        by_cases hc' : c'' = c'
        · simp only [hc', ↓reduceIte]
        · simp only [hc', ↓reduceIte]
          exact getAux_insertAux_other ps c rest a c' r' h

end

/-- **`insert` discharges `InsertSpec`**, on every tree: neither half needs an invariant. -/
theorem insertSpec {α : Type} (t : Patricia α) (k : List Nat) (a : α) :
    InsertSpec k a t (insert t k a) := by
  intro k'
  by_cases h : k' = k
  · subst h; simp [get_insert]
  · simp [h, get_insert_other t k k' h]

/-! ## What insertion keeps: the invariants -/

/-- Insertion never shortens a child list: it changes one child in place or appends one. -/
private theorem length_le_insertAux {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    (cs : List (List Nat × Patricia α)) → cs.length ≤ (insertAux cs c rest a).length
  | [] => Nat.zero_le _
  | ([], _) :: ps => by
      simpa [insertAux] using length_le_insertAux c rest a ps
  | (c' :: lbl, t) :: ps => by
      by_cases hc : c' = c
      · simp only [insertAux, hc, ↓reduceIte]
        rcases splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;> simp
      · simpa [insertAux, hc] using length_le_insertAux c rest a ps

mutual

/-- Insertion below a node that branches unless a word ends there leaves such a node: the value can
only be set, and the child list only grows. -/
theorem branchesUnlessWordEndsNode_insert {α : Type} : (t : Patricia α) → (k : List Nat) →
    (a : α) → BranchesUnlessWordEndsNode t → BranchesUnlessWordEndsNode (insert t k a)
  | .node _ cs, [], _, ⟨_, hcs⟩ => ⟨Or.inl (by simp), hcs⟩
  | .node _ cs, c :: rest, a, ⟨hv, hcs⟩ =>
      ⟨hv.imp id fun h => Nat.le_trans h (length_le_insertAux c rest a cs),
        branchesUnlessWordEndsChildren_insertAux cs c rest a hcs⟩

/-- The child-list half of `branchesUnlessWordEndsNode_insert`, where the split happens: the fresh
node either holds the value or has two children. -/
theorem branchesUnlessWordEndsChildren_insertAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) → (a : α) →
      BranchesUnlessWordEndsChildren cs →
        BranchesUnlessWordEndsChildren (insertAux cs c rest a)
  | [], _, _, _, _ => ⟨⟨Or.inl (by simp), trivial⟩, trivial⟩
  | ([], _) :: ps, c, rest, a, ⟨h2, h3⟩ =>
      ⟨h2, branchesUnlessWordEndsChildren_insertAux ps c rest a h3⟩
  | (c' :: lbl, t) :: ps, c, rest, a, ⟨h2, h3⟩ => by
      by_cases hc : c' = c
      · simp only [insertAux, hc, ↓reduceIte]
        rcases splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩
        · exact ⟨branchesUnlessWordEndsNode_insert t [] a h2, h3⟩
        · exact ⟨branchesUnlessWordEndsNode_insert t (f :: kr) a h2, h3⟩
        · exact ⟨⟨Or.inl (by simp), ⟨h2, trivial⟩⟩, h3⟩
        · exact ⟨⟨Or.inr (by simp), ⟨h2, ⟨⟨Or.inl (by simp), trivial⟩, trivial⟩⟩⟩, h3⟩
      · simp only [insertAux, hc, ↓reduceIte]
        exact ⟨h2, branchesUnlessWordEndsChildren_insertAux ps c rest a h3⟩

end

/-- **Insertion preserves `BranchesUnlessWordEnds`** (box line 3). -/
theorem branchesUnlessWordEnds_insert {α : Type} {t : Patricia α} (k : List Nat) (a : α)
    (h : BranchesUnlessWordEnds t) : BranchesUnlessWordEnds (insert t k a) := by
  cases t with
  | node v cs =>
      cases k with
      | nil => exact h
      | cons c rest => exact branchesUnlessWordEndsChildren_insertAux cs c rest a h

mutual

/-- **Insertion preserves `NoEmptyBranches`** (box line 4). -/
theorem noEmptyBranches_insert {α : Type} : (t : Patricia α) → (k : List Nat) → (a : α) →
    NoEmptyBranches t → NoEmptyBranches (insert t k a)
  | .node _ _, [], _, hcs => hcs
  | .node _ cs, c :: rest, a, hcs => noEmptyBranchesChildren_insertAux cs c rest a hcs

/-- The child-list half of `noEmptyBranches_insert`. A split leaves every label non-empty: the
common part keeps the matched first symbol, and the rest of the old label is non-empty because the
split fires only where the label diverges. -/
theorem noEmptyBranchesChildren_insertAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) → (a : α) →
      NoEmptyBranchesChildren cs → NoEmptyBranchesChildren (insertAux cs c rest a)
  | [], _, _, _, _ => ⟨by simp, trivial, trivial⟩
  | ([], _) :: _, _, _, _, ⟨h, _, _⟩ => absurd rfl h
  | (c' :: lbl, t) :: ps, c, rest, a, ⟨h1, h2, h3⟩ => by
      by_cases hc : c' = c
      · simp only [insertAux, hc, ↓reduceIte]
        rcases splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩
        · exact ⟨by simp, noEmptyBranches_insert t [] a h2, h3⟩
        · exact ⟨by simp, noEmptyBranches_insert t (f :: kr) a h2, h3⟩
        · exact ⟨by simp, ⟨by simp, h2, trivial⟩, h3⟩
        · exact ⟨by simp, ⟨by simp, h2, ⟨by simp, trivial, trivial⟩⟩, h3⟩
      · simp only [insertAux, hc, ↓reduceIte]
        exact ⟨h1, h2, noEmptyBranchesChildren_insertAux ps c rest a h3⟩

end

/-- The first symbols of the labels in a child list, which `DistinctFirstLetters` asks to be
distinct. -/
private theorem map_head?_insertAux {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    (cs : List (List Nat × Patricia α)) →
      (insertAux cs c rest a).map (·.1.head?)
        = if some c ∈ cs.map (·.1.head?) then cs.map (·.1.head?)
          else cs.map (·.1.head?) ++ [some c]
  | [] => by simp [insertAux]
  | ([], _) :: ps => by
      simp only [insertAux, List.map_cons, List.head?_nil, List.mem_cons, reduceCtorEq,
        false_or, map_head?_insertAux c rest a ps]
      split <;> simp
  | (c' :: lbl, t) :: ps => by
      by_cases hc : c' = c
      · subst hc
        simp only [insertAux, ↓reduceIte, List.map_cons, List.head?_cons, List.mem_cons,
          true_or]
        rcases splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;> rfl
      · simp only [insertAux, hc, ↓reduceIte, List.map_cons, List.head?_cons, List.mem_cons,
          Option.some.injEq, map_head?_insertAux c rest a ps]
        have hc' : ¬ c = c' := fun e => hc e.symm
        simp only [hc', false_or]
        split <;> simp

private theorem nodup_heads_insertAux {α : Type} (c : Nat) (rest : List Nat) (a : α)
    (cs : List (List Nat × Patricia α)) (h : (cs.map (·.1.head?)).Nodup) :
    ((insertAux cs c rest a).map (·.1.head?)).Nodup := by
  rw [map_head?_insertAux]
  split
  · exact h
  · rename_i hmem
    refine List.nodup_append.mpr ⟨h, by simp, fun x hx y hy => ?_⟩
    rw [List.mem_singleton] at hy
    subst hy
    rintro rfl
    exact hmem hx

mutual

/-- **Insertion preserves `DistinctFirstLetters`**, with no other hypothesis. The child it changes
keeps its first symbol; a new leaf edge is added only when no sibling begins with its symbol; and
the two children of a split node begin with the two symbols at which the label and the key disagree.
-/
theorem distinctFirstLetters_insert {α : Type} : (t : Patricia α) → (k : List Nat) → (a : α) →
    DistinctFirstLetters t → DistinctFirstLetters (insert t k a)
  | .node _ _, [], _, h => h
  | .node _ cs, c :: rest, a, ⟨h1, h2⟩ =>
      ⟨nodup_heads_insertAux c rest a cs h1, distinctFirstLettersChildren_insertAux cs c rest a h2⟩

/-- The child-list half of `distinctFirstLetters_insert`. -/
theorem distinctFirstLettersChildren_insertAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) → (a : α) →
      DistinctFirstLettersChildren cs → DistinctFirstLettersChildren (insertAux cs c rest a)
  | [], _, _, _, _ => ⟨⟨List.nodup_nil, trivial⟩, trivial⟩
  | ([], _) :: ps, c, rest, a, ⟨h1, h2⟩ =>
      ⟨h1, distinctFirstLettersChildren_insertAux ps c rest a h2⟩
  | (c' :: lbl, t) :: ps, c, rest, a, ⟨h1, h2⟩ => by
      by_cases hc : c' = c
      · simp only [insertAux, hc, ↓reduceIte]
        obtain ⟨-, -, hne⟩ := splitCommon_spec lbl rest
        rcases hs : splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
          rw [hs] at hne <;> simp only at hne
        · exact ⟨distinctFirstLetters_insert t [] a h1, h2⟩
        · exact ⟨distinctFirstLetters_insert t (f :: kr) a h1, h2⟩
        · exact ⟨⟨by simp, h1, trivial⟩, h2⟩
        · have hdf := hne d f lr kr rfl rfl
          exact ⟨⟨by simp [hdf], h1, ⟨List.nodup_nil, trivial⟩, trivial⟩, h2⟩
      · simp only [insertAux, hc, ↓reduceIte]
        exact ⟨h1, distinctFirstLettersChildren_insertAux ps c rest a h2⟩

end

mutual

/-- **What `insert` does to the key list**: it adds the key inserted and keeps every other, with
no invariant needed. Stated on membership, since `insert` files a new key where its path leaves
the tree, not at the end of the list; `words_ofList` gives the order for trees built from empty. -/
theorem mem_words_insert {α : Type} : (t : Patricia α) → (k : List Nat) → (a : α) →
    (x : List Nat) → (x ∈ (insert t k a).words ↔ x = k ∨ x ∈ t.words)
  | .node v cs, [], a, x => by
      cases v <;> simp [insert, words]
  | .node v cs, c :: rest, a, x => by
      have h := mem_wordsAux_insertAux cs c rest a x
      cases v <;> simp only [insert, words, List.mem_append, h] <;> simp only [or_left_comm]

/-- The child-list half of `mem_words_insert`. -/
theorem mem_wordsAux_insertAux {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → (a : α) → (x : List Nat) →
      (x ∈ wordsAux (insertAux cs c rest a) ↔ x = c :: rest ∨ x ∈ wordsAux cs)
  | [], c, rest, a, x => by simp [insertAux, wordsAux, words]
  | ([], t) :: ps, c, rest, a, x => by
      have h := mem_wordsAux_insertAux ps c rest a x
      simp only [insertAux, wordsAux, List.mem_append, h]
      simp only [or_left_comm]
  | (c' :: lbl, t) :: ps, c, rest, a, x => by
      by_cases hc : c' = c
      · subst hc
        obtain ⟨hl, hr, -⟩ := splitCommon_spec lbl rest
        simp only [insertAux, ↓reduceIte]
        rcases hs : splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
          rw [hs] at hl hr <;> simp only [List.append_nil] at hl hr <;> subst hl hr
        · have h := mem_words_insert t [] a
          simp only [wordsAux, List.mem_append, List.mem_map]
          constructor
          · rintro (⟨u, hu, rfl⟩ | hx)
            · rcases (h u).1 hu with rfl | hu
              · exact Or.inl (by simp)
              · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
            · exact Or.inr (Or.inr hx)
          · rintro (rfl | ⟨u, hu, rfl⟩ | hx)
            · exact Or.inl ⟨[], (h []).2 (Or.inl rfl), by simp⟩
            · exact Or.inl ⟨u, (h u).2 (Or.inr hu), rfl⟩
            · exact Or.inr hx
        · have h := mem_words_insert t (f :: kr) a
          simp only [wordsAux, List.mem_append, List.mem_map]
          constructor
          · rintro (⟨u, hu, rfl⟩ | hx)
            · rcases (h u).1 hu with rfl | hu
              · exact Or.inl (by simp)
              · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
            · exact Or.inr (Or.inr hx)
          · rintro (rfl | ⟨u, hu, rfl⟩ | hx)
            · exact Or.inl ⟨f :: kr, (h _).2 (Or.inl rfl), by simp⟩
            · exact Or.inl ⟨u, (h u).2 (Or.inr hu), rfl⟩
            · exact Or.inr hx
        · simp [wordsAux, words, List.mem_map]
        · simp [wordsAux, words, List.mem_map, or_left_comm]
      · simp only [insertAux, hc, ↓reduceIte, wordsAux, List.mem_append,
          mem_wordsAux_insertAux ps c rest a x]
        simp only [or_left_comm]

end

/-- **`insert` keeps the invariant**: `distinctFirstLetters_insert`,
`branchesUnlessWordEnds_insert` and `noEmptyBranches_insert`. -/
theorem valid_insert {α : Type} {t : Patricia α} (k : List Nat) (a : α) (h : Valid t) :
    Valid (insert t k a) :=
  ⟨distinctFirstLetters_insert t k a h.distinctFirstLetters,
    branchesUnlessWordEnds_insert k a h.branchesUnlessWordEnds,
    noEmptyBranches_insert t k a h.noEmptyBranches⟩

end Patricia

end AlgoDesign.Strings
