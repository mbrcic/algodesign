/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Build

/-!
# Patricia: sorted child lists

`insertSorted` models the Rust's `Patricia::insert`, which keeps each child list sorted by first
symbol (`SortedHeads`). It builds the sorted form of the same tree (`ofListSorted_eq_ofTrie`),
sorting changes no lookup (`get_sortTree`), and it discharges `InsertSpec` on the trees it builds
(`insertSpec_insertSorted`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-! ## Sorted child order

`insertSorted` writes the binary search as an ordered scan that stops at the first label not below
the key's symbol; `sortTree` sorts every child list by first symbol. -/

/-- The first symbol of an edge's label; an empty label reads as `0`. -/
def headSym {α : Type} (e : List Nat × Patricia α) : Nat := e.1.headD 0

/-- Edges ordered by the first symbol of their label. -/
def HeadLe {α : Type} (e f : List Nat × Patricia α) : Prop := headSym e ≤ headSym f

instance {α : Type} : DecidableRel (HeadLe (α := α)) := fun _ _ => Nat.decLe _ _

instance {α : Type} : Std.Total (HeadLe (α := α)) := ⟨fun _ _ => Nat.le_total _ _⟩

instance {α : Type} : IsTrans (List Nat × Patricia α) HeadLe :=
  ⟨fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂⟩

mutual

/-- In every child list, first symbols strictly ascend: what a binary search by first symbol
needs. Not part of `Valid`. -/
def SortedHeads {α : Type} : Patricia α → Prop
  | .node _ cs => cs.Pairwise (fun e f => headSym e < headSym f) ∧ SortedHeadsAux cs

/-- `SortedHeads` for every subtree in a child list. -/
def SortedHeadsAux {α : Type} : List (List Nat × Patricia α) → Prop
  | [] => True
  | p :: rest => SortedHeads p.2 ∧ SortedHeadsAux rest

end

/-- Put an edge before the first edge whose label does not begin below its own. Mathlib's
`List.orderedInsert` for `HeadLe` (`insertByHead_eq`), written out so the kernel can evaluate
it. -/
def insertByHead {α : Type} (e : List Nat × Patricia α) :
    List (List Nat × Patricia α) → List (List Nat × Patricia α)
  | [] => [e]
  | f :: l => if headSym e ≤ headSym f then e :: f :: l else f :: insertByHead e l

/-- Insertion sort by first symbol: `List.insertionSort HeadLe` (`sortByHead_eq`). -/
def sortByHead {α : Type} : List (List Nat × Patricia α) → List (List Nat × Patricia α)
  | [] => []
  | e :: l => insertByHead e (sortByHead l)

theorem insertByHead_eq {α : Type} (e : List Nat × Patricia α) :
    (l : List (List Nat × Patricia α)) → insertByHead e l = l.orderedInsert HeadLe e
  | [] => by simp [insertByHead]
  | f :: l => by
      rw [List.orderedInsert_cons, insertByHead]
      by_cases h : headSym e ≤ headSym f
      · have h' : HeadLe e f := h
        simp only [h, h', ↓reduceIte]
      · have h' : ¬ HeadLe e f := h
        simp only [h, h', ↓reduceIte, insertByHead_eq e l]

theorem sortByHead_eq {α : Type} :
    (l : List (List Nat × Patricia α)) → sortByHead l = l.insertionSort HeadLe
  | [] => by rw [List.insertionSort_nil]; rfl
  | e :: l => by rw [List.insertionSort_cons, sortByHead, sortByHead_eq l, insertByHead_eq]

mutual

/-- Sort every child list by the first symbol of its labels: the Rust's representation of the
same tree. -/
def sortTree {α : Type} : Patricia α → Patricia α
  | .node v cs => .node v (sortByHead (sortTreeAux cs))

/-- `sortTree` below every edge of a child list, labels untouched. -/
def sortTreeAux {α : Type} : List (List Nat × Patricia α) → List (List Nat × Patricia α)
  | [] => []
  | p :: rest => (p.1, sortTree p.2) :: sortTreeAux rest

end

mutual

/-- **The Rust's `Patricia::insert`**, child order included: `insert` with every child list kept
sorted by first symbol. A new leaf edge goes before the first label that begins above the key's
symbol, and a split node lists its two children in order. -/
def insertSorted {α : Type} : Patricia α → List Nat → α → Patricia α
  | .node _ cs, [], a => .node (some a) cs
  | .node v cs, c :: rest, a => .node v (insertSortedAux cs c rest a)

/-- `insertAux` for a sorted child list: the scan stops at the first label that does not begin
below `c`, which in a sorted list is where the Rust's binary search lands. -/
def insertSortedAux {α : Type} :
    List (List Nat × Patricia α) → Nat → List Nat → α → List (List Nat × Patricia α)
  | [], c, rest, a => [(c :: rest, .node (some a) [])]
  | ([], t) :: ps, c, rest, a => ([], t) :: insertSortedAux ps c rest a
  | (c' :: lbl, t) :: ps, c, rest, a =>
      if c' = c then
        match splitCommon lbl rest with
        | (_, [], keyRest) => (c' :: lbl, insertSorted t keyRest a) :: ps
        | (pre, d :: lr, []) => (c :: pre, .node (some a) [(d :: lr, t)]) :: ps
        | (pre, d :: lr, f :: kr) =>
            (c :: pre, .node none (if d < f then [(d :: lr, t), (f :: kr, .node (some a) [])]
              else [(f :: kr, .node (some a) []), (d :: lr, t)])) :: ps
      else if c < c' then (c :: rest, .node (some a) []) :: (c' :: lbl, t) :: ps
      else (c' :: lbl, t) :: insertSortedAux ps c rest a

end

/-- The tree the Rust's insert builds from a list of key/value pairs, starting from empty. -/
def ofListSorted {α : Type} (kvs : List (List Nat × α)) : Patricia α :=
  kvs.foldl (fun t p => insertSorted t p.1 p.2) (.node none [])

/-- `insertSortedAux`'s work at the edge it changes. -/
private def splitEdgeSorted {α : Type} (c : Nat) (lbl : List Nat) (t : Patricia α)
    (rest : List Nat) (a : α) : List Nat × Patricia α :=
  match splitCommon lbl rest with
  | (_, [], keyRest) => (c :: lbl, insertSorted t keyRest a)
  | (pre, d :: lr, []) => (c :: pre, .node (some a) [(d :: lr, t)])
  | (pre, d :: lr, f :: kr) =>
      (c :: pre, .node none (if d < f then [(d :: lr, t), (f :: kr, .node (some a) [])]
        else [(f :: kr, .node (some a) []), (d :: lr, t)]))

/-- The edge change `insert` makes, applied to every edge whose label begins with `c`. -/
private def edgeIns {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    List Nat × Patricia α → List Nat × Patricia α
  | (c' :: lbl, t) => if c' = c then splitEdge c' lbl t rest a else (c' :: lbl, t)
  | ([], t) => ([], t)

/-- The same for `insertSorted`. -/
private def edgeInsS {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    List Nat × Patricia α → List Nat × Patricia α
  | (c' :: lbl, t) => if c' = c then splitEdgeSorted c' lbl t rest a else (c' :: lbl, t)
  | ([], t) => ([], t)

private theorem headSym_splitEdgeSorted {α : Type} (c : Nat) (lbl : List Nat) (t : Patricia α)
    (rest : List Nat) (a : α) : headSym (splitEdgeSorted c lbl t rest a) = c := by
  simp only [splitEdgeSorted]
  rcases splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;> rfl

private theorem headSym_edgeInsS {α : Type} (c : Nat) (rest : List Nat) (a : α)
    (e : List Nat × Patricia α) : headSym (edgeInsS c rest a e) = headSym e := by
  match e with
  | (c' :: lbl, t) =>
      simp only [edgeInsS]
      split
      · rename_i h; rw [headSym_splitEdgeSorted, h]; rfl
      · rfl
  | ([], t) => rfl

/-- Sorting decides by first symbols only, so it commutes with any map that keeps them. -/
private theorem insertByHead_map {α : Type} (g : List Nat × Patricia α → List Nat × Patricia α)
    (hg : ∀ e, headSym (g e) = headSym e) (x : List Nat × Patricia α) :
    (l : List (List Nat × Patricia α)) → insertByHead (g x) (l.map g) = (insertByHead x l).map g
  | [] => rfl
  | f :: l => by
      simp only [List.map_cons, insertByHead, hg]
      split
      · rfl
      · simp only [List.map_cons, insertByHead_map g hg x l]

private theorem sortByHead_map {α : Type} (g : List Nat × Patricia α → List Nat × Patricia α)
    (hg : ∀ e, headSym (g e) = headSym e) :
    (l : List (List Nat × Patricia α)) → sortByHead (l.map g) = (sortByHead l).map g
  | [] => rfl
  | x :: l => by
      simp only [List.map_cons, sortByHead, sortByHead_map g hg l, insertByHead_map g hg]

/-- Two insertions under different first symbols can be made in either order. -/
private theorem insertByHead_comm {α : Type} (x y : List Nat × Patricia α)
    (h : headSym x ≠ headSym y) : (l : List (List Nat × Patricia α)) →
      insertByHead y (insertByHead x l) = insertByHead x (insertByHead y l)
  | [] => by
      by_cases hxy : headSym x ≤ headSym y <;> by_cases hyx : headSym y ≤ headSym x <;>
        simp only [insertByHead, hxy, hyx, ↓reduceIte] <;> omega
  | b :: l => by
      have ih := insertByHead_comm x y h l
      by_cases hx : headSym x ≤ headSym b <;> by_cases hy : headSym y ≤ headSym b <;>
        by_cases hxy : headSym x ≤ headSym y <;> by_cases hyx : headSym y ≤ headSym x <;>
        simp only [insertByHead, hx, hy, hxy, hyx, ↓reduceIte, ih] <;> omega

/-- Appending an edge under a new first symbol and sorting is inserting it into the sort. -/
private theorem sortByHead_append_single {α : Type} (x : List Nat × Patricia α) :
    (l : List (List Nat × Patricia α)) → (∀ e ∈ l, headSym e ≠ headSym x) →
      sortByHead (l ++ [x]) = insertByHead x (sortByHead l)
  | [], _ => rfl
  | y :: l, h => by
      simp only [List.cons_append, sortByHead]
      rw [sortByHead_append_single x l (fun e he => h e (List.mem_cons_of_mem _ he))]
      exact insertByHead_comm x y (fun e => h y (List.mem_cons_self ..) e.symm) _

/-- `insertAux` on a child list with distinct heads: the edge beginning with `c` changes, or, if
there is none, a leaf edge is appended. -/
private theorem insertAux_eq {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    (cs : List (List Nat × Patricia α)) → (cs.map (·.1.head?)).Nodup →
      insertAux cs c rest a = if some c ∈ cs.map (·.1.head?) then cs.map (edgeIns c rest a)
        else cs ++ [(c :: rest, .node (some a) [])]
  | [], _ => rfl
  | ([], t) :: ps, h => by
      have ih := insertAux_eq c rest a ps (List.nodup_cons.mp h).2
      simp only [insertAux, ih, List.map_cons, List.head?_nil, List.mem_cons, reduceCtorEq,
        false_or]
      split <;> rfl
  | (c' :: lbl, t) :: ps, h => by
      have ih := insertAux_eq c rest a ps (List.nodup_cons.mp h).2
      by_cases hc : c' = c
      · subst hc
        have hno : some c' ∉ ps.map (·.1.head?) := by simpa using (List.nodup_cons.mp h).1
        have hid : ps.map (edgeIns c' rest a) = ps := by
          conv_rhs => rw [← List.map_id ps]
          refine List.map_congr_left (fun e he => ?_)
          rcases e with ⟨_ | ⟨c'', lbl'⟩, t'⟩
          · rfl
          · have : c'' ≠ c' := fun hh => hno (List.mem_map.mpr ⟨_, he, by simp [hh]⟩)
            simp [edgeIns, this]
        simp only [List.map_cons, List.head?_cons, List.mem_cons, true_or, ↓reduceIte,
          insertAux_cons_self, edgeIns, hid]
      · have hc' : ¬ c = c' := fun e => hc e.symm
        simp only [insertAux, hc, ↓reduceIte, ih, List.map_cons, List.head?_cons, List.mem_cons,
          Option.some.injEq, hc', false_or]
        split <;> simp [edgeIns, hc]

/-- `insertSortedAux` on a child list sorted by first symbol, with non-empty labels and distinct
heads: the edge beginning with `c` changes, or, if there is none, a leaf edge is inserted at its
sorted place. -/
private theorem insertSortedAux_eq {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    (L : List (List Nat × Patricia α)) → L.Pairwise HeadLe → (L.map (·.1.head?)).Nodup →
      (∀ e ∈ L, e.1 ≠ []) →
      insertSortedAux L c rest a = if some c ∈ L.map (·.1.head?) then L.map (edgeInsS c rest a)
        else insertByHead (c :: rest, .node (some a) []) L
  | [], _, _, _ => rfl
  | ([], _) :: _, _, _, hl => absurd rfl (hl _ (List.mem_cons_self ..))
  | (c' :: lbl, t) :: ps, hs, hn, hl => by
      have ih := insertSortedAux_eq c rest a ps (List.pairwise_cons.mp hs).2
        (List.nodup_cons.mp hn).2 (fun e he => hl e (List.mem_cons_of_mem _ he))
      by_cases hc : c' = c
      · subst hc
        have hno : some c' ∉ ps.map (·.1.head?) := by simpa using (List.nodup_cons.mp hn).1
        have hid : ps.map (edgeInsS c' rest a) = ps := by
          conv_rhs => rw [← List.map_id ps]
          refine List.map_congr_left (fun e he => ?_)
          rcases e with ⟨_ | ⟨c'', lbl'⟩, t'⟩
          · rfl
          · have : c'' ≠ c' := fun hh => hno (List.mem_map.mpr ⟨_, he, by simp [hh]⟩)
            simp [edgeInsS, this]
        simp only [insertSortedAux, ↓reduceIte, List.map_cons, List.head?_cons, List.mem_cons,
          true_or, edgeInsS, hid, splitEdgeSorted]
        generalize splitCommon lbl rest = s
        rcases s with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;> rfl
      · have hc' : ¬ c = c' := fun e => hc e.symm
        have hhd : headSym ((c' :: lbl, t) : List Nat × Patricia α) = c' := rfl
        have hhc : headSym ((c :: rest, .node (some a) []) : List Nat × Patricia α) = c := rfl
        by_cases hlt : c < c'
        · -- every later head is at least `c'`, so none is `c`
          have hno : some c ∉ ps.map (·.1.head?) := by
            intro hm
            obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
            have hle : c' ≤ headSym e := (List.pairwise_cons.mp hs).1 e he
            rcases e with ⟨_ | ⟨c'', lbl'⟩, t'⟩
            · simp at hh
            · simp only [List.head?_cons, Option.some.injEq] at hh
              have : headSym ((c'' :: lbl', t') : List Nat × Patricia α) = c'' := rfl
              omega
          have hle : c ≤ c' := Nat.le_of_lt hlt
          simp only [insertSortedAux, hc, hlt, ↓reduceIte, List.map_cons, List.head?_cons,
            List.mem_cons, Option.some.injEq, hc', false_or, hno, insertByHead, hhd, hhc, hle]
        · have hle : ¬ c ≤ c' := by omega
          simp only [insertSortedAux, hc, hlt, ↓reduceIte, ih, List.map_cons, List.head?_cons,
            List.mem_cons, Option.some.injEq, hc', false_or, insertByHead, hhd, hhc, hle]
          split <;> simp [edgeInsS, hc]

private theorem map_fst_sortTreeAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (sortTreeAux cs).map (·.1) = cs.map (·.1)
  | [] => rfl
  | _ :: rest => by simp [sortTreeAux, map_fst_sortTreeAux rest]

private theorem sortTreeAux_append {α : Type} (x : List Nat × Patricia α) :
    (cs : List (List Nat × Patricia α)) →
      sortTreeAux (cs ++ [x]) = sortTreeAux cs ++ [(x.1, sortTree x.2)]
  | [] => rfl
  | _ :: rest => by simp [sortTreeAux, sortTreeAux_append x rest]

mutual

private theorem sortTree_insert_aux {α : Type} : (t : Patricia α) → (k : List Nat) → (a : α) →
    NoEmptyBranches t → DistinctFirstLetters t →
      sortTree (insert t k a) = insertSorted (sortTree t) k a
  | .node _ _, [], _, _, _ => rfl
  | .node v cs, c :: rest, a, hp, ⟨hn, hd⟩ => by
      have hlab := NoEmptyBranchesChildren.labels_ne (cs := cs) hp
      have hperm : (sortByHead (sortTreeAux cs)).Perm (sortTreeAux cs) := by
        rw [sortByHead_eq]; exact List.perm_insertionSort HeadLe _
      have hheads : (sortTreeAux cs).map (·.1.head?) = cs.map (·.1.head?) := by
        have := congrArg (List.map List.head?) (map_fst_sortTreeAux cs)
        simpa [List.map_map, Function.comp_def] using this
      have hsorted : (sortByHead (sortTreeAux cs)).Pairwise HeadLe := by
        rw [sortByHead_eq]; exact List.pairwise_insertionSort HeadLe _
      have hn' : ((sortByHead (sortTreeAux cs)).map (·.1.head?)).Nodup :=
        (hperm.map _).nodup_iff.mpr (hheads ▸ hn)
      have hfst : ∀ e ∈ sortTreeAux cs, ∃ e' ∈ cs, e'.1 = e.1 := by
        intro e he
        have : e.1 ∈ (sortTreeAux cs).map (·.1) := List.mem_map.mpr ⟨e, he, rfl⟩
        rw [map_fst_sortTreeAux] at this
        exact List.mem_map.mp this
      have hlab' : ∀ e ∈ sortByHead (sortTreeAux cs), e.1 ≠ [] := by
        intro e he
        obtain ⟨e', he', h⟩ := hfst e (hperm.mem_iff.mp he)
        rw [← h]; exact hlab e' he'
      have hmem : (some c ∈ (sortByHead (sortTreeAux cs)).map (·.1.head?))
          ↔ some c ∈ cs.map (·.1.head?) := by
        rw [← hheads]; exact (hperm.map _).mem_iff
      change Patricia.node v (sortByHead (sortTreeAux (insertAux cs c rest a)))
        = Patricia.node v (insertSortedAux (sortByHead (sortTreeAux cs)) c rest a)
      rw [insertAux_eq c rest a cs hn, insertSortedAux_eq c rest a _ hsorted hn' hlab']
      by_cases hno : some c ∈ cs.map (·.1.head?)
      · have hno' := hmem.mpr hno
        simp only [hno, hno', ↓reduceIte]
        rw [sortTreeAux_map_edgeIns c rest a cs hp hd,
          sortByHead_map _ (headSym_edgeInsS c rest a)]
      · have hno' : ¬ some c ∈ (sortByHead (sortTreeAux cs)).map (·.1.head?) :=
          fun h => hno (hmem.mp h)
        simp only [hno, hno', ↓reduceIte]
        rw [sortTreeAux_append, sortByHead_append_single]
        · rfl
        · intro e he hh
          obtain ⟨e', he', h⟩ := hfst e he
          apply hno
          refine List.mem_map.mpr ⟨e', he', ?_⟩
          have hne := hlab e' he'
          rcases e' with ⟨_ | ⟨x, xs⟩, t'⟩
          · exact absurd rfl hne
          · rcases e with ⟨l, u⟩
            simp only at h
            subst h
            exact congrArg some hh

/-- The child-list step of `sortTree_insert`: sorting below each edge commutes with the edge
change, one edge at a time. -/
private theorem sortTreeAux_map_edgeIns {α : Type} (c : Nat) (rest : List Nat) (a : α) :
    (cs : List (List Nat × Patricia α)) → NoEmptyBranchesChildren cs →
      DistinctFirstLettersChildren cs →
        sortTreeAux (cs.map (edgeIns c rest a)) = (sortTreeAux cs).map (edgeInsS c rest a)
  | [], _, _ => rfl
  | ([], t) :: ps, ⟨_, _, h3⟩, ⟨_, h5⟩ => by
      simp only [List.map_cons, edgeIns, sortTreeAux, edgeInsS,
        sortTreeAux_map_edgeIns c rest a ps h3 h5]
  | (c' :: lbl, t) :: ps, ⟨_, h2, h3⟩, ⟨h4, h5⟩ => by
      simp only [List.map_cons, sortTreeAux, sortTreeAux_map_edgeIns c rest a ps h3 h5]
      congr 1
      simp only [edgeIns, edgeInsS]
      split
      · rename_i hc
        subst hc
        obtain ⟨-, -, hne⟩ := splitCommon_spec lbl rest
        simp only [splitEdge, splitEdgeSorted]
        rcases hs : splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
          rw [hs] at hne
        · simp only [sortTree_insert_aux t [] a h2 h4]
        · simp only [sortTree_insert_aux t (f :: kr) a h2 h4]
        · rfl
        · have hdf := hne d f lr kr rfl rfl
          by_cases hlt : d < f
          · have : d ≤ f := Nat.le_of_lt hlt
            simp only [hlt, ↓reduceIte, sortTree, sortTreeAux, sortByHead, insertByHead,
              headSym, List.headD_cons, this]
          · have : ¬ d ≤ f := by omega
            simp only [hlt, ↓reduceIte, sortTree, sortTreeAux, sortByHead, insertByHead,
              headSym, List.headD_cons, this]
      · rfl

end

/-- **The Rust's insert is this module's insert, sorted.** On every tree with non-empty labels and
distinct heads (`NoEmptyBranches` and `DistinctFirstLetters`, both of which `insert` keeps),
inserting with the child lists kept sorted gives the sort of inserting in creation order. -/
theorem sortTree_insert {α : Type} (t : Patricia α) (k : List Nat) (a : α)
    (hp : NoEmptyBranches t) (hd : DistinctFirstLetters t) :
    sortTree (insert t k a) = insertSorted (sortTree t) k a :=
  sortTree_insert_aux t k a hp hd

private theorem sortTree_foldl {α : Type} :
    (kvs : List (List Nat × α)) → (t : Patricia α) → NoEmptyBranches t → DistinctFirstLetters t →
      sortTree (kvs.foldl (fun p q => insert p q.1 q.2) t)
        = kvs.foldl (fun p q => insertSorted p q.1 q.2) (sortTree t)
  | [], _, _, _ => rfl
  | q :: qs, t, hp, hd => by
      simp only [List.foldl_cons]
      rw [sortTree_foldl qs _ (noEmptyBranches_insert t q.1 q.2 hp)
          (distinctFirstLetters_insert t q.1 q.2 hd),
        sortTree_insert t q.1 q.2 hp hd]

/-- **From empty, the Rust's construction is the sort of this module's.** -/
theorem ofListSorted_eq {α : Type} (kvs : List (List Nat × α)) :
    ofListSorted kvs = sortTree (ofList kvs) :=
  (sortTree_foldl kvs (.node none []) trivial ⟨List.nodup_nil, trivial⟩).symm

/-- **The Rust's incremental insert builds the sorted compression of the trie** the same
insertions build. -/
theorem ofListSorted_eq_ofTrie {α : Type} (kvs : List (List Nat × α)) :
    ofListSorted kvs
      = sortTree (ofTrie (kvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty)) := by
  rw [ofListSorted_eq, ofList_eq_ofTrie]

/-! ### The sort keeps the invariant, and makes the order
`sortTree` permutes every child list and recurses into every subtree, so it keeps every piece of
`Valid`; on a tree with no empty branch and distinct heads it sorts strictly
(`sortedHeads_sortTree`); and on a tree already sorted it changes nothing (`sortTree_eq_self`).
Together with `sortTree_insert` these give the Rust's insert the invariant and the order
(`valid_insertSorted`). -/

/-- `DistinctFirstLettersChildren`, read edge by edge. -/
theorem distinctFirstLettersChildren_iff {α : Type} :
    (cs : List (List Nat × Patricia α)) →
      DistinctFirstLettersChildren cs ↔ ∀ e ∈ cs, DistinctFirstLetters e.2
  | [] => by simp [DistinctFirstLettersChildren]
  | p :: rest => by
      simp only [DistinctFirstLettersChildren, distinctFirstLettersChildren_iff rest, List.mem_cons,
          forall_eq_or_imp]

private theorem sortedHeadsAux_iff {α : Type} :
    (cs : List (List Nat × Patricia α)) →
      SortedHeadsAux cs ↔ ∀ e ∈ cs, SortedHeads e.2
  | [] => by simp [SortedHeadsAux]
  | p :: rest => by
      simp only [SortedHeadsAux, sortedHeadsAux_iff rest, List.mem_cons, forall_eq_or_imp]

/-- Sorting a child list permutes it. -/
private theorem perm_sortByHead {α : Type} (cs : List (List Nat × Patricia α)) :
    (sortByHead cs).Perm cs := by
  rw [sortByHead_eq]; exact List.perm_insertionSort HeadLe _

private theorem length_sortTreeAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (sortTreeAux cs).length = cs.length
  | [] => rfl
  | _ :: rest => by simp [sortTreeAux, length_sortTreeAux rest]

private theorem heads_sortTreeAux {α : Type} (cs : List (List Nat × Patricia α)) :
    (sortTreeAux cs).map (·.1.head?) = cs.map (·.1.head?) := by
  have := congrArg (List.map List.head?) (map_fst_sortTreeAux cs)
  simpa [List.map_map, Function.comp_def] using this

mutual

/-- The node half of `branchesUnlessWordEnds_sortTree`. -/
private theorem branchesUnlessWordEndsNode_sortTree {α : Type} :
    (t : Patricia α) → BranchesUnlessWordEndsNode t → BranchesUnlessWordEndsNode (sortTree t)
  | .node v cs, ⟨hv, h⟩ => by
      refine ⟨?_, (branchesUnlessWordEndsChildren_iff _).mpr fun e he =>
        ((branchesUnlessWordEndsChildren_iff _).mp
          (branchesUnlessWordEndsChildren_sortTreeAux cs h)) e
          ((perm_sortByHead _).mem_iff.mp he)⟩
      rwa [(perm_sortByHead _).length_eq, length_sortTreeAux]

/-- The child-list half of `branchesUnlessWordEnds_sortTree`. -/
private theorem branchesUnlessWordEndsChildren_sortTreeAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → BranchesUnlessWordEndsChildren cs →
      BranchesUnlessWordEndsChildren (sortTreeAux cs)
  | [], _ => trivial
  | p :: rest, ⟨h2, h3⟩ =>
      ⟨branchesUnlessWordEndsNode_sortTree p.2 h2,
        branchesUnlessWordEndsChildren_sortTreeAux rest h3⟩

end

/-- **Sorting keeps `BranchesUnlessWordEnds`**: it permutes child lists, so every node keeps its
value and its number of children. -/
theorem branchesUnlessWordEnds_sortTree {α : Type} :
    (t : Patricia α) → BranchesUnlessWordEnds t → BranchesUnlessWordEnds (sortTree t)
  | .node _ cs, h => (branchesUnlessWordEndsChildren_iff _).mpr fun e he =>
      ((branchesUnlessWordEndsChildren_iff _).mp
        (branchesUnlessWordEndsChildren_sortTreeAux cs h)) e
        ((perm_sortByHead _).mem_iff.mp he)

mutual

/-- **Sorting keeps `NoEmptyBranches`**: it permutes child lists and keeps every label. -/
theorem noEmptyBranches_sortTree {α : Type} :
    (t : Patricia α) → NoEmptyBranches t → NoEmptyBranches (sortTree t)
  | .node _ cs, h => (noEmptyBranchesChildren_iff _).mpr fun e he =>
      ((noEmptyBranchesChildren_iff _).mp (noEmptyBranchesChildren_sortTreeAux cs h)) e
        ((perm_sortByHead _).mem_iff.mp he)

/-- The child-list half of `noEmptyBranches_sortTree`. -/
theorem noEmptyBranchesChildren_sortTreeAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → NoEmptyBranchesChildren cs →
      NoEmptyBranchesChildren (sortTreeAux cs)
  | [], _ => trivial
  | p :: rest, ⟨h1, h2, h3⟩ =>
      ⟨h1, noEmptyBranches_sortTree p.2 h2, noEmptyBranchesChildren_sortTreeAux rest h3⟩

end

mutual

/-- **Sorting keeps `DistinctFirstLetters`**: a permuted child list has the same heads. -/
theorem distinctFirstLetters_sortTree {α : Type} :
    (t : Patricia α) → DistinctFirstLetters t → DistinctFirstLetters (sortTree t)
  | .node _ cs, ⟨hn, h⟩ =>
      ⟨(((perm_sortByHead _).map _).nodup_iff).mpr (heads_sortTreeAux cs ▸ hn),
        (distinctFirstLettersChildren_iff _).mpr fun e he =>
          ((distinctFirstLettersChildren_iff _).mp
            (distinctFirstLettersChildren_sortTreeAux cs h)) e
            ((perm_sortByHead _).mem_iff.mp he)⟩

/-- The child-list half of `distinctFirstLetters_sortTree`. -/
theorem distinctFirstLettersChildren_sortTreeAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → DistinctFirstLettersChildren cs →
      DistinctFirstLettersChildren (sortTreeAux cs)
  | [], _ => trivial
  | p :: rest, ⟨h1, h2⟩ => ⟨distinctFirstLetters_sortTree p.2 h1,
      distinctFirstLettersChildren_sortTreeAux rest h2⟩

end

/-- On a child list with non-empty labels and distinct heads, `HeadLe`'s `≤` is `<`. -/
private theorem pairwise_lt_of_le {α : Type} {cs : List (List Nat × Patricia α)}
    (hle : cs.Pairwise HeadLe) (hn : (cs.map (·.1.head?)).Nodup) (hlab : ∀ e ∈ cs, e.1 ≠ []) :
    cs.Pairwise (fun e f => headSym e < headSym f) := by
  have hne : cs.Pairwise (fun e f => e.1.head? ≠ f.1.head?) := List.pairwise_map.mp hn
  refine (hle.and hne).imp_of_mem fun {e f} he hf ⟨h1, h2⟩ => ?_
  rcases e with ⟨_ | ⟨x, xs⟩, u⟩
  · exact absurd rfl (hlab _ he)
  rcases f with ⟨_ | ⟨y, ys⟩, w⟩
  · exact absurd rfl (hlab _ hf)
  simp only [HeadLe, headSym, List.headD_cons, List.head?_cons, ne_eq, Option.some.injEq] at h1 h2 ⊢
  omega

mutual

/-- **Sorting a `Valid` tree sorts it strictly**: insertion sort leaves heads in `≤` order, and on
non-empty labels with distinct heads that order is `<`. -/
theorem sortedHeads_sortTree {α : Type} :
    (t : Patricia α) → NoEmptyBranches t → DistinctFirstLetters t → SortedHeads (sortTree t)
  | .node _ cs, hp, ⟨hn, hd⟩ => by
      have hperm := perm_sortByHead (sortTreeAux cs)
      have hsorted : (sortByHead (sortTreeAux cs)).Pairwise HeadLe := by
        rw [sortByHead_eq]; exact List.pairwise_insertionSort HeadLe _
      have hn' : ((sortByHead (sortTreeAux cs)).map (·.1.head?)).Nodup :=
        (hperm.map _).nodup_iff.mpr (heads_sortTreeAux cs ▸ hn)
      have hlab : ∀ e ∈ sortByHead (sortTreeAux cs), e.1 ≠ [] := fun e he =>
        ((noEmptyBranchesChildren_iff _).mp (noEmptyBranchesChildren_sortTreeAux cs hp) e
          (hperm.mem_iff.mp he)).1
      exact ⟨pairwise_lt_of_le hsorted hn' hlab, (sortedHeadsAux_iff _).mpr fun e he =>
        ((sortedHeadsAux_iff _).mp (sortedHeadsAux_sortTreeAux cs hp hd)) e
          (hperm.mem_iff.mp he)⟩

/-- The child-list half of `sortedHeads_sortTree`. -/
theorem sortedHeadsAux_sortTreeAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → NoEmptyBranchesChildren cs →
      DistinctFirstLettersChildren cs → SortedHeadsAux (sortTreeAux cs)
  | [], _, _ => trivial
  | p :: rest, ⟨_, h2, h3⟩, ⟨h4, h5⟩ =>
      ⟨sortedHeads_sortTree p.2 h2 h4, sortedHeadsAux_sortTreeAux rest h3 h5⟩

end

mutual

/-- **Sorting a sorted tree changes nothing.** -/
theorem sortTree_eq_self {α : Type} : (t : Patricia α) → SortedHeads t → sortTree t = t
  | .node v cs, ⟨hs, h⟩ => by
      have hle : cs.Pairwise HeadLe := hs.imp Nat.le_of_lt
      simp only [sortTree, sortTreeAux_eq_self cs h, sortByHead_eq, hle.insertionSort_eq]

/-- The child-list half of `sortTree_eq_self`. -/
theorem sortTreeAux_eq_self {α : Type} :
    (cs : List (List Nat × Patricia α)) → SortedHeadsAux cs → sortTreeAux cs = cs
  | [], _ => rfl
  | p :: rest, ⟨h1, h2⟩ => by
      simp only [sortTreeAux, sortTree_eq_self p.2 h1, sortTreeAux_eq_self rest h2]

end

/-- **The Rust's insert keeps the invariant and the order**: on a sorted tree it is the sort of
`insert` (`sortTree_insert`), `insert` keeps `Valid` (`valid_insert`), and sorting keeps `Valid` and
makes the order (`distinctFirstLetters_sortTree`, `branchesUnlessWordEnds_sortTree`,
`noEmptyBranches_sortTree`, `sortedHeads_sortTree`). -/
theorem valid_insertSorted {α : Type} {u : Patricia α} (k : List Nat) (a : α) (h : Valid u)
    (hs : SortedHeads u) :
    Valid (insertSorted u k a) ∧ SortedHeads (insertSorted u k a) := by
  have he : insertSorted u k a = sortTree (insert u k a) :=
    calc insertSorted u k a = insertSorted (sortTree u) k a := by rw [sortTree_eq_self u hs]
      _ = sortTree (insert u k a) :=
        (sortTree_insert u k a h.noEmptyBranches h.distinctFirstLetters).symm
  have hv := valid_insert k a h
  rw [he]
  exact ⟨⟨distinctFirstLetters_sortTree _ hv.distinctFirstLetters,
      branchesUnlessWordEnds_sortTree _ hv.branchesUnlessWordEnds,
      noEmptyBranches_sortTree _ hv.noEmptyBranches⟩,
    sortedHeads_sortTree _ hv.noEmptyBranches hv.distinctFirstLetters⟩

private theorem valid_foldl_insert {α : Type} :
    (kvs : List (List Nat × α)) → (t : Patricia α) → Valid t →
      Valid (kvs.foldl (fun p q => insert p q.1 q.2) t)
  | [], _, h => h
  | q :: qs, _, h => valid_foldl_insert qs _ (valid_insert q.1 q.2 h)

/-- **From empty, the Rust's construction is `Valid` and sorted.** -/
theorem valid_ofListSorted {α : Type} (kvs : List (List Nat × α)) :
    Valid (ofListSorted kvs) ∧ SortedHeads (ofListSorted kvs) := by
  have hv : Valid (ofList kvs) := valid_foldl_insert kvs _ valid_empty
  rw [ofListSorted_eq]
  exact ⟨⟨distinctFirstLetters_sortTree _ hv.distinctFirstLetters,
      branchesUnlessWordEnds_sortTree _ hv.branchesUnlessWordEnds,
      noEmptyBranches_sortTree _ hv.noEmptyBranches⟩,
    sortedHeads_sortTree _ hv.noEmptyBranches hv.distinctFirstLetters⟩

/-! ### Lookup in the Rust's order

`get` reads the first child whose label begins with the key's next symbol, so on a child list
with distinct heads the order of the list cannot change its answer (`getAux_perm`). Sorting
below every edge therefore changes no lookup (`get_sortTree`), and with `sortTree_insert` that
turns this module's `InsertSpec` into the Rust insert's: on every tree the Rust's insert builds
from empty, and more generally on the sort of every tree with no empty branch and distinct heads,
the
inserted key maps to its value and every other key to what it mapped to before
(`insertSpec_insertSorted`). The self half needs no hypothesis at all (`get_insertSorted`). The
other half does: on a child list that is not sorted, the Rust's scan can stop before a later
sibling that begins with the key's symbol, file a second edge under that symbol in front of it,
and so hide it. -/

/-- On a child list whose labels begin with distinct symbols, `getAux` does not depend on the
order of the list. -/
private theorem getAux_perm {α : Type} {L L' : List (List Nat × Patricia α)} (h : L.Perm L')
    (hn : (L.map (·.1.head?)).Nodup) (c : Nat) (rest : List Nat) :
    getAux L c rest = getAux L' c rest := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
      have ih' := ih (List.nodup_cons.mp hn).2
      rcases x with ⟨_ | ⟨c', lbl⟩, t⟩
      · exact ih'
      · rw [getAux_cons_cons, getAux_cons_cons, ih']
  | swap x y l =>
      have hxy : y.1.head? ≠ x.1.head? := by
        intro he
        exact (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl he))
      rcases x with ⟨_ | ⟨cx, lx⟩, tx⟩ <;> rcases y with ⟨_ | ⟨cy, ly⟩, ty⟩
      · rfl
      · rfl
      · rfl
      · have hne : cy ≠ cx := fun h => hxy (by simp [h])
        rw [getAux_cons_cons, getAux_cons_cons, getAux_cons_cons, getAux_cons_cons]
        by_cases hy : cy = c <;> by_cases hx : cx = c
        · exact absurd (hy.trans hx.symm) hne
        · simp only [hy, hx, ↓reduceIte]
        · simp only [hy, hx, ↓reduceIte]
        · simp only [hy, hx, ↓reduceIte]
  | trans h₁ _ ih₁ ih₂ =>
      rw [ih₁ hn, ih₂ ((h₁.map _).nodup_iff.mp hn)]

mutual

/-- **Sorting changes no lookup.** On a tree with distinct heads, the Rust's representation
answers every key as this module's does. -/
theorem get_sortTree {α : Type} : (t : Patricia α) → DistinctFirstLetters t → (k : List Nat) →
    get (sortTree t) k = get t k
  | .node _ _, _, [] => rfl
  | .node _ cs, ⟨hn, hd⟩, c :: rest => by
      have hheads : (sortTreeAux cs).map (·.1.head?) = cs.map (·.1.head?) := by
        have := congrArg (List.map List.head?) (map_fst_sortTreeAux cs)
        simpa [List.map_map, Function.comp_def] using this
      have hperm : (sortTreeAux cs).Perm (sortByHead (sortTreeAux cs)) := by
        rw [sortByHead_eq]; exact (List.perm_insertionSort HeadLe _).symm
      change getAux (sortByHead (sortTreeAux cs)) c rest = getAux cs c rest
      rw [← getAux_perm hperm (hheads ▸ hn) c rest]
      exact getAux_sortTreeAux cs hd c rest

/-- The child-list half of `get_sortTree`: sorting below each edge, labels and order kept. -/
theorem getAux_sortTreeAux {α : Type} : (cs : List (List Nat × Patricia α)) →
    DistinctFirstLettersChildren cs → (c : Nat) → (rest : List Nat) →
    getAux (sortTreeAux cs) c rest = getAux cs c rest
  | [], _, _, _ => rfl
  | ([], _) :: ps, ⟨_, h⟩, c, rest => getAux_sortTreeAux ps h c rest
  | (c' :: lbl, t) :: ps, ⟨ht, h⟩, c, rest => by
      change (if c' = c then edge lbl (sortTree t) rest else getAux (sortTreeAux ps) c rest)
        = (if c' = c then edge lbl t rest else getAux ps c rest)
      simp only [edge, get_sortTree t ht, getAux_sortTreeAux ps h c rest]

end

mutual

/-- **The Rust's insert stores the key**, on every tree: the half of `InsertSpec` that, as for
`insert`, needs no invariant. The edge it changes or files first under the key's symbol is the
one `get` reads. -/
theorem get_insertSorted {α : Type} : (t : Patricia α) → (k : List Nat) → (a : α) →
    get (insertSorted t k a) k = some a
  | .node _ _, [], _ => rfl
  | .node _ cs, c :: rest, a => getAux_insertSortedAux cs c rest a

/-- The child-list half of `get_insertSorted`. -/
theorem getAux_insertSortedAux {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → (a : α) → getAux (insertSortedAux cs c rest a) c rest = some a
  | [], c, rest, a => by
      simp only [insertSortedAux, getAux_cons_cons, ↓reduceIte]
      exact edge_leaf_self rest a
  | ([], _) :: ps, c, rest, a => getAux_insertSortedAux ps c rest a
  | (c' :: lbl, t) :: ps, c, rest, a => by
      by_cases hc : c' = c
      · subst hc
        obtain ⟨hl, hr, hne⟩ := splitCommon_spec lbl rest
        simp only [insertSortedAux, ↓reduceIte]
        rcases hs : splitCommon lbl rest with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;>
          rw [hs] at hl hr hne <;> simp only [List.append_nil] at hl hr hne ⊢ <;> subst hl hr <;>
          simp only [getAux_cons_cons, ↓reduceIte]
        · rw [edge_self]
          exact get_insertSorted t [] a
        · rw [edge_prefix]
          exact get_insertSorted t (f :: kr) a
        · rw [edge_self]
          rfl
        · rw [edge_prefix]
          have hdf := hne d f lr kr rfl rfl
          change getAux _ f kr = some a
          by_cases hlt : d < f
          · simp only [hlt, ↓reduceIte, getAux_cons_cons, hdf]
            exact edge_leaf_self kr a
          · simp only [hlt, ↓reduceIte, getAux_cons_cons]
            exact edge_leaf_self kr a
      · by_cases hlt : c < c'
        · simp only [insertSortedAux, hc, hlt, ↓reduceIte, getAux_cons_cons]
          exact edge_leaf_self rest a
        · simp only [insertSortedAux, hc, hlt, ↓reduceIte, getAux_cons_cons]
          exact getAux_insertSortedAux ps c rest a

end

/-- **The Rust's insert discharges `InsertSpec`** on the sort of every tree with no empty branch
and distinct heads — the only trees it is ever handed, since it starts from the empty tree
(`insertSpec_insertSorted_ofListSorted`). Through `sortTree_insert` it is `insert` on the
unsorted tree, whose `InsertSpec` holds everywhere, and `get_sortTree` reads both trees
through the sort. -/
theorem insertSpec_insertSorted {α : Type} (u : Patricia α) (hp : NoEmptyBranches u)
    (hd : DistinctFirstLetters u) (k : List Nat) (a : α) :
    InsertSpec k a (sortTree u) (insertSorted (sortTree u) k a) := by
  intro k'
  rw [← sortTree_insert u k a hp hd, get_sortTree _ (distinctFirstLetters_insert u k a hd),
    get_sortTree u hd]
  exact insertSpec u k a k'

private theorem noEmptyBranches_distinctFirstLetters_ofList {α : Type} :
    (kvs : List (List Nat × α)) → (t : Patricia α) → NoEmptyBranches t →
      DistinctFirstLetters t →
        NoEmptyBranches (kvs.foldl (fun p q => insert p q.1 q.2) t) ∧
          DistinctFirstLetters (kvs.foldl (fun p q => insert p q.1 q.2) t)
  | [], _, hp, hd => ⟨hp, hd⟩
  | q :: qs, t, hp, hd =>
      noEmptyBranches_distinctFirstLetters_ofList qs _ (noEmptyBranches_insert t q.1 q.2 hp)
        (distinctFirstLetters_insert t q.1 q.2 hd)

/-- **`InsertSpec` for the Rust's insert on every tree it builds from empty.** -/
theorem insertSpec_insertSorted_ofListSorted {α : Type} (kvs : List (List Nat × α))
    (k : List Nat) (a : α) :
    InsertSpec k a (ofListSorted kvs) (insertSorted (ofListSorted kvs) k a) := by
  obtain ⟨hp, hd⟩ := noEmptyBranches_distinctFirstLetters_ofList kvs (.node none []) trivial
    ⟨List.nodup_nil, trivial⟩
  rw [ofListSorted_eq]
  exact insertSpec_insertSorted _ hp hd k a

/-- The words of a child list, block by block. -/
theorem wordsAux_eq_flatMap {α : Type} :
    (l : List (List Nat × Patricia α)) →
      wordsAux l = l.flatMap (fun e => (words e.2).map (e.1 ++ ·))
  | [] => rfl
  | e :: l => by simp [wordsAux, wordsAux_eq_flatMap l]

mutual

/-- Sorting the child lists reorders the key list and changes nothing else, so the Rust's tree
holds the key set this module's does. -/
theorem words_sortTree_perm {α : Type} : (t : Patricia α) → (sortTree t).words.Perm t.words
  | .node v cs => by
      simp only [sortTree, words]
      refine List.Perm.append_left _ ?_
      have hp : (sortByHead (sortTreeAux cs)).Perm (sortTreeAux cs) := by
        rw [sortByHead_eq]; exact List.perm_insertionSort HeadLe _
      refine List.Perm.trans ?_ (wordsAux_sortTreeAux_perm cs)
      rw [wordsAux_eq_flatMap, wordsAux_eq_flatMap]
      exact List.Perm.flatMap_right _ hp

/-- The child-list half of `words_sortTree_perm`. -/
theorem wordsAux_sortTreeAux_perm {α : Type} :
    (cs : List (List Nat × Patricia α)) → (wordsAux (sortTreeAux cs)).Perm (wordsAux cs)
  | [] => List.Perm.refl _
  | p :: rest => by
      simp only [sortTreeAux, wordsAux]
      exact ((words_sortTree_perm p.2).map _).append (wordsAux_sortTreeAux_perm rest)

end

end Patricia

end AlgoDesign.Strings
