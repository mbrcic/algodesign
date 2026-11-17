/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Remove
public import AlgoDesign.Strings.Patricia.Sorted
public import Mathlib.Data.Nat.Find
public import AlgoDesign.Strings.Trie.Query

/-!
# Patricia tree: the queries

What the chapter asks a Patricia tree, stated against what the tree holds.

- `longestPrefix` is the appendix's `longest_prefix`, the router's question: walk down from the
  root a whole label at a time, choosing the child by the next symbol, remembering the last node
  that holds a value, and stop when no label matches the rest of the key. On a `Valid` tree the
  answer is the longest stored key that is a prefix of the key, or `none` if no stored key is
  (`longestPrefix_eq_some_iff`, `longestPrefix_eq_none_iff`). Stated through `get` it holds on
  every tree (`longestPrefix_eq_some_iff_get`): the walk commits to a child by its first symbol
  exactly as `get` does.
- `keysWithPrefix` is `patricia.py`'s and `patricia.rs`'s `keys_with_prefix`: walk down whole labels
  while the prefix lasts (`prefixNode`); where the prefix ends inside a label, every key below
  that label begins with it, so the label is read whole and the walk stops at its child; then
  collect the subtree, children in byte order (`collect` over `sortTree`). On a `Valid` tree the
  answer is the stored words that begin with the prefix (`keysWithPrefix_perm`), strictly ascending
  (`keysWithPrefix_sorted`). The chapter prints the trie's version; this one adds the descent
  that ends inside a label.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-! ### `longest_prefix` -/

mutual

/-- The loop of `longest_prefix`, standing on a node with `rest` of the key still to read,
`consumed` symbols read, and `best` the length of the longest stored prefix met so far. With
nothing left to read it answers `best`; otherwise `lpGoAux` chooses the child. -/
def lpGo {α : Type} : Patricia α → List Nat → Nat → Option Nat → Option Nat
  | .node _ _, [], _, best => best
  | .node _ cs, c :: rest, consumed, best => lpGoAux cs c rest consumed best

/-- Choose the child whose label begins with `c`, as `getAux` does (an empty label begins with
nothing and is passed over). If no child does, or its whole label is not a prefix of the rest of
the key, the loop stops with `best`. Otherwise step down, count the label, and remember this node
if it holds a value. -/
def lpGoAux {α : Type} :
    List (List Nat × Patricia α) → Nat → List Nat → Nat → Option Nat → Option Nat
  | [], _, _, _, best => best
  | ([], _) :: ps, c, rest, consumed, best => lpGoAux ps c rest consumed best
  | (c' :: lbl, .node v cs) :: ps, c, rest, consumed, best =>
      if c' = c then
        if lbl.isPrefixOf rest then
          lpGo (.node v cs) (rest.drop lbl.length) (consumed + lbl.length + 1)
            (if v.isSome then some (consumed + lbl.length + 1) else best)
        else best
      else lpGoAux ps c rest consumed best

end

/-- **The appendix's `longest_prefix`.** Start at the root with `best` set if the root holds a
value (the empty key), run the loop over the whole key, and return the key cut to `best`. -/
def longestPrefix {α : Type} (t : Patricia α) (k : List Nat) : Option (List Nat) :=
  match t with
  | .node v cs => (lpGo (.node v cs) k 0 (if v.isSome then some 0 else none)).map (k.take ·)

/-- A stored key `j` symbols long begins `x`: `get` answers the first `j` symbols of `x`. -/
def Hit {α : Type} (t : Patricia α) (x : List Nat) (j : Nat) : Prop :=
  j ≤ x.length ∧ (get t (x.take j)).isSome = true

/-- A label begins the first `i` symbols of `r` exactly when it begins `r` and fits in `i`. -/
theorem isPrefixOf_take_iff (lbl r : List Nat) (i : Nat) :
    lbl.isPrefixOf (r.take i) = true ↔ lbl.isPrefixOf r = true ∧ lbl.length ≤ i := by
  simp only [List.isPrefixOf_iff_prefix]
  constructor
  · intro h
    exact ⟨h.trans (List.take_prefix i r), by
      have := h.length_le; simp at this; omega⟩
  · rintro ⟨h, hl⟩
    rw [List.prefix_iff_eq_take] at h ⊢
    rw [List.take_take, Nat.min_eq_left hl]
    exact h

mutual

/-- **The loop, over a child list.** If `i` is the longest cut of `rest` that `getAux` answers,
the loop returns `consumed + i + 1`; if `getAux` answers no cut, it returns `best`. -/
theorem lpGoAux_spec {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) → (consumed : Nat) →
      (best : Option Nat) →
      ((∀ i, i ≤ rest.length → (getAux cs c (rest.take i)).isSome = false) →
          lpGoAux cs c rest consumed best = best) ∧
      (∀ i, i ≤ rest.length → (getAux cs c (rest.take i)).isSome = true →
          (∀ i', i' ≤ rest.length → (getAux cs c (rest.take i')).isSome = true → i' ≤ i) →
          lpGoAux cs c rest consumed best = some (consumed + i + 1))
  | [], c, rest, consumed, best => by
      refine ⟨fun _ => by simp [lpGoAux], fun i _ h _ => by simp [getAux] at h⟩
  | ([], u) :: ps, c, rest, consumed, best => by
      simpa [lpGoAux, getAux] using lpGoAux_spec ps c rest consumed best
  | (c' :: lbl, .node v ds) :: ps, c, rest, consumed, best => by
      by_cases hc : c' = c
      · subst hc
        simp only [lpGoAux, getAux, ↓reduceIte]
        by_cases hpre : lbl.isPrefixOf rest = true
        · simp only [hpre, ↓reduceIte]
          have hL : lbl.length ≤ rest.length := by
            have := (List.isPrefixOf_iff_prefix.mp hpre).length_le; omega
          -- the cut `i` of `rest` is answered exactly when `lbl` fits and the child answers the
          -- cut `i - |lbl|` of what follows the label
          have hcut : ∀ i, i ≤ rest.length →
              ((if lbl.isPrefixOf (rest.take i) then
                  get (.node v ds) ((rest.take i).drop lbl.length) else none).isSome = true ↔
                lbl.length ≤ i ∧ Hit (.node v ds) (rest.drop lbl.length) (i - lbl.length)) := by
            intro i hi
            have key := isPrefixOf_take_iff lbl rest i
            by_cases hli : lbl.length ≤ i
            · have hp : lbl.isPrefixOf (rest.take i) = true := key.mpr ⟨hpre, hli⟩
              simp only [hp, ↓reduceIte, Hit, List.length_drop, hli, true_and]
              rw [List.drop_take]
              constructor
              · intro h; exact ⟨by omega, h⟩
              · intro h; exact h.2
            · have hp : lbl.isPrefixOf (rest.take i) = false := by
                cases h : lbl.isPrefixOf (rest.take i)
                · rfl
                · exact absurd (key.mp h).2 hli
              simp [hp, hli]
          obtain ⟨hnone, hsome⟩ := lpGo_spec (.node v ds) (rest.drop lbl.length)
            (consumed + lbl.length + 1)
            (if v.isSome then some (consumed + lbl.length + 1) else best)
          have hit0 : Hit (.node v ds) (rest.drop lbl.length) 0 ↔ v.isSome = true := by
            simp [Hit, get]
          refine ⟨fun hno => ?_, fun i hi hhit hmax => ?_⟩
          · -- no cut answered: so no cut of what follows the label, and no value on the child
            have hall : ∀ j, Hit (.node v ds) (rest.drop lbl.length) j → False := by
              intro j hj
              have hj' := hj.1
              simp only [List.length_drop] at hj'
              have := (hcut (lbl.length + j) (by omega)).mpr
                ⟨by omega, by simpa using hj⟩
              rw [hno _ (by omega)] at this
              exact Bool.false_ne_true this
            have hv : v.isSome = false := by
              cases h : v.isSome
              · rfl
              · exact (hall 0 (hit0.mpr h)).elim
            simpa [hv] using hnone (fun j hj => (hall j hj).elim)
          · obtain ⟨hli, hhit'⟩ := (hcut i hi).mp hhit
            have hmax' : ∀ j', Hit (.node v ds) (rest.drop lbl.length) j' →
                j' ≤ i - lbl.length := by
              intro j' hj'
              have hj'' := hj'.1
              simp only [List.length_drop] at hj''
              have := hmax (lbl.length + j') (by omega)
                ((hcut (lbl.length + j') (by omega)).mpr ⟨by omega, by simpa using hj'⟩)
              omega
            by_cases h1 : 1 ≤ i - lbl.length
            · rw [hsome (i - lbl.length) h1 hhit' hmax']
              congr 1
              omega
            · have hi0 : i - lbl.length = 0 := by omega
              rw [hnone (fun j hj => by have := hmax' j hj; omega)]
              rw [hi0] at hhit'
              rw [hit0.mp hhit']
              simp only [↓reduceIte, Option.some.injEq]
              omega
        · simp only [hpre, Bool.false_eq_true, ↓reduceIte]
          have hno : ∀ i, i ≤ rest.length → (if lbl.isPrefixOf (rest.take i) then
              get (.node v ds) ((rest.take i).drop lbl.length) else none).isSome = false := by
            intro i hi
            have : ¬ (lbl.isPrefixOf (rest.take i) = true) := by
              rw [isPrefixOf_take_iff lbl rest i]
              exact fun h => hpre h.1
            simp [this]
          refine ⟨fun _ => trivial, fun i hi hhit _ => ?_⟩
          rw [hno i hi] at hhit
          exact absurd hhit Bool.false_ne_true
      · simpa [lpGoAux, getAux, hc] using lpGoAux_spec ps c rest consumed best

/-- **The loop, on a node.** If `j ≥ 1` is the longest cut of `rest` that `get` answers, the loop
returns `consumed + j`; if `get` answers no cut but the empty one, it returns `best`. -/
theorem lpGo_spec {α : Type} :
    (t : Patricia α) → (rest : List Nat) → (consumed : Nat) → (best : Option Nat) →
      ((∀ j, Hit t rest j → j = 0) → lpGo t rest consumed best = best) ∧
      (∀ j, 1 ≤ j → Hit t rest j → (∀ j', Hit t rest j' → j' ≤ j) →
          lpGo t rest consumed best = some (consumed + j))
  | .node v cs, [], consumed, best => by
      refine ⟨fun _ => by simp [lpGo], fun j hj h _ => ?_⟩
      have := h.1; simp at this; omega
  | .node v cs, c :: r, consumed, best => by
      obtain ⟨hnone, hsome⟩ := lpGoAux_spec cs c r consumed best
      -- a cut `j ≥ 1` of `c :: r` is answered exactly when `getAux` answers the cut `j - 1` of `r`
      have hshift : ∀ i, (Hit (.node v cs) (c :: r) (i + 1) ↔
          i ≤ r.length ∧ (getAux cs c (r.take i)).isSome = true) := by
        intro i
        simp [Hit, get, List.take_succ_cons]
      refine ⟨fun h0 => ?_, fun j hj hhit hmax => ?_⟩
      · simp only [lpGo]
        apply hnone
        intro i hi
        cases hf : (getAux cs c (r.take i)).isSome
        · rfl
        · exact absurd (h0 (i + 1) ((hshift i).mpr ⟨hi, hf⟩)) (by omega)
      · simp only [lpGo]
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        obtain ⟨hi, hf⟩ := (hshift i).mp hhit
        rw [hsome i hi hf (fun i' hi' hf' => by
          have := hmax (i' + 1) ((hshift i').mpr ⟨hi', hf'⟩); omega)]
        congr 1

end

instance {α : Type} (t : Patricia α) (x : List Nat) (j : Nat) : Decidable (Hit t x j) :=
  by unfold Hit; infer_instance

/-- Where a stored key begins `x`, a longest one does. -/
theorem exists_greatest_hit {α : Type} {t : Patricia α} {x : List Nat} {j : Nat}
    (h : Hit t x j) : ∃ J, Hit t x J ∧ ∀ j', Hit t x j' → j' ≤ J :=
  ⟨Nat.findGreatest (Hit t x) x.length, Nat.findGreatest_spec h.1 h,
    fun _ hj' => Nat.le_findGreatest hj'.1 hj'⟩

/-- **What `longest_prefix` returns, through `get`, on every tree**: the key cut to the longest
length at which `get` answers, or `none` if it answers at none. -/
theorem longestPrefix_eq_some_iff_get {α : Type} (t : Patricia α) (k q : List Nat) :
    longestPrefix t k = some q ↔ ∃ j, q = k.take j ∧ Hit t k j ∧ ∀ j', Hit t k j' → j' ≤ j := by
  obtain ⟨v, cs⟩ := t
  obtain ⟨hnone, hsome⟩ := lpGo_spec (.node v cs) k 0 (if v.isSome then some 0 else none)
  have hit0 : Hit (.node v cs) k 0 ↔ v.isSome = true := by simp [Hit, get]
  simp only [longestPrefix]
  by_cases hpos : ∃ j, 1 ≤ j ∧ Hit (.node v cs) k j
  · obtain ⟨j0, hj0, hh0⟩ := hpos
    obtain ⟨J, hJ, hmax⟩ := exists_greatest_hit hh0
    have hJ1 : 1 ≤ J := Nat.le_trans hj0 (hmax j0 hh0)
    rw [hsome J hJ1 hJ hmax, Nat.zero_add, Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨J, rfl, hJ, hmax⟩
    · rintro ⟨j, rfl, hj, hjmax⟩
      rw [Nat.le_antisymm (hmax j hj) (hjmax J hJ)]
  · have hall : ∀ j, Hit (.node v cs) k j → j = 0 := fun j hj => by
      by_contra hne; exact hpos ⟨j, by omega, hj⟩
    rw [hnone hall]
    cases hv : v.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.map_none, reduceCtorEq, false_iff]
      rintro ⟨j, _, hj, _⟩
      rw [hall j hj, hit0, hv] at hj
      exact Bool.false_ne_true hj
    · simp only [↓reduceIte, Option.map_some, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨0, rfl, hit0.mpr hv, fun j' hj' => by rw [hall j' hj']⟩
      · rintro ⟨j, rfl, hj, _⟩
        rw [hall j hj]

/-- `longest_prefix` answers `none` exactly when `get` answers no cut of the key. -/
theorem longestPrefix_eq_none_iff_get {α : Type} (t : Patricia α) (k : List Nat) :
    longestPrefix t k = none ↔ ∀ j, ¬ Hit t k j := by
  rw [Option.eq_none_iff_forall_ne_some]
  constructor
  · intro h j hj
    obtain ⟨J, hJ, hmax⟩ := exists_greatest_hit hj
    exact h (k.take J) ((longestPrefix_eq_some_iff_get t k _).mpr ⟨J, rfl, hJ, hmax⟩)
  · intro h q hq
    obtain ⟨j, _, hj, _⟩ := (longestPrefix_eq_some_iff_get t k q).mp hq
    exact h j hj

/-- A stored key that begins `k` is a hit at its length, on a tree whose words are its lookups. -/
private theorem hit_iff_of_mem_words {α : Type} {t : Patricia α}
    (hk : ∀ x, x ∈ words t ↔ (get t x).isSome) (k : List Nat) (j : Nat) :
    Hit t k j ↔ j ≤ k.length ∧ k.take j ∈ words t := by
  rw [Hit, hk]

/-- **What `longest_prefix` returns**, on a `Valid` tree: `some q` exactly when `q` is a stored
key, a prefix of `k`, and no stored key that is a prefix of `k` is longer. -/
theorem longestPrefix_eq_some_iff {α : Type} (t : Patricia α) (h : Valid t) (k q : List Nat) :
    longestPrefix t k = some q ↔
      q ∈ words t ∧ q <+: k ∧ ∀ q' ∈ words t, q' <+: k → q'.length ≤ q.length := by
  have hk := mem_words_iff t h.noEmptyBranches h.distinctFirstLetters
  rw [longestPrefix_eq_some_iff_get]
  simp only [hit_iff_of_mem_words hk]
  constructor
  · rintro ⟨j, rfl, ⟨hjl, hjk⟩, hmax⟩
    refine ⟨hjk, List.take_prefix j k, fun q' hq' hpre => ?_⟩
    have hl := hpre.length_le
    have := hmax q'.length ⟨hl, by rwa [← List.prefix_iff_eq_take.mp hpre]⟩
    simp only [List.length_take]
    omega
  · rintro ⟨hq, hpre, hmax⟩
    have hl := hpre.length_le
    refine ⟨q.length, List.prefix_iff_eq_take.mp hpre, ⟨hl, ?_⟩, fun j' ⟨hj', hjk⟩ => ?_⟩
    · rwa [← List.prefix_iff_eq_take.mp hpre]
    · have := hmax _ hjk (List.take_prefix j' k)
      simp only [List.length_take] at this
      omega

/-- **`longest_prefix` answers `none`**, on a `Valid` tree, exactly when no stored key is a prefix
of `k`: the router's default route. -/
theorem longestPrefix_eq_none_iff {α : Type} (t : Patricia α) (h : Valid t) (k : List Nat) :
    longestPrefix t k = none ↔ ∀ q ∈ words t, ¬ q <+: k := by
  have hk := mem_words_iff t h.noEmptyBranches h.distinctFirstLetters
  rw [longestPrefix_eq_none_iff_get]
  simp only [hit_iff_of_mem_words hk]
  constructor
  · intro hn q hq hpre
    exact hn q.length ⟨hpre.length_le, by rwa [← List.prefix_iff_eq_take.mp hpre]⟩
  · rintro hn j ⟨_, hjk⟩
    exact hn _ hjk (List.take_prefix j k)

/-! ### `keys_with_prefix` -/

mutual

/-- The descent of `keys_with_prefix`: walk down whole labels while the prefix lasts, returning
the path read and the node reached, or `none` if the walk stops short. With nothing left of the
prefix, the node stands where it is. -/
def prefixNode {α : Type} :
    Patricia α → List Nat → List Nat → Option (List Nat × Patricia α)
  | t, [], consumed => some (consumed, t)
  | .node _ cs, c :: rest, consumed => prefixAux cs c rest consumed

/-- Choose the child whose label begins with `c`. A label no longer than the rest of the prefix
must begin it, and the walk steps down; a longer label must continue it, and then the prefix ends
inside that label: every key below it begins with the prefix, so the whole label is read and the
walk stops at its child. -/
def prefixAux {α : Type} :
    List (List Nat × Patricia α) → Nat → List Nat → List Nat → Option (List Nat × Patricia α)
  | [], _, _, _ => none
  | ([], _) :: ps, c, rest, consumed => prefixAux ps c rest consumed
  | (c' :: lbl, u) :: ps, c, rest, consumed =>
      if c' = c then
        if lbl.length ≤ rest.length then
          if lbl.isPrefixOf rest then prefixNode u (rest.drop lbl.length) (consumed ++ c' :: lbl)
          else none
        else if rest.isPrefixOf lbl then some (consumed ++ c' :: lbl, u) else none
      else prefixAux ps c rest consumed

end

mutual

/-- The chapter's `_collect` on a Patricia tree: the node's own key, if it holds one, then
everything below each child, in the order of the child list, the child's label appended to the
path. -/
def collect {α : Type} : Patricia α → List Nat → List (List Nat)
  | .node v cs, path => (match v with | some _ => [path] | none => []) ++ collectAux cs path

/-- `collect` over a child list. -/
def collectAux {α : Type} : List (List Nat × Patricia α) → List Nat → List (List Nat)
  | [], _ => []
  | (lbl, t) :: rest, path => collect t (path ++ lbl) ++ collectAux rest path

end

/-- **`keys_with_prefix` on a Patricia tree.** Walk down the prefix, possibly ending inside a
label; if the walk stops short no key begins with it; otherwise collect everything below, children
in byte order (`sortTree`, the Rust's order). -/
def keysWithPrefix {α : Type} (t : Patricia α) (p : List Nat) : List (List Nat) :=
  match prefixNode t p [] with
  | some (path, n) => collect (sortTree n) path
  | none => []

mutual

/-- `collect` is `words` with the path in front. -/
theorem collect_eq {α : Type} : (t : Patricia α) → (path : List Nat) →
    collect t path = (words t).map (path ++ ·)
  | .node v cs, path => by
      cases v <;> simp [collect, words, collectAux_eq cs path]

/-- The child-list half of `collect_eq`. -/
theorem collectAux_eq {α : Type} : (cs : List (List Nat × Patricia α)) → (path : List Nat) →
    collectAux cs path = (wordsAux cs).map (path ++ ·)
  | [], _ => by simp [collectAux, wordsAux]
  | (lbl, t) :: rest, path => by
      simp [collectAux, wordsAux, collect_eq t, collectAux_eq rest path, Function.comp_def]

end

/-- Blocks of words behind labels whose first symbols strictly ascend, each block ascending,
ascend. -/
theorem wordsAux_sorted {α : Type} :
    (l : List (List Nat × Patricia α)) → l.Pairwise (fun e f => headSym e < headSym f) →
      (∀ e ∈ l, e.1 ≠ []) → (∀ e ∈ l, (words e.2).Pairwise (· < ·)) →
      (wordsAux l).Pairwise (· < ·)
  | [], _, _, _ => List.Pairwise.nil
  | (lbl, t) :: rest, hl, hne, hk => by
      simp only [wordsAux]
      rw [List.pairwise_append]
      refine ⟨?_, wordsAux_sorted rest hl.of_cons (fun e he => hne e (List.mem_cons_of_mem _ he))
        (fun e he => hk e (List.mem_cons_of_mem _ he)), ?_⟩
      · rw [List.pairwise_map]
        exact (hk (lbl, t) (List.mem_cons_self ..)).imp
          fun h => (Trie.append_lt_append_same lbl).mpr h
      · intro x hx y hy
        obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨q, hq, y', _, rfl⟩ := (mem_wordsAux' rest y).mp hy
        have hcq : headSym (lbl, t) < headSym q := List.rel_of_pairwise_cons hl hq
        obtain ⟨a, l1, hl1⟩ := List.exists_cons_of_ne_nil (hne (lbl, t) (List.mem_cons_self ..))
        obtain ⟨b, l2, hl2⟩ := List.exists_cons_of_ne_nil (hne q (List.mem_cons_of_mem _ hq))
        simp only [headSym] at hcq
        have hl1' : lbl = a :: l1 := hl1
        rw [hl1'] at hcq ⊢
        rw [hl2] at hcq ⊢
        simp only [List.headD_cons] at hcq
        simp only [List.cons_append]
        rw [List.cons_lt_cons_iff]
        exact Or.inl hcq

mutual

/-- On a tree with no empty branch whose heads ascend, the words strictly ascend: byte order, each
once. -/
theorem words_sorted {α : Type} :
    (t : Patricia α) → NoEmptyBranches t → SortedHeads t → (words t).Pairwise (· < ·)
  | .node v cs, hp, ⟨hpw, haux⟩ => by
      simp only [words]
      have hall := (noEmptyBranchesChildren_iff cs).mp hp
      have hrest := wordsAux_sorted cs hpw (fun e he => (hall e he).1)
        (wordsAux_sorted_of cs hp haux)
      cases v with
      | none => simpa using hrest
      | some _ =>
          simp only [List.singleton_append]
          refine List.Pairwise.cons ?_ hrest
          intro y hy
          obtain ⟨q, hq, y', _, rfl⟩ := (mem_wordsAux' cs y).mp hy
          obtain ⟨a, l1, hl1⟩ := List.exists_cons_of_ne_nil (hall q hq).1
          rw [hl1, List.cons_append]
          exact List.nil_lt_cons _ _

/-- The child-list half of `words_sorted`. -/
theorem wordsAux_sorted_of {α : Type} :
    (cs : List (List Nat × Patricia α)) → NoEmptyBranchesChildren cs → SortedHeadsAux cs →
      ∀ e ∈ cs, (words e.2).Pairwise (· < ·)
  | [], _, _, _, he => by simp at he
  | (lbl, u) :: ps, ⟨_, hpn, hpr⟩, ⟨hsu, hsr⟩, e, he => by
      rcases List.mem_cons.mp he with rfl | he
      · exact words_sorted u hpn hsu
      · exact wordsAux_sorted_of ps hpr hsr e he

end

/-- `c :: r` begins a key behind the label `c :: lbl` no longer than `r` exactly when `lbl`
begins `r` and the rest of `r` begins what follows the label. -/
theorem isPrefixOf_cons_append_of_le (c : Nat) {r lbl : List Nat} (y : List Nat)
    (h : lbl.length ≤ r.length) :
    (c :: r).isPrefixOf (c :: lbl ++ y) =
      (lbl.isPrefixOf r && (r.drop lbl.length).isPrefixOf y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.isPrefixOf_iff_prefix, List.cons_append, List.cons_prefix_cons,
    true_and]
  constructor
  · intro hr
    have hl : lbl <+: r := List.prefix_of_prefix_length_le (List.prefix_append lbl y) hr h
    refine ⟨hl, ?_⟩
    obtain ⟨s, rfl⟩ := hl
    simpa using hr
  · rintro ⟨⟨s, rfl⟩, hs⟩
    simpa using hs

/-- `c :: r` begins a key behind the label `c :: lbl` longer than `r` exactly when `r` begins
`lbl`. -/
theorem isPrefixOf_cons_append_of_lt (c : Nat) {r lbl : List Nat} (y : List Nat)
    (h : r.length < lbl.length) :
    (c :: r).isPrefixOf (c :: lbl ++ y) = r.isPrefixOf lbl := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.isPrefixOf_iff_prefix, List.cons_append, List.cons_prefix_cons, true_and]
  constructor
  · intro hr
    exact List.prefix_of_prefix_length_le hr (List.prefix_append lbl y) (by omega)
  · intro hr
    exact hr.trans (List.prefix_append lbl y)

mutual

/-- **The descent finds the block.** On a tree with non-empty labels and distinct heads, the
stored words beginning with `p` (behind the path `consumed`) are the words of the node the descent
reaches, behind the path it read; none if it stops short. -/
theorem filter_words_prefixNode {α : Type} :
    (t : Patricia α) → NoEmptyBranches t → DistinctFirstLetters t → (p consumed : List Nat) →
      (((words t).filter (p.isPrefixOf ·)).map (consumed ++ ·)).Perm
        (match prefixNode t p consumed with
         | some (path, n) => (words n).map (path ++ ·)
         | none => [])
  | .node v cs, _, _, [], consumed => by
      simp [prefixNode]
  | .node v cs, hp, ⟨hnd, hd⟩, c :: r, consumed => by
      have hv : (words (.node v cs)).filter ((c :: r).isPrefixOf ·) =
          (wordsAux cs).filter ((c :: r).isPrefixOf ·) := by
        cases v <;> simp [words, List.isPrefixOf]
      rw [hv]
      simp only [prefixNode]
      exact filter_wordsAux_prefixAux cs hp hd hnd c r consumed

/-- The child-list half of `filter_words_prefixNode`. -/
theorem filter_wordsAux_prefixAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → NoEmptyBranchesChildren cs →
      DistinctFirstLettersChildren cs → (cs.map (·.1.head?)).Nodup → (c : Nat) →
      (r consumed : List Nat) →
      (((wordsAux cs).filter ((c :: r).isPrefixOf ·)).map (consumed ++ ·)).Perm
        (match prefixAux cs c r consumed with
         | some (path, n) => (words n).map (path ++ ·)
         | none => [])
  | [], _, _, _, c, r, consumed => by simp [wordsAux, prefixAux]
  | ([], _) :: _, hp, _, _, _, _, _ => absurd rfl hp.1
  | (c' :: lbl, u) :: ps, ⟨_, hpn, hpr⟩, ⟨hdu, hdr⟩, hnd, c, r, consumed => by
      simp only [wordsAux, List.filter_append, List.map_append, prefixAux]
      by_cases hcc : c' = c
      · subst hcc
        -- no sibling's key begins with `c'`
        have hnone : (wordsAux ps).filter ((c' :: r).isPrefixOf ·) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          obtain ⟨q, hq, y, _, rfl⟩ := (mem_wordsAux' ps x).mp hx
          obtain ⟨b, l2, hl2⟩ := List.exists_cons_of_ne_nil
            (((noEmptyBranchesChildren_iff ps).mp hpr) q hq).1
          have hb : b ≠ c' := by
            intro hb
            simp only [List.map_cons, List.nodup_cons, List.head?_cons] at hnd
            apply hnd.1
            rw [List.mem_map]
            exact ⟨q, hq, by rw [hl2, hb]; rfl⟩
          rw [hl2]
          simp [List.isPrefixOf, Ne.symm hb]
        rw [hnone, List.map_nil, List.append_nil]
        simp only [↓reduceIte, List.filter_map, List.map_map]
        by_cases hle : lbl.length ≤ r.length
        · simp only [hle, ↓reduceIte]
          have hf : ∀ y, ((c' :: r).isPrefixOf ∘ ((c' :: lbl) ++ ·)) y =
              (lbl.isPrefixOf r && (r.drop lbl.length).isPrefixOf y) := fun y =>
            isPrefixOf_cons_append_of_le c' y hle
          rw [List.filter_congr (fun y _ => hf y)]
          by_cases hpre : lbl.isPrefixOf r = true
          · simp only [hpre, Bool.true_and, ↓reduceIte]
            have := filter_words_prefixNode u hpn hdu (r.drop lbl.length)
              (consumed ++ c' :: lbl)
            refine List.Perm.trans (List.Perm.of_eq ?_) this
            simp [Function.comp_def]
          · simp only [hpre, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
            simp
        · simp only [hle, ↓reduceIte]
          have hlt : r.length < lbl.length := by omega
          have hf : ∀ y, ((c' :: r).isPrefixOf ∘ ((c' :: lbl) ++ ·)) y = r.isPrefixOf lbl :=
            fun y => isPrefixOf_cons_append_of_lt c' y hlt
          rw [List.filter_congr (fun y _ => hf y)]
          by_cases hpre : r.isPrefixOf lbl = true
          · simp [hpre, Function.comp_def]
          · simp [hpre]
      · have hnil : ((words u).map ((c' :: lbl) ++ ·)).filter ((c :: r).isPrefixOf ·) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
          simp [List.isPrefixOf, Ne.symm hcc]
        rw [hnil, List.map_nil, List.nil_append]
        simp only [hcc, ↓reduceIte]
        exact filter_wordsAux_prefixAux ps hpr hdr (List.nodup_cons.mp hnd).2 c r consumed

end

mutual

/-- The descent reaches a node with no empty branch and distinct heads. -/
theorem valid_prefixNode {α : Type} :
    (t : Patricia α) → NoEmptyBranches t → DistinctFirstLetters t → (p consumed : List Nat) →
      ∀ path n, prefixNode t p consumed = some (path, n) →
        NoEmptyBranches n ∧ DistinctFirstLetters n
  | t, hp, hd, [], consumed, path, n, h => by
      simp only [prefixNode, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨hp, hd⟩
  | .node v cs, hp, ⟨_, hd⟩, c :: r, consumed, path, n, h => by
      simp only [prefixNode] at h
      exact valid_prefixAux cs hp hd c r consumed path n h

/-- The child-list half of `valid_prefixNode`. -/
theorem valid_prefixAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → NoEmptyBranchesChildren cs →
      DistinctFirstLettersChildren cs → (c : Nat) → (r consumed : List Nat) →
      ∀ path n, prefixAux cs c r consumed = some (path, n) →
        NoEmptyBranches n ∧ DistinctFirstLetters n
  | [], _, _, _, _, _, _, _, h => by simp [prefixAux] at h
  | ([], _) :: ps, ⟨_, _, hpr⟩, ⟨_, hdr⟩, c, r, consumed, path, n, h => by
      simp only [prefixAux] at h
      exact valid_prefixAux ps hpr hdr c r consumed path n h
  | (c' :: lbl, u) :: ps, ⟨_, hpn, hpr⟩, ⟨hdu, hdr⟩, c, r, consumed, path, n, h => by
      simp only [prefixAux] at h
      split at h
      · split at h
        · split at h
          · exact valid_prefixNode u hpn hdu _ _ path n h
          · cases h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            exact ⟨hpn, hdu⟩
          · cases h
      · exact valid_prefixAux ps hpr hdr c r consumed path n h

end

/-- **What `keys_with_prefix` returns**, as a set: on a `Valid` tree, exactly the stored words
that begin with `p`. -/
theorem keysWithPrefix_perm {α : Type} (t : Patricia α) (h : Valid t) (p : List Nat) :
    (keysWithPrefix t p).Perm ((words t).filter (p.isPrefixOf ·)) := by
  have hf := filter_words_prefixNode t h.noEmptyBranches h.distinctFirstLetters p []
  simp only [List.nil_append, List.map_id'] at hf
  unfold keysWithPrefix
  split
  · rename_i path n hn
    rw [hn] at hf
    rw [collect_eq]
    exact ((words_sortTree_perm n).map _).trans hf.symm
  · rename_i hn
    rw [hn] at hf
    exact hf.symm

/-- **In byte order, each once**: on a `Valid` tree the answer strictly ascends, which with
`keysWithPrefix_perm` fixes the list. -/
theorem keysWithPrefix_sorted {α : Type} (t : Patricia α) (h : Valid t) (p : List Nat) :
    (keysWithPrefix t p).Pairwise (· < ·) := by
  unfold keysWithPrefix
  split
  · rename_i path n hn
    obtain ⟨hpn, hdn⟩ :=
      valid_prefixNode t h.noEmptyBranches h.distinctFirstLetters p [] path n hn
    rw [collect_eq, List.pairwise_map]
    exact (words_sorted (sortTree n) (noEmptyBranches_sortTree n hpn)
      (sortedHeads_sortTree n hpn hdn)).imp
      fun hxy => (Trie.append_lt_append_same path).mpr hxy
  · exact List.Pairwise.nil

/-- **The list is fixed**: on a `Valid` tree, any strictly ascending arrangement of the stored words
that begin with `p` is `keysWithPrefix t p`. -/
theorem keysWithPrefix_unique {α : Type} (t : Patricia α) (h : Valid t) (p : List Nat)
    (l : List (List Nat)) (hl : l.Pairwise (· < ·))
    (hperm : l.Perm ((words t).filter (p.isPrefixOf ·))) : l = keysWithPrefix t p :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => absurd (List.lt_trans h₁ h₂) (List.lt_irrefl _))
    hl (keysWithPrefix_sorted t h p) (hperm.trans (keysWithPrefix_perm t h p).symm)

end Patricia

end AlgoDesign.Strings
