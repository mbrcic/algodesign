/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Trie.Remove
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Find

/-!
# Trie: the queries

- `toList` lists every stored key with its value; on a `DistinctLetters` trie `get t k = some a`
  exactly when `(k, a)` is in it (`get_eq_some_iff`).
- `keysWithPrefix`, the chapter's `keys_with_prefix`: on a `DistinctLetters` trie the stored words
  that begin with the prefix (`keysWithPrefix_perm`), each once and in byte order
  (`keysWithPrefix_sorted`). `sortTrie` sorts every child list by symbol first.
- `longestPrefix`, the chapter's `longest_prefix`: the longest stored key that is a prefix of the
  key (`longestPrefix_eq_some_iff`), or none (`longestPrefix_eq_none_iff`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Trie

/-! ### `get` against the stored map -/

mutual

/-- Every stored key with its value, in the order `words` lists the words (`map_fst_toList`). -/
def toList {α : Type} : Trie α → List (List Nat × α)
  | .node v cs => (match v with | some a => [([], a)] | none => []) ++ toListAux cs

/-- `toList` of a child list, each key prefixed with the symbol its subtrie is filed under. -/
def toListAux {α : Type} : List (Nat × Trie α) → List (List Nat × α)
  | [] => []
  | (c, t) :: rest => (toList t).map (fun e => (c :: e.1, e.2)) ++ toListAux rest

end

mutual

/-- The words of `toList` are `words`. -/
theorem map_fst_toList {α : Type} : (t : Trie α) → (toList t).map (·.1) = words t
  | .node v cs => by
      cases v <;> simp [toList, words, map_fst_toListAux cs]

/-- The child-list half of `map_fst_toList`. -/
theorem map_fst_toListAux {α : Type} :
    (cs : List (Nat × Trie α)) → (toListAux cs).map (·.1) = wordsAux cs
  | [] => by simp [toListAux, wordsAux]
  | (c, t) :: rest => by
      simp [toListAux, wordsAux, ← map_fst_toList t, map_fst_toListAux rest, Function.comp_def]

end

/-- An entry of a child list's `toList` is a child's symbol followed by an entry of that child. -/
theorem mem_toListAux {α : Type} :
    ∀ (cs : List (Nat × Trie α)) (x : List Nat) (a : α),
      (x, a) ∈ toListAux cs ↔ ∃ p ∈ cs, ∃ y, (y, a) ∈ toList p.2 ∧ x = p.1 :: y
  | [], x, a => by simp [toListAux]
  | (c, t) :: rest, x, a => by
      rw [toListAux, List.mem_append, mem_toListAux rest x a, List.mem_map]
      constructor
      · rintro (⟨⟨y, b⟩, hy, he⟩ | ⟨q, hq, y, hy, rfl⟩)
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨(c, t), List.mem_cons_self .., y, hy, rfl⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, y, hy, rfl⟩
      · rintro ⟨q, hq, y, hy, rfl⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inl ⟨(y, a), hy, rfl⟩
        · exact Or.inr ⟨q, hq', y, hy, rfl⟩

/-- **`get` is lookup in the stored map**, on a `DistinctLetters` trie: `get t k` answers `some a`
exactly when `(k, a)` is stored. `words` are the first components (`map_fst_toList`), so with
`mem_words_iff` this is the whole of what `get` owes. Without `DistinctLetters` it fails: a second
child under one symbol holds words `get` never reaches. -/
theorem get_eq_some_iff {α : Type} :
    ∀ (k : List Nat) (t : Trie α), DistinctLetters t → ∀ a, (get t k = some a ↔ (k, a) ∈ toList t)
  | [], .node v cs, _, a => by
      have : ([], a) ∉ toListAux cs := by
        rw [mem_toListAux]; rintro ⟨_, _, _, _, h⟩; cases h
      cases v with
      | none => simp [toList, get, this]
      | some b =>
          simp only [toList, get, List.cons_append, List.nil_append, List.mem_cons,
            Prod.mk.injEq, true_and, this, or_false, Option.some.injEq]
          exact ⟨fun h => h.symm, fun h => h.symm⟩
  | c :: rest, .node v cs, ⟨hnd, haux⟩, a => by
      have hx : (c :: rest, a) ∈ toList (.node v cs) ↔ (c :: rest, a) ∈ toListAux cs := by
        cases v <;> simp [toList]
      rw [hx, mem_toListAux]
      rcases hq : cs.find? (fun p => p.1 == c) with _ | q
      · simp only [get, hq, reduceCtorEq, false_iff]
        rintro ⟨p, hp, y, _, hpy⟩
        have := List.find?_eq_none.mp hq p hp
        simp_all
      · have hqm := List.mem_of_find?_eq_some hq
        have hqc : q.1 = c := by simpa using List.find?_some hq
        simp only [get, hq]
        rw [get_eq_some_iff rest q.2 (distinctLetters_of_mem haux hqm) a]
        constructor
        · intro hy
          exact ⟨q, hqm, rest, hy, by rw [hqc]⟩
        · rintro ⟨p, hp, y, hy, hpy⟩
          obtain ⟨rfl, rfl⟩ := List.cons.inj hpy
          rw [eq_of_fst_eq hnd hp hqm (by rw [hqc])] at hy
          exact hy

/-- `get` misses exactly the words with nothing stored. -/
theorem find_eq_none_iff {α : Type} (t : Trie α) (h : DistinctLetters t) (k : List Nat) :
    get t k = none ↔ ∀ a, (k, a) ∉ toList t := by
  rw [Option.eq_none_iff_forall_ne_some]
  exact forall_congr' fun a => not_congr (get_eq_some_iff k t h a)

/-! ### `keys_with_prefix` -/

/-- Walk down a key from the root, building nothing: the node the key leads to, or `none` if the
path stops short. `get` is this walk followed by reading the node's value. -/
def nodeAt {α : Type} : Trie α → List Nat → Option (Trie α)
  | t, [] => some t
  | .node _ cs, c :: rest =>
      match cs.find? (fun p => p.1 == c) with
      | some p => nodeAt p.2 rest
      | none => none
termination_by structural _ k => k

/-- Put a child before the first child filed under a symbol not below its own: an ordered insert
by symbol, written out so the kernel can evaluate it. -/
def insertBySym {α : Type} (e : Nat × Trie α) : List (Nat × Trie α) → List (Nat × Trie α)
  | [] => [e]
  | f :: l => if e.1 ≤ f.1 then e :: f :: l else f :: insertBySym e l

/-- Insertion sort of a child list by symbol. -/
def sortBySym {α : Type} : List (Nat × Trie α) → List (Nat × Trie α)
  | [] => []
  | e :: l => insertBySym e (sortBySym l)

mutual

/-- The same trie with every child list in byte order: the order the Python's
`sorted(node.children)` visits and the Rust's array holds. -/
def sortTrie {α : Type} : Trie α → Trie α
  | .node v cs => .node v (sortBySym (sortTrieAux cs))

/-- `sortTrie` below every child of a child list, symbols untouched. -/
def sortTrieAux {α : Type} : List (Nat × Trie α) → List (Nat × Trie α)
  | [] => []
  | (c, t) :: rest => (c, sortTrie t) :: sortTrieAux rest

end

mutual

/-- The chapter's `_collect`: the node's own key, if it holds one, then everything below each
child, in the order of the child list, with `path` the key that leads to the node. -/
def collect {α : Type} : Trie α → List Nat → List (List Nat)
  | .node v cs, path => (match v with | some _ => [path] | none => []) ++ collectAux cs path

/-- `collect` over a child list: each child's words, its symbol appended to the path. -/
def collectAux {α : Type} : List (Nat × Trie α) → List Nat → List (List Nat)
  | [], _ => []
  | (c, t) :: rest, path => collect t (path ++ [c]) ++ collectAux rest path

end

/-- **The chapter's `keys_with_prefix`.** Walk down the prefix; if the path stops short no key
begins with it; otherwise collect everything below, in byte order. -/
def keysWithPrefix {α : Type} (t : Trie α) (p : List Nat) : List (List Nat) :=
  match nodeAt t p with
  | some n => collect (sortTrie n) p
  | none => []

mutual

/-- `collect` is `words` with the path in front. -/
theorem collect_eq {α : Type} : (t : Trie α) → (path : List Nat) →
    collect t path = (words t).map (path ++ ·)
  | .node v cs, path => by
      cases v <;> simp [collect, words, collectAux_eq cs path]

/-- The child-list half of `collect_eq`. -/
theorem collectAux_eq {α : Type} : (cs : List (Nat × Trie α)) → (path : List Nat) →
    collectAux cs path = (wordsAux cs).map (path ++ ·)
  | [], _ => by simp [collectAux, wordsAux]
  | (c, t) :: rest, path => by
      simp [collectAux, wordsAux, collect_eq t, collectAux_eq rest path, Function.comp_def]

end

/-- An ordered insert by symbol adds the child and reorders nothing else. -/
theorem insertBySym_perm {α : Type} (e : Nat × Trie α) :
    (l : List (Nat × Trie α)) → (insertBySym e l).Perm (e :: l)
  | [] => List.Perm.refl _
  | f :: l => by
      unfold insertBySym
      split
      · exact List.Perm.refl _
      · exact ((insertBySym_perm e l).cons f).trans (List.Perm.swap e f l)

/-- Sorting a child list by symbol only reorders it. -/
theorem sortBySym_perm {α : Type} : (l : List (Nat × Trie α)) → (sortBySym l).Perm l
  | [] => List.Perm.refl _
  | e :: l => (insertBySym_perm e _).trans ((sortBySym_perm l).cons e)

/-- An ordered insert by symbol keeps a child list in symbol order. -/
theorem insertBySym_sorted {α : Type} (e : Nat × Trie α) :
    (l : List (Nat × Trie α)) → l.Pairwise (fun p q => p.1 ≤ q.1) →
      (insertBySym e l).Pairwise (fun p q => p.1 ≤ q.1)
  | [], _ => List.pairwise_singleton _ _
  | f :: l, h => by
      unfold insertBySym
      split
      · rename_i hle
        refine List.Pairwise.cons ?_ h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hle
        · exact Nat.le_trans hle (List.rel_of_pairwise_cons h hx)
      · rename_i hle
        refine List.Pairwise.cons ?_ (insertBySym_sorted e l h.of_cons)
        intro x hx
        rcases List.mem_cons.mp ((insertBySym_perm e l).mem_iff.mp hx) with rfl | hx
        · omega
        · exact List.rel_of_pairwise_cons h hx

/-- Sorting a child list by symbol puts it in symbol order. -/
theorem sortBySym_sorted {α : Type} :
    (l : List (Nat × Trie α)) → (sortBySym l).Pairwise (fun p q => p.1 ≤ q.1)
  | [] => List.Pairwise.nil
  | e :: l => insertBySym_sorted e _ (sortBySym_sorted l)

/-- The words of a child list, block by block. -/
theorem wordsAux_eq_flatMap {α : Type} :
    (l : List (Nat × Trie α)) → wordsAux l = l.flatMap (fun e => (words e.2).map (e.1 :: ·))
  | [] => rfl
  | e :: l => by simp [wordsAux, wordsAux_eq_flatMap l]

mutual

/-- Sorting the child lists reorders the key list and changes nothing else. -/
theorem words_sortTrie_perm {α : Type} : (t : Trie α) → (words (sortTrie t)).Perm (words t)
  | .node v cs => by
      simp only [sortTrie, words]
      refine List.Perm.append_left _ ?_
      refine List.Perm.trans ?_ (wordsAux_sortTrieAux_perm cs)
      rw [wordsAux_eq_flatMap, wordsAux_eq_flatMap]
      exact List.Perm.flatMap_right _ (sortBySym_perm _)

/-- The child-list half of `words_sortTrie_perm`. -/
theorem wordsAux_sortTrieAux_perm {α : Type} :
    (cs : List (Nat × Trie α)) → (wordsAux (sortTrieAux cs)).Perm (wordsAux cs)
  | [] => List.Perm.refl _
  | (c, t) :: rest => by
      simp only [sortTrieAux, wordsAux]
      exact ((words_sortTrie_perm t).map _).append (wordsAux_sortTrieAux_perm rest)

end

/-- `sortTrieAux` keeps every child's symbol. -/
theorem map_fst_sortTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → (sortTrieAux cs).map (·.1) = cs.map (·.1)
  | [] => rfl
  | (c, t) :: rest => by simp [sortTrieAux, map_fst_sortTrieAux rest]

/-- Consing one symbol keeps the order of two words. -/
theorem cons_lt_cons_same {c : Nat} {x y : List Nat} : c :: x < c :: y ↔ x < y := by
  rw [List.cons_lt_cons_iff]
  simp

/-- A shared prefix keeps the order of two words. -/
theorem append_lt_append_same : (p : List Nat) → {x y : List Nat} → (p ++ x < p ++ y ↔ x < y)
  | [], _, _ => Iff.rfl
  | c :: p, _, _ => by rw [List.cons_append, List.cons_append, cons_lt_cons_same,
      append_lt_append_same p]

/-- The blocks of a child list whose symbols strictly ascend, each block ascending, ascend. -/
theorem wordsAux_sorted {α : Type} :
    (l : List (Nat × Trie α)) → l.Pairwise (fun p q => p.1 < q.1) →
      (∀ p ∈ l, (words p.2).Pairwise (· < ·)) → (wordsAux l).Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | (c, t) :: rest, hl, hk => by
      simp only [wordsAux]
      rw [List.pairwise_append]
      refine ⟨?_,
        wordsAux_sorted rest hl.of_cons (fun p hp => hk p (List.mem_cons_of_mem _ hp)), ?_⟩
      · rw [List.pairwise_map]
        exact (hk (c, t) (List.mem_cons_self ..)).imp fun h => cons_lt_cons_same.mpr h
      · intro x hx y hy
        obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨q, hq, y', _, rfl⟩ := (mem_wordsAux rest y).mp hy
        have hcq : c < q.1 := List.rel_of_pairwise_cons hl hq
        rw [List.cons_lt_cons_iff]
        exact Or.inl hcq

mutual

/-- On a `DistinctLetters` trie, the sorted trie lists its words strictly ascending: byte order,
each key once. -/
theorem words_sortTrie_sorted {α : Type} :
    (t : Trie α) → DistinctLetters t → (words (sortTrie t)).Pairwise (· < ·)
  | .node v cs, ⟨hnd, haux⟩ => by
      simp only [sortTrie, words]
      have hperm := sortBySym_perm (sortTrieAux cs)
      have hstrict : (sortBySym (sortTrieAux cs)).Pairwise (fun p q => p.1 < q.1) := by
        have hne : (sortBySym (sortTrieAux cs)).Pairwise (fun p q => p.1 ≠ q.1) := by
          have := (hperm.map (·.1)).nodup_iff.mpr (by rw [map_fst_sortTrieAux]; exact hnd)
          exact List.pairwise_map.mp this
        exact (sortBySym_sorted _).imp₂ (fun _ _ h₁ h₂ => Nat.lt_of_le_of_ne h₁ h₂) hne
      have hrest := wordsAux_sorted _ hstrict
        (fun p hp => wordsAux_sortTrieAux_sorted cs haux p (hperm.mem_iff.mp hp))
      cases v with
      | none => simpa using hrest
      | some _ =>
          simp only [List.singleton_append]
          refine List.Pairwise.cons ?_ hrest
          intro y hy
          obtain ⟨q, _, y', _, rfl⟩ := (mem_wordsAux _ y).mp hy
          exact List.nil_lt_cons _ _

/-- The child-list half of `words_sortTrie_sorted`. -/
theorem wordsAux_sortTrieAux_sorted {α : Type} :
    (cs : List (Nat × Trie α)) → DistinctLettersChildren cs →
      ∀ p ∈ sortTrieAux cs, (words p.2).Pairwise (· < ·)
  | [], _, _, hp => by simp [sortTrieAux] at hp
  | (c, t) :: rest, ⟨ht, hrest⟩, p, hp => by
      simp only [sortTrieAux, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact words_sortTrie_sorted t ht
      · exact wordsAux_sortTrieAux_sorted rest hrest p hp

end

/-- The walk keeps `DistinctLetters`: the node a prefix leads to is a `DistinctLetters` trie. -/
theorem distinctLetters_nodeAt {α : Type} :
    ∀ (p : List Nat) (t : Trie α), DistinctLetters t → ∀ n, nodeAt t p = some n → DistinctLetters n
  | [], t, h, n, hn => by
      simp only [nodeAt, Option.some.injEq] at hn
      exact hn ▸ h
  | c :: rest, .node v cs, ⟨_, haux⟩, n, hn => by
      simp only [nodeAt] at hn
      split at hn
      · rename_i q hq
        exact distinctLetters_nodeAt rest q.2 (distinctLetters_of_mem haux
            (List.mem_of_find?_eq_some hq)) n hn
      · cases hn

/-- The words of a child list that begin with `c :: r` are the words below the one child filed
under `c` that begin with `r`, behind `c`. -/
theorem filter_wordsAux {α : Type} (c : Nat) (r : List Nat) :
    (cs : List (Nat × Trie α)) → (cs.map (·.1)).Nodup →
      ((wordsAux cs).filter ((c :: r).isPrefixOf ·)).Perm
        (match cs.find? (fun p => p.1 == c) with
         | some q => ((words q.2).filter (r.isPrefixOf ·)).map (c :: ·)
         | none => [])
  | [], _ => by simp [wordsAux]
  | (d, u) :: rest, hnd => by
      simp only [wordsAux, List.filter_append, List.find?_cons]
      by_cases hdc : d = c
      · subst hdc
        have hnone : (wordsAux rest).filter ((d :: r).isPrefixOf ·) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          obtain ⟨q, hq, y, _, rfl⟩ := (mem_wordsAux rest x).mp hx
          have : q.1 ≠ d := by
            intro h
            simp only [List.map_cons, List.nodup_cons] at hnd
            exact hnd.1 (h ▸ List.mem_map_of_mem hq)
          simp [List.isPrefixOf, this.symm]
        simp only [beq_self_eq_true, hnone, List.append_nil, List.filter_map]
        apply List.Perm.of_eq
        congr 1
        apply List.filter_congr
        intro x _
        simp [List.isPrefixOf]
      · have hne : (d == c) = false := by simpa using hdc
        have hnil : ((words u).map (d :: ·)).filter ((c :: r).isPrefixOf ·) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
          simp [List.isPrefixOf, Ne.symm hdc]
        rw [hnil, List.nil_append]
        simp only [hne]
        exact filter_wordsAux c r rest (List.nodup_cons.mp hnd).2

/-- **The walk finds the block.** On a `DistinctLetters` trie the stored words beginning with `p`
are the words of the node `p` leads to, behind `p`; none if the walk stops short. -/
theorem filter_words_nodeAt {α : Type} :
    ∀ (p : List Nat) (t : Trie α), DistinctLetters t →
      ((words t).filter (p.isPrefixOf ·)).Perm
        (match nodeAt t p with
         | some n => (words n).map (p ++ ·)
         | none => [])
  | [], t, _ => by simp [nodeAt]
  | c :: rest, .node v cs, ⟨hnd, haux⟩ => by
      have hv : (words (.node v cs)).filter ((c :: rest).isPrefixOf ·) =
          (wordsAux cs).filter ((c :: rest).isPrefixOf ·) := by
        cases v <;> simp [words, List.isPrefixOf]
      rw [hv]
      simp only [nodeAt]
      refine (filter_wordsAux c rest cs hnd).trans ?_
      split
      · rename_i q hq
        have hd := distinctLetters_of_mem haux (List.mem_of_find?_eq_some hq)
        refine ((filter_words_nodeAt rest q.2 hd).map (c :: ·)).trans ?_
        split <;> simp [Function.comp_def]
      · exact List.Perm.refl _

/-- **What `keys_with_prefix` returns**, as a set: on a `DistinctLetters` trie, exactly the stored
words that begin with `p`. -/
theorem keysWithPrefix_perm {α : Type} (t : Trie α) (h : DistinctLetters t) (p : List Nat) :
    (keysWithPrefix t p).Perm ((words t).filter (p.isPrefixOf ·)) := by
  have hf := filter_words_nodeAt p t h
  unfold keysWithPrefix
  split
  · rename_i n hn
    rw [hn] at hf
    rw [collect_eq]
    exact ((words_sortTrie_perm n).map _).trans hf.symm
  · rename_i hn
    rw [hn] at hf
    exact hf.symm

/-- **In byte order, each once**: on a `DistinctLetters` trie the answer strictly ascends. With
`keysWithPrefix_perm` this fixes the list: one strictly ascending arrangement of a set exists. -/
theorem keysWithPrefix_sorted {α : Type} (t : Trie α) (h : DistinctLetters t) (p : List Nat) :
    (keysWithPrefix t p).Pairwise (· < ·) := by
  unfold keysWithPrefix
  split
  · rename_i n hn
    rw [collect_eq, List.pairwise_map]
    exact (words_sortTrie_sorted n (distinctLetters_nodeAt p t h n hn)).imp
      fun hxy => (append_lt_append_same p).mpr hxy
  · exact List.Pairwise.nil

/-- **The list is fixed**: on a `DistinctLetters` trie, any strictly ascending arrangement of the
stored words that begin with `p` is `keysWithPrefix t p`. -/
theorem keysWithPrefix_unique {α : Type} (t : Trie α) (h : DistinctLetters t) (p : List Nat)
    (l : List (List Nat)) (hl : l.Pairwise (· < ·))
    (hperm : l.Perm ((words t).filter (p.isPrefixOf ·))) : l = keysWithPrefix t p :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => absurd (List.lt_trans h₁ h₂) (List.lt_irrefl _))
    hl (keysWithPrefix_sorted t h p) (hperm.trans (keysWithPrefix_perm t h p).symm)

/-! ### `longest_prefix` -/

/-- The loop of `trie.rs`'s and `trie.py`'s `longest_prefix`, standing on a node with `rest` of the
key still to read, `consumed` symbols read, and `best` the length of the longest stored prefix met
so far: step to the child filed under the next symbol, remembering it if it holds a value, and stop
with `best` where there is none or the key runs out. -/
def lpGo {α : Type} : Trie α → List Nat → Nat → Option Nat → Option Nat
  | .node _ _, [], _, best => best
  | .node _ cs, c :: rest, consumed, best =>
      match cs.find? (fun p => p.1 == c) with
      | some (_, .node v ds) =>
          lpGo (.node v ds) rest (consumed + 1) (if v.isSome then some (consumed + 1) else best)
      | none => best
termination_by structural _ k => k

/-- **`longest_prefix` on a trie.** Start at the root with `best` set if the root holds a value,
run the loop over the whole key, and return the key cut to `best`. -/
def longestPrefix {α : Type} (t : Trie α) (k : List Nat) : Option (List Nat) :=
  match t with
  | .node v cs => (lpGo (.node v cs) k 0 (if v.isSome then some 0 else none)).map (k.take ·)

/-- A stored key `j` symbols long begins `x`: `get` answers the first `j` symbols of `x`. -/
def Hit {α : Type} (t : Trie α) (x : List Nat) (j : Nat) : Prop :=
  j ≤ x.length ∧ (get t (x.take j)).isSome = true

instance {α : Type} (t : Trie α) (x : List Nat) (j : Nat) : Decidable (Hit t x j) :=
  by unfold Hit; infer_instance

/-- **The loop.** If `j ≥ 1` is the longest cut of `rest` that `get` answers, the loop returns
`consumed + j`; if `get` answers no cut but the empty one, it returns `best`. -/
theorem lpGo_spec {α : Type} :
    (rest : List Nat) → (t : Trie α) → (consumed : Nat) → (best : Option Nat) →
      ((∀ j, Hit t rest j → j = 0) → lpGo t rest consumed best = best) ∧
      (∀ j, 1 ≤ j → Hit t rest j → (∀ j', Hit t rest j' → j' ≤ j) →
          lpGo t rest consumed best = some (consumed + j))
  | [], .node v cs, consumed, best => by
      refine ⟨fun _ => by simp [lpGo], fun j hj h _ => ?_⟩
      have := h.1; simp at this; omega
  | c :: r, .node v cs, consumed, best => by
      -- a cut `i + 1` of `c :: r` is answered exactly when the child under `c` answers cut `i`
      have hshift : ∀ i, Hit (.node v cs) (c :: r) (i + 1) ↔
          (match cs.find? (fun p => p.1 == c) with
           | some q => Hit q.2 r i
           | none => False) := by
        intro i
        rcases hq : cs.find? (fun p => p.1 == c) with _ | q
        · simp [Hit, get, hq]
        · simp [Hit, get, hq]
      simp only [lpGo]
      split
      · rename_i e w ds hq
        rw [hq] at hshift
        have hit0 : Hit (.node w ds) r 0 ↔ w.isSome = true := by simp [Hit, get]
        obtain ⟨hnone, hsome⟩ := lpGo_spec r (.node w ds) (consumed + 1)
          (if w.isSome then some (consumed + 1) else best)
        refine ⟨fun h0 => ?_, fun j hj hhit hmax => ?_⟩
        · have hall : ∀ i, Hit (.node w ds) r i → False := fun i hi =>
            absurd (h0 (i + 1) ((hshift i).mpr hi)) (by omega)
          have hw : w.isSome = false := by
            cases h : w.isSome
            · rfl
            · exact (hall 0 (hit0.mpr h)).elim
          simpa [hw] using hnone (fun i hi => (hall i hi).elim)
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          have hi := (hshift i).mp hhit
          have hmax' : ∀ i', Hit (.node w ds) r i' → i' ≤ i := fun i' hi' => by
            have := hmax (i' + 1) ((hshift i').mpr hi'); omega
          by_cases h1 : 1 ≤ i
          · rw [hsome i h1 hi hmax']
            congr 1
            omega
          · have hi0 : i = 0 := by omega
            subst hi0
            rw [hnone (fun i' hi' => by have := hmax' i' hi'; omega), hit0.mp hi]
            rfl
      · rename_i hq
        rw [hq] at hshift
        refine ⟨fun _ => rfl, fun j hj hhit _ => ?_⟩
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        exact ((hshift i).mp hhit).elim

/-- Where a stored key begins `x`, a longest one does. -/
theorem exists_greatest_hit {α : Type} {t : Trie α} {x : List Nat} {j : Nat}
    (h : Hit t x j) : ∃ J, Hit t x J ∧ ∀ j', Hit t x j' → j' ≤ J :=
  ⟨Nat.findGreatest (Hit t x) x.length, Nat.findGreatest_spec h.1 h,
    fun _ hj' => Nat.le_findGreatest hj'.1 hj'⟩

/-- **What `longest_prefix` returns, through `get`, on every trie**: the key cut to the longest
length at which `get` answers, or `none` if it answers at none. -/
theorem longestPrefix_eq_some_iff_get {α : Type} (t : Trie α) (k q : List Nat) :
    longestPrefix t k = some q ↔ ∃ j, q = k.take j ∧ Hit t k j ∧ ∀ j', Hit t k j' → j' ≤ j := by
  obtain ⟨v, cs⟩ := t
  obtain ⟨hnone, hsome⟩ := lpGo_spec k (.node v cs) 0 (if v.isSome then some 0 else none)
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

/-- **What `longest_prefix` returns**, on a `DistinctLetters` trie: `some q` exactly when `q` is a
stored key, a prefix of `k`, and no stored key that is a prefix of `k` is longer. -/
theorem longestPrefix_eq_some_iff {α : Type} (t : Trie α) (h : DistinctLetters t) (k q : List Nat) :
    longestPrefix t k = some q ↔
      q ∈ words t ∧ q <+: k ∧ ∀ q' ∈ words t, q' <+: k → q'.length ≤ q.length := by
  have hk : ∀ j, Hit t k j ↔ j ≤ k.length ∧ k.take j ∈ words t := fun j => by
    rw [Hit, mem_words_iff _ t h]
  rw [longestPrefix_eq_some_iff_get]
  simp only [hk]
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

/-- **`longest_prefix` answers `none`**, on a `DistinctLetters` trie, exactly when no stored key is
a prefix of `k`. -/
theorem longestPrefix_eq_none_iff {α : Type} (t : Trie α) (h : DistinctLetters t) (k : List Nat) :
    longestPrefix t k = none ↔ ∀ q ∈ words t, ¬ q <+: k := by
  have hk : ∀ j, Hit t k j ↔ j ≤ k.length ∧ k.take j ∈ words t := fun j => by
    rw [Hit, mem_words_iff _ t h]
  rw [Option.eq_none_iff_forall_ne_some]
  constructor
  · intro hn q hq hpre
    obtain ⟨J, hJ, hmax⟩ := exists_greatest_hit
      ((hk q.length).mpr ⟨hpre.length_le, by rwa [← List.prefix_iff_eq_take.mp hpre]⟩)
    exact hn (k.take J) ((longestPrefix_eq_some_iff_get t k _).mpr ⟨J, rfl, hJ, hmax⟩)
  · intro hn q hq
    obtain ⟨j, _, hj, _⟩ := (longestPrefix_eq_some_iff_get t k q).mp hq
    obtain ⟨_, hjk⟩ := (hk j).mp hj
    exact hn _ hjk (List.take_prefix j k)

end Trie

end AlgoDesign.Strings
