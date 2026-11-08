/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.Finset.Sort
public import Cslib.Algorithms.Lean.TimeM
public import AlgoDesign.Searching.RangeQuery

/-!
# The search tree's promise

The Search chapter's BST, LLRB and B-tree boxes share one promise, "the search tree's":

> **Promise:** a set, kept in order. Search says whether a key is there. Insert adds a key; delete
> takes one out. Every other key stays in the set. The keys come out in increasing order, so the
> next larger key and every key in a range can be read off.

This file is that promise, as the reader checks it: the operations a search tree offers
(`SearchTree`), and the laws they obey on every valid tree (`Promise`), one law per sentence; the
last sentence's two reads, `nextLarger` and `range`, keep theirs on every such tree
(`Promise.nextLarger_spec`, `Promise.range_spec`). Each
tree states its contract as `Contract` in its `Spec.lean` and proves it after its operations. A
design that changes the representation (a new tree, an AI's candidate) is held to these same laws.
The laws hold on every valid tree. So that `Valid := False` cannot meet them, each tree's `Ops`
asks that the empty tree is valid and that insert and delete keep it valid.

`keys` reads what a tree holds off its in-order listing, so "every other key stays" is inside
`insert_adds` and `delete_takes`, and `in_order` pins the listing's contents, uniqueness and order
at once.
-/

@[expose] public section

namespace AlgoDesign.Searching

/-- **Goal:** the operations the job needs, over states `S`, and the invariant the design keeps.
A design that leaves one out does not typecheck. -/
structure SearchTree (α S : Type) where
  /-- The empty tree. -/
  empty : S
  /-- Add a key. -/
  insert : α → S → S
  /-- Take a key out. -/
  delete : α → S → S
  /-- Is the key there? -/
  search : α → S → Bool
  /-- The keys, in the order the tree gives them. -/
  toList : S → List α
  /-- The design's invariants. -/
  Valid : S → Prop

namespace SearchTree

variable {α S : Type} [LinearOrder α] (t : SearchTree α S)

/-- What a tree holds. -/
def keys (s : S) : Finset α := (t.toList s).toFinset

/-- **The set laws**, the core every set design keeps, stated on raw operations and a meaning
`keys`: the search tree's `Promise` adds the ordered listing to them, and the design project's
`Workbench.Contract` (`Workbench/Spec.lean`) adds the answers and "next larger". -/
structure SetLaws {S : Type} (empty : S) (insert delete : α → S → S) (search : α → S → Bool)
    (keys : S → Finset α) (Valid : S → Prop) : Prop where
  /-- The empty tree holds nothing. -/
  keys_empty : keys empty = ∅
  /-- "Insert adds a key", and every other key stays. -/
  insert_adds : ∀ a s, Valid s → keys (insert a s) = keys s ∪ {a}
  /-- "Delete takes one out", and every other key stays. -/
  delete_takes : ∀ a s, Valid s → keys (delete a s) = keys s \ {a}
  /-- "Search says whether a key is there." -/
  search_says : ∀ a s, Valid s → (search a s = true ↔ a ∈ keys s)

/-- **Promise:** a set, kept in order, on every valid tree. "The next larger key and every key in a
range can be read off" is proved for every search tree from this, `Promise.nextLarger_spec` and
`Promise.range_spec`. -/
structure Promise : Prop extends SetLaws t.empty t.insert t.delete t.search t.keys t.Valid where
  /-- "The keys come out in increasing order": exactly the keys, once each, increasing. -/
  in_order : ∀ s, t.Valid s → t.toList s = (t.keys s).sort (· ≤ ·)

/-- How many keys a tree holds: the `n` every cost bound is in, read off what the tree holds, so
no design picks its own. -/
def size (s : S) : ℕ := (t.keys s).card

open Cslib.Algorithms.Lean in
/-- **Cost:** a counted operation takes at most `bound n` steps on every valid tree of `n ≥ 1`
keys.

**What this holds, and what it does not.** The steps are the ones the operation counts itself:
Lean proves the bound for that counting, and does not check that the counting is honest. A
wrapper that counts nothing meets every `Within`. So the library's counting functions are named
in each `Spec.lean`, and a separate check fails when the statement of one changes,
which catches one being swapped or a tick removed; a counter written dishonestly from the start is
caught only by reading it. This is said once, here, for every counted bound in the library.
Where a design must not count its own steps (an AI's candidate), the workbench's counted memory
(`python/algodesign/searching/workbench.py`) measures it instead. -/
def Within {β : Type} (counted : α → S → TimeM ℕ β) (bound : ℕ → ℕ) : Prop :=
  ∀ a s, t.Valid s → 0 < t.size s → (counted a s).time ≤ bound (t.size s)

open Cslib.Algorithms.Lean in
/-- **The design target "short":** search, insert and delete each in at most `c · log₂(n + 1)`
counted steps on every valid tree of `n ≥ 1` keys. A new design is asked for this; the BST does
not meet it (sorted input makes its paths `n` long), the LLRB meets it for search and insert, the
B-tree for all three. -/
def Logarithmic {β γ δ : Type} (c : ℕ) (searchM : α → S → TimeM ℕ β)
    (insertM : α → S → TimeM ℕ γ) (deleteM : α → S → TimeM ℕ δ) : Prop :=
  t.Within searchM (fun n => c * Nat.log2 (n + 1)) ∧
  t.Within insertM (fun n => c * Nat.log2 (n + 1)) ∧
  t.Within deleteM (fun n => c * Nat.log2 (n + 1))

/-- **What "next larger" owes**, on a set of keys `m`: `some c` exactly when `c` is in `m`, larger
than `k`, and no larger than any other key of `m` above `k`; `none` exactly when no key of `m` is
above `k`. -/
def NextLargerSpec (m : Finset α) (k : α) : Option α → Prop
  | some c => c ∈ m ∧ k < c ∧ ∀ b ∈ m, k < b → c ≤ b
  | none => ∀ b ∈ m, b ≤ k

/-- "The next larger key can be read off": the first key in the listing above `k`. -/
def nextLarger (s : S) (k : α) : Option α := (t.toList s).find? (k < ·)

/-- "Every key in a range can be read off": the listing's keys that the bounds admit. -/
def range (s : S) (lo hi : RangeBound α) : List α := keysInRange lo hi (t.toList s)

open Cslib.Algorithms.Lean in
/-- A bound proved below another, for every `n ≥ 1`, carries over. -/
theorem Within.mono {t : SearchTree α S} {β : Type} {counted : α → S → TimeM ℕ β}
    {b b' : ℕ → ℕ} (h : t.Within counted b) (hb : ∀ n, 0 < n → b n ≤ b' n) :
    t.Within counted b' :=
  fun a s hv hn => (h a s hv hn).trans (hb _ hn)

/-- On a tree that keeps the promise, `size` is the length of its listing. -/
theorem Promise.size_eq_length {t : SearchTree α S} (p : t.Promise) {s : S} (h : t.Valid s) :
    t.size s = (t.toList s).length := by
  rw [p.in_order s h, Finset.length_sort]; rfl

omit [LinearOrder α] in
/-- **Whatever order the keys arrive in**, the tree they build is valid, so every bound proved
for valid trees holds for it. -/
theorem valid_inserts {t : SearchTree α S} (h0 : t.Valid t.empty)
    (hi : ∀ a s, t.Valid s → t.Valid (t.insert a s)) (ks : List α) :
    t.Valid (ks.foldl (fun s a => t.insert a s) t.empty) := by
  suffices h : ∀ s, t.Valid s → t.Valid (ks.foldl (fun s a => t.insert a s) s) from h _ h0
  induction ks with
  | nil => exact fun _ h => h
  | cons k ks ih => exact fun s h => ih _ (hi k s h)

/-- The promise from facts stated with a tree's own membership predicate `mem`, the form each
tree's library proves them in. -/
theorem Promise.of_mem (mem : α → S → Prop)
    (mem_toList : ∀ a s, a ∈ t.toList s ↔ mem a s)
    (toList_empty : t.toList t.empty = [])
    (mem_insert : ∀ a b s, t.Valid s → (mem b (t.insert a s) ↔ b = a ∨ mem b s))
    (mem_delete : ∀ a b s, t.Valid s → (mem b (t.delete a s) ↔ b ≠ a ∧ mem b s))
    (search_correct : ∀ a s, t.Valid s → (t.search a s = true ↔ mem a s))
    (sorted : ∀ s, t.Valid s → (t.toList s).Pairwise (· < ·)) :
    t.Promise where
  keys_empty := by simp [keys, toList_empty]
  insert_adds a s h := by
    ext b; simp [keys, mem_toList, mem_insert a b s h, or_comm]
  delete_takes a s h := by
    ext b; simp [keys, mem_toList, mem_delete a b s h, and_comm]
  search_says a s h := by simp [keys, mem_toList, search_correct a s h]
  in_order s h :=
    ((List.toFinset_sort (· ≤ ·) ((sorted s h).imp ne_of_lt)).2 ((sorted s h).imp le_of_lt)).symm

/-- On a tree that keeps the promise, the listing is strictly increasing. -/
theorem Promise.toList_sorted {t : SearchTree α S} (p : t.Promise) {s : S} (h : t.Valid s) :
    (t.toList s).Pairwise (· < ·) := by
  rw [p.in_order s h]
  exact ((Finset.pairwise_sort _ (· ≤ ·)).and (Finset.sort_nodup _ (· ≤ ·))).imp
    (fun ⟨a, b⟩ => lt_of_le_of_ne a b)

/-- **"Next larger" is read off the listing, and keeps its law** on every tree that keeps the
promise: one proof for every search tree. -/
theorem Promise.nextLarger_spec {t : SearchTree α S} (p : t.Promise) {s : S} (h : t.Valid s)
    (k : α) : NextLargerSpec (t.keys s) k (t.nextLarger s k) := by
  have hl : t.toList s = (t.keys s).sort (· ≤ ·) := p.in_order s h
  have hmem : ∀ b, b ∈ t.toList s ↔ b ∈ t.keys s := fun b => by rw [hl, Finset.mem_sort]
  have hsort : (t.toList s).Pairwise (· < ·) := p.toList_sorted h
  unfold nextLarger
  cases hf : (t.toList s).find? (k < ·) with
  | none =>
    intro b hb
    have := List.find?_eq_none.1 hf b ((hmem b).2 hb)
    simpa using this
  | some c =>
    obtain ⟨hc, as, bs, heq, has⟩ := List.find?_eq_some_iff_append.1 hf
    have hck : k < c := by simpa using hc
    refine ⟨(hmem c).1 (by rw [heq]; simp), hck, fun b hb hkb => ?_⟩
    have hbl : b ∈ as ++ c :: bs := heq ▸ (hmem b).2 hb
    rw [heq, List.pairwise_append, List.pairwise_cons] at hsort
    rcases List.mem_append.1 hbl with hba | hbc
    · exact absurd hkb (by simpa using has b hba)
    · rcases List.mem_cons.1 hbc with rfl | hbs
      · exact le_rfl
      · exact le_of_lt (hsort.2.1.1 b hbs)

/-- **"Every key in a range" is read off the listing, and keeps its law** on every tree that keeps
the promise: exactly the keys the bounds admit, in increasing order. One proof for every search
tree. -/
theorem Promise.range_spec {t : SearchTree α S} (p : t.Promise) {s : S} (h : t.Valid s)
    (lo hi : RangeBound α) :
    (∀ k, k ∈ t.range s lo hi ↔ k ∈ t.keys s ∧ InRange lo hi k) ∧
      (t.range s lo hi).Pairwise (· < ·) :=
  ⟨fun k => by simp [range, keysInRange, keys],
    (p.toList_sorted h).filter _⟩

end SearchTree

end AlgoDesign.Searching
