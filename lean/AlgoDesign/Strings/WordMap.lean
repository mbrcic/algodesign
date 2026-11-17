/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Data.List.Basic

/-!
# The trie's promise

The Strings chapter's trie and Patricia boxes share one promise, "the trie's":

> **Promise:** a map from words to values. Get gives a word's stored value, or nothing. Insert
> stores or replaces one word's value; remove deletes it. Other words stay unchanged. Every word
> that starts with a given prefix can be listed.

This file is that promise, as the reader checks it: the operations a word map offers (`WordMap`),
and the laws they obey on every valid map (`Promise`), one law per sentence. A word is a list of
symbols (`List Nat`). Each structure states its contract as `Contract` in its `Spec.lean` and proves
it in its umbrella file. A design that changes the representation (a ternary search trie, an AI's
candidate) is held to these same laws. The laws hold on every valid map. So that `Valid := False`
cannot meet them, each structure's `Ops` asks that the empty map is valid and that insert and remove
keep it valid.

The first two sentences are the type of `get`: a word's value, or nothing. Every law speaks
through `get`, so the stored words are the ones `get` has a value for, and the prefix listing is
pinned to them.

**Counted steps.** Each structure's `Contract` bounds the steps its counted get (`getM`) reports,
and ties its answer to `get`. What such a bound holds, and what it does not, is said once, at
`SearchTree.Within` (`Searching/SearchTree.lean`).
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- **Goal:** the operations a word map needs, over states `S` holding values of type `α`, and the
invariant the design keeps. A design that leaves one out does not typecheck. -/
structure WordMap (α S : Type) where
  /-- The map holding no word. -/
  empty : S
  /-- Store a word's value, or replace it. -/
  insert : List Nat → α → S → S
  /-- Delete a word. -/
  remove : List Nat → S → S
  /-- Get: a word's stored value, or nothing. -/
  get : List Nat → S → Option α
  /-- The stored words that start with a given prefix. -/
  keysWithPrefix : List Nat → S → List (List Nat)
  /-- The design's invariants. -/
  Valid : S → Prop

namespace WordMap

variable {α S : Type} (m : WordMap α S)

/-- **Promise:** a map from words to values, on every valid map. "Get gives a word's stored
value, or nothing" is `get`'s type. -/
structure Promise : Prop where
  /-- The empty map holds no word. -/
  get_empty : ∀ w, m.get w m.empty = none
  /-- "Insert stores or replaces one word's value." -/
  insert_stores : ∀ w a s, m.Valid s → m.get w (m.insert w a s) = some a
  /-- "Remove deletes it." -/
  remove_deletes : ∀ w s, m.Valid s → m.get w (m.remove w s) = none
  /-- "Other words stay unchanged", by insert and by remove. -/
  others_unchanged : ∀ w v s, m.Valid s → v ≠ w →
    (∀ a, m.get v (m.insert w a s) = m.get v s) ∧ m.get v (m.remove w s) = m.get v s
  /-- "Every word that starts with a given prefix can be listed": the listing holds exactly the
  stored words that start with `p`, each once. -/
  lists_prefix : ∀ p s, m.Valid s →
    (∀ w, w ∈ m.keysWithPrefix p s ↔ p <+: w ∧ m.get w s ≠ none) ∧
      (m.keysWithPrefix p s).Nodup

variable {m}

/-- The prefix law from facts stated with a structure's own list of stored words `words`, the form
the trie and Patricia libraries prove them in: `words` holds the words `get` has a value for, and
the listing is the stored words that start with `p`, rearranged, in strictly increasing order. -/
theorem lists_prefix_of_words (words : S → List (List Nat)) {s : S} (p : List Nat)
    (mem_words : ∀ w, w ∈ words s ↔ (m.get w s).isSome)
    (perm : (m.keysWithPrefix p s).Perm ((words s).filter (p.isPrefixOf ·)))
    (sorted : (m.keysWithPrefix p s).Pairwise (· < ·)) :
    (∀ w, w ∈ m.keysWithPrefix p s ↔ p <+: w ∧ m.get w s ≠ none) ∧
      (m.keysWithPrefix p s).Nodup := by
  refine ⟨fun w => ?_, sorted.imp fun {a b} (h : a < b) (e : a = b) => List.lt_irrefl a (e ▸ h)⟩
  rw [perm.mem_iff, List.mem_filter, mem_words, List.isPrefixOf_iff_prefix,
    Option.isSome_iff_ne_none]
  exact and_comm

end WordMap

end AlgoDesign.Strings
