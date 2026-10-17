/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Basic

/-!
# Patricia: compressing a trie
`ofTrie` collapses a finished trie's valueless single-child chains into labelled edges. It is total
and lossless: the result has no empty branch (`noEmptyBranches_ofTrie`), holds the trie's words
(`words_ofTrie`), answers every lookup as the trie did (`get_ofTrie`), and inherits
`DistinctFirstLetters` from `Trie.DistinctLetters` (`distinctFirstLetters_ofTrie`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-- Prepend a symbol to a subtree, merging with the subtree's own single edge when that subtree is
a valueless one-child node — which is exactly the shape compression exists to remove. -/
def glue {α : Type} (c : Nat) : Patricia α → (List Nat × Patricia α)
  | .node none [(lbl, t)] => (c :: lbl, t)
  | t => ([c], t)

mutual

/-- Collapse a trie's valueless single-child chains into labelled edges. Paired with `ofTrieAux`
rather than written with `List.map` so that the recursion stays structural. -/
def ofTrie {α : Type} : Trie α → Patricia α
  | .node v cs => .node v (ofTrieAux cs)

/-- Compress each child of a trie node, gluing its symbol onto the compressed subtree. -/
def ofTrieAux {α : Type} : List (Nat × Trie α) → List (List Nat × Patricia α)
  | [] => []
  | p :: rest => glue p.1 (ofTrie p.2) :: ofTrieAux rest

end

/-- `glue` emits a non-empty branch: the label it builds holds `c` either way, and the subtree it
returns has no empty branch when its argument has none — in the merging branch it is the
argument's own child. -/
private theorem glue_spec {α : Type} (c : Nat) (p : Patricia α) (hp : NoEmptyBranches p) :
    (glue c p).1 ≠ [] ∧ NoEmptyBranches (glue c p).2 := by
  match p with
  | .node none [(lbl, t)] =>
      simp only [NoEmptyBranches, NoEmptyBranchesChildren] at hp
      exact ⟨by simp [glue], hp.2.1⟩
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ =>
      exact ⟨by simp [glue], hp⟩

mutual

/-- **Compression leaves no empty branch** (box line 4), whatever trie it was given. -/
theorem noEmptyBranches_ofTrie {α : Type} : (t : Trie α) → NoEmptyBranches (ofTrie t)
  | .node _ cs => noEmptyBranchesChildren_ofTrieAux cs

/-- The child-list half of `noEmptyBranches_ofTrie`. -/
theorem noEmptyBranchesChildren_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → NoEmptyBranchesChildren (ofTrieAux cs)
  | [] => trivial
  | p :: rest =>
      ⟨(glue_spec p.1 (ofTrie p.2) (noEmptyBranches_ofTrie p.2)).1,
        (glue_spec p.1 (ofTrie p.2) (noEmptyBranches_ofTrie p.2)).2,
        noEmptyBranchesChildren_ofTrieAux rest⟩

end

/-- Gluing a symbol on contributes exactly the words of the subtree with that symbol in front,
merged label or not. This is the one place the two branches of `glue` have to agree, and they do
because `(c :: lbl) ++ k` is `c :: (lbl ++ k)`. -/
private theorem words_glue {α : Type} (c : Nat) (p : Patricia α) :
    (words (glue c p).2).map ((glue c p).1 ++ ·) = (words p).map (c :: ·) := by
  match p with
  | .node none [(lbl, t)] => simp [glue, words, wordsAux, List.map_map, Function.comp_def]
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ => simp [glue]

mutual

/-- **Compression keeps every key**, which the node count's saving depends on. Compression is a
representation change: the key list is untouched, so a smaller node count is a free lunch and not
a loss. Stronger than the permutation the chapter needs — `ofTrie` keeps the child order, so the
words come out in the same order as well. -/
theorem words_ofTrie {α : Type} : (t : Trie α) → (ofTrie t).words = t.words
  | .node v cs => by
      cases v <;> simp [ofTrie, words, Trie.words, wordsAux_ofTrieAux cs]

/-- The child-list half of `words_ofTrie`. -/
theorem wordsAux_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → wordsAux (ofTrieAux cs) = Trie.wordsAux cs
  | [] => rfl
  | p :: rest => by
      simp [ofTrieAux, wordsAux, Trie.wordsAux, words_glue, words_ofTrie p.2,
        wordsAux_ofTrieAux rest]

end

/-- The permutation form the chapter states, immediate from the equality. -/
theorem words_perm_ofTrie {α : Type} (t : Trie α) : (ofTrie t).words.Perm t.words := by
  rw [words_ofTrie]

/-- `glue c` always emits a label beginning with `c`, merged or not. -/
theorem head?_glue {α : Type} (c : Nat) (p : Patricia α) :
    (glue c p).1.head? = some c := by
  match p with
  | .node none [(lbl, t)] => rfl
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ => rfl

private theorem map_head?_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → (ofTrieAux cs).map (·.1.head?) = (cs.map (·.1)).map some
  | [] => rfl
  | p :: rest => by
      simp only [ofTrieAux, List.map_cons, head?_glue, map_head?_ofTrieAux rest]

/-- Merging a chain away keeps the subtree below it, so it keeps that subtree's invariant. -/
private theorem distinctFirstLetters_glue {α : Type} (c : Nat) (p : Patricia α)
    (hp : DistinctFirstLetters p) : DistinctFirstLetters (glue c p).2 := by
  match p with
  | .node none [(lbl, t)] =>
      simp only [DistinctFirstLetters, DistinctFirstLettersChildren] at hp
      exact hp.2.1
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ => exact hp

mutual

/-- **Compression keeps siblings apart.** A trie child under symbol `c` becomes an edge whose label
begins with `c` — `glue` either emits `[c]` or prepends `c` to the label it merges with — so
distinct symbols among a trie node's children become distinct heads among the compressed node's
edges. Here `Trie.DistinctLetters` is needed: compression renames no edge, so it cannot separate
siblings the trie had already put under one symbol. -/
theorem distinctFirstLetters_ofTrie {α : Type} :
    (t : Trie α) → Trie.DistinctLetters t → DistinctFirstLetters (ofTrie t)
  | .node _ cs, h =>
      ⟨by
        rw [firstLetters, map_head?_ofTrieAux]
        exact List.Pairwise.map some (fun _ _ hne heq => hne (Option.some.inj heq)) h.1,
        distinctFirstLettersChildren_ofTrieAux cs h.2⟩

/-- The child-list half of `distinctFirstLetters_ofTrie`. -/
theorem distinctFirstLettersChildren_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → Trie.DistinctLettersChildren cs →
      DistinctFirstLettersChildren (ofTrieAux cs)
  | [], _ => trivial
  | p :: rest, h =>
      ⟨distinctFirstLetters_glue p.1 (ofTrie p.2) (distinctFirstLetters_ofTrie p.2 h.1),
        distinctFirstLettersChildren_ofTrieAux rest h.2⟩

end

/-- Looking `c :: rest` up through the edge `glue c p` is looking `rest` up in `p`. In the merging
branch the label `c :: lbl` is matched as `c`, then `lbl`, which is exactly the step `p` itself
would take through its single edge. `NoEmptyBranches p` rules out an empty `lbl`, the one shape
where the two would part: asked for the empty key, `p` stops at its own absent value, while the
merged edge would reach past it to the child. -/
private theorem getAux_glue {α : Type} (c : Nat) (p : Patricia α) (hp : NoEmptyBranches p)
    (ps : List (List Nat × Patricia α)) (rest : List Nat) :
    getAux (glue c p :: ps) c rest = get p rest := by
  match p with
  | .node none [(lbl, t)] =>
      simp only [NoEmptyBranches, NoEmptyBranchesChildren] at hp
      cases lbl with
      | nil => exact absurd rfl hp.1
      | cons c' lbl' =>
          cases rest with
          | nil => simp [glue, getAux, get, List.isPrefixOf]
          | cons d rest =>
              by_cases hd : c' = d
              · subst hd; simp [glue, getAux, get, List.isPrefixOf]
              · simp [glue, getAux, get, List.isPrefixOf, hd]
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ => simp [glue, getAux]

/-- An edge glued under another symbol does not answer for `c`. -/
private theorem getAux_glue_other {α : Type} {c c' : Nat} (h : c' ≠ c) (p : Patricia α)
    (ps : List (List Nat × Patricia α)) (rest : List Nat) :
    getAux (glue c' p :: ps) c rest = getAux ps c rest := by
  match p with
  | .node none [(lbl, t)] => simp [glue, getAux, h]
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ => simp [glue, getAux, h]

mutual

/-- **Lookup is unchanged by compression.** Whatever key is asked, the compressed tree answers
what the trie answered. The trie's lookup is already pinned down by `Trie.get_insert` and
`Trie.get_insert_other`, so this is what gives `get` a specification and not only a definition.
No invariant of the trie is needed. Each side commits to the first child filed under the key's first
symbol — `Trie.get` by `List.find?`, `getAux` by taking the first label with that head — and
compression keeps the children in order, so the two pick the same child even in a trie that breaks
`Trie.DistinctLetters`. -/
theorem get_ofTrie {α : Type} : (t : Trie α) → (k : List Nat) → (ofTrie t).get k = t.get k
  | .node v cs, [] => by simp [ofTrie, get, Trie.get]
  | .node v cs, c :: rest => by
      simp only [ofTrie, get, Trie.get]
      exact getAux_ofTrieAux cs c rest

/-- The child-list half of `get_ofTrie`. -/
theorem getAux_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → (c : Nat) → (rest : List Nat) →
      getAux (ofTrieAux cs) c rest
        = match cs.find? (fun p => p.1 == c) with
          | some p => Trie.get p.2 rest
          | none => none
  | [], _, _ => rfl
  | p :: ps, c, rest => by
      by_cases hc : p.1 = c
      · simp only [ofTrieAux, List.find?_cons, hc, beq_self_eq_true]
        rw [← hc, getAux_glue _ _ (noEmptyBranches_ofTrie p.2), get_ofTrie p.2 rest]
      · have hb : (p.1 == c) = false := by simp [hc]
        simp only [ofTrieAux, List.find?_cons, hb]
        rw [getAux_glue_other hc, getAux_ofTrieAux ps c rest]

end

end Patricia

end AlgoDesign.Strings
