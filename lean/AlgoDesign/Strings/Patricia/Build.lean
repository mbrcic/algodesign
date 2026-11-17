/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Insert

/-!
# Patricia: two constructions, one tree
Compressing the trie the insertions built, and inserting key by key while splitting edges, give the
same tree, child order included: `insert_ofTrie` on every `NoDeadBranches` trie, so
`ofList_eq_ofTrie` from empty.
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-! ## Two constructions, one tree

The hypothesis is the trie's `NoDeadBranches`: `ofTrie` compresses a valueless leaf away once a
key passes through it, while `insert` would leave it as a chain. -/

open Trie (NoDeadBranches NoDeadBranchesNode NoDeadBranchesChildren noDeadBranches_empty
    noDeadBranches_insert length_updateChild)

private theorem branchesUnlessWordEndsNode_glue {α : Type} (c : Nat) (p : Patricia α)
    (hp : BranchesUnlessWordEnds p) (hleaf : p ≠ .node none []) :
    BranchesUnlessWordEndsNode (glue c p).2 := by
  match p with
  | .node none [(lbl, t)] => exact hp.1
  | .node none [] => exact absurd rfl hleaf
  | .node none (_ :: _ :: _) => exact ⟨Or.inr (by simp), hp⟩
  | .node (some _) _ => exact ⟨Or.inl (by simp), hp⟩

private theorem ofTrieAux_eq_nil {α : Type} :
    (cs : List (Nat × Trie α)) → ofTrieAux cs = [] → cs = []
  | [], _ => rfl
  | _ :: _, h => by simp [ofTrieAux] at h

private theorem ofTrie_ne_leaf {α : Type} {s : Trie α} (h : NoDeadBranchesNode s) :
    ofTrie s ≠ .node none [] := by
  cases s with
  | node v cs =>
      intro he
      simp only [ofTrie, Patricia.node.injEq] at he
      exact h.1 (ofTrieAux_eq_nil cs he.2) he.1

mutual

/-- **Compressing a `NoDeadBranches` trie lands in `BranchesUnlessWordEnds`** (box line 3), which
incremental insertion keeps: every node below the root carries a value or branches. Box line 4
holds of every compressed trie (`noEmptyBranches_ofTrie`). -/
theorem branchesUnlessWordEnds_ofTrie {α : Type} :
    (t : Trie α) → NoDeadBranches t → BranchesUnlessWordEnds (ofTrie t)
  | .node _ cs, h => branchesUnlessWordEndsChildren_ofTrieAux cs h

/-- The child-list half of `branchesUnlessWordEnds_ofTrie`. -/
theorem branchesUnlessWordEndsChildren_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → NoDeadBranchesChildren cs →
      BranchesUnlessWordEndsChildren (ofTrieAux cs)
  | [], _ => trivial
  | p :: rest, ⟨h1, h2⟩ =>
      ⟨branchesUnlessWordEndsNode_glue p.1 (ofTrie p.2)
          (branchesUnlessWordEnds_ofTrie p.2 h1.noDeadBranches) (ofTrie_ne_leaf h1),
        branchesUnlessWordEndsChildren_ofTrieAux rest h2⟩

end

/-- `insertAux`'s work at the edge it changes, named: the edge `c :: lbl` over `t`, and the key
`c :: rest` arriving at it. -/
def splitEdge {α : Type} (c : Nat) (lbl : List Nat) (t : Patricia α) (rest : List Nat)
    (a : α) : List Nat × Patricia α :=
  match splitCommon lbl rest with
  | (_, [], keyRest) => (c :: lbl, insert t keyRest a)
  | (pre, d :: lr, []) => (c :: pre, .node (some a) [(d :: lr, t)])
  | (pre, d :: lr, f :: kr) =>
      (c :: pre, .node none [(d :: lr, t), (f :: kr, .node (some a) [])])

theorem insertAux_cons_self {α : Type} (c : Nat) (lbl : List Nat) (t : Patricia α)
    (ps : List (List Nat × Patricia α)) (rest : List Nat) (a : α) :
    insertAux ((c :: lbl, t) :: ps) c rest a = splitEdge c lbl t rest a :: ps := by
  simp only [insertAux, ↓reduceIte, splitEdge]
  generalize splitCommon lbl rest = s
  rcases s with ⟨pre, _ | ⟨d, lr⟩, _ | ⟨f, kr⟩⟩ <;> rfl

/-- One more matching symbol in front of both the label and the key moves the split one symbol
down, and changes nothing else. -/
private theorem splitEdge_cons {α : Type} (c d : Nat) (lbl : List Nat) (t : Patricia α)
    (r : List Nat) (a : α) :
    splitEdge c (d :: lbl) t (d :: r) a
      = (c :: (splitEdge d lbl t r a).1, (splitEdge d lbl t r a).2) := by
  simp only [splitEdge, splitCommon, ↓reduceIte]
  generalize splitCommon lbl r = s
  rcases s with ⟨pre, _ | ⟨d', lr⟩, _ | ⟨f, kr⟩⟩ <;> rfl

private theorem glue_eq_cons {α : Type} (c : Nat) (p : Patricia α) :
    ∃ lbl t, glue c p = (c :: lbl, t) := by
  match p with
  | .node none [(lbl, t)] => exact ⟨lbl, t, rfl⟩
  | .node none [] | .node none (_ :: _ :: _) | .node (some _) _ => exact ⟨[], _, rfl⟩

private theorem glue_flat {α : Type} (c : Nat) (v : Option α) (ps : List (List Nat × Patricia α))
    (h : v ≠ none ∨ 2 ≤ ps.length) : glue c (.node v ps) = ([c], .node v ps) := by
  match v, ps with
  | some _, _ => rfl
  | none, [] => simp at h
  | none, [_] => simp at h
  | none, _ :: _ :: _ => rfl

private theorem length_ofTrieAux {α : Type} :
    (cs : List (Nat × Trie α)) → (ofTrieAux cs).length = cs.length
  | [] => rfl
  | _ :: rest => by simp [ofTrieAux, length_ofTrieAux rest]

/-- A key inserted into the empty trie is a chain, and compresses to one edge carrying it. -/
private theorem glue_ofTrie_chain {α : Type} (a : α) :
    (r : List Nat) → (c : Nat) →
      glue c (ofTrie (Trie.insert Trie.empty r a)) = (c :: r, .node (some a) [])
  | [], _ => rfl
  | d :: r, c => by
      have h : ofTrie (Trie.insert Trie.empty (d :: r) a)
          = .node none [glue d (ofTrie (Trie.insert Trie.empty r a))] := rfl
      rw [h, glue_ofTrie_chain a r d]
      rfl

/-- A trie node that holds a value or branches still does after an insertion. -/
private theorem flat_insert {α : Type} (v : Option α) (cs : List (Nat × Trie α))
    (h : v ≠ none ∨ 2 ≤ cs.length) (k : List Nat) (a : α) :
    ∃ v' cs', Trie.insert (.node v cs) k a = .node v' cs' ∧ (v' ≠ none ∨ 2 ≤ cs'.length) := by
  cases k with
  | nil => exact ⟨some a, cs, rfl, Or.inl (by simp)⟩
  | cons c rest =>
      simp only [Trie.insert]
      split
      · exact ⟨v, _, rfl, h.imp id fun h => by rw [length_updateChild]; exact h⟩
      · exact ⟨v, _, rfl, h.imp id fun h => by simp; omega⟩

/-- The edge step where the trie node below the edge holds a value or branches: compression
gives it an edge of its own, one symbol long, and the insertion descends straight into it. -/
private theorem splitEdge_flat {α : Type} (a : α) (v : Option α) (cs : List (Nat × Trie α))
    (h : v ≠ none ∨ 2 ≤ cs.length) (rest : List Nat)
    (hM : insert (ofTrie (.node v cs)) rest a = ofTrie (Trie.insert (.node v cs) rest a))
    (c : Nat) (lbl : List Nat) (T : Patricia α)
    (hg : glue c (ofTrie (.node v cs)) = (c :: lbl, T)) :
    splitEdge c lbl T rest a = glue c (ofTrie (Trie.insert (.node v cs) rest a)) := by
  have hl : (ofTrieAux cs).length = cs.length := length_ofTrieAux cs
  have g1 : glue c (ofTrie (.node v cs)) = ([c], ofTrie (.node v cs)) :=
    glue_flat c v _ (by rw [hl]; exact h)
  rw [g1] at hg
  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hg
  obtain ⟨rfl, rfl⟩ := hg
  obtain ⟨v', cs', he, h'⟩ := flat_insert v cs h rest a
  rw [he] at hM ⊢
  have hl' : (ofTrieAux cs').length = cs'.length := length_ofTrieAux cs'
  have g2 : glue c (ofTrie (.node v' cs')) = ([c], ofTrie (.node v' cs')) :=
    glue_flat c v' _ (by rw [hl']; exact h')
  rw [g2, ← hM]
  rfl

/-- The edge step of `insert_ofTrie`: at the edge compression built for a trie child `s`, the
split `insert` performs is the edge compression builds for `s` after the trie insert. Proved by
induction on the key, since a chain in the trie is walked one symbol per step. -/
private theorem splitEdge_ofTrie {α : Type} (a : α) (rest : List Nat) :
    (∀ r : List Nat, r.length ≤ rest.length → ∀ s : Trie α, NoDeadBranches s →
      insert (ofTrie s) r a = ofTrie (Trie.insert s r a)) →
    ∀ (s : Trie α) (c : Nat) (lbl : List Nat) (T : Patricia α), NoDeadBranchesNode s →
      glue c (ofTrie s) = (c :: lbl, T) →
      splitEdge c lbl T rest a = glue c (ofTrie (Trie.insert s rest a)) := by
  induction rest with
  | nil =>
      intro hM s c lbl T hs hg
      obtain ⟨v, cs⟩ := s
      rcases v with _ | v
      · rcases cs with _ | ⟨⟨d, s'⟩, _ | ⟨p2, ps⟩⟩
        · exact absurd rfl (hs.1 rfl)
        · obtain ⟨L', T', hg'⟩ := glue_eq_cons d (ofTrie s')
          have ho : ofTrie (.node none [(d, s')]) = .node none [(d :: L', T')] := by
            simp only [ofTrie, ofTrieAux, hg']
          rw [ho] at hg
          simp only [glue, Prod.mk.injEq, List.cons.injEq, true_and] at hg
          obtain ⟨rfl, rfl⟩ := hg
          simp only [Trie.insert, ofTrie, ofTrieAux, hg']
          rfl
        · exact splitEdge_flat a none _ (Or.inr (by simp)) []
            (hM [] (Nat.le_refl _) _ hs.noDeadBranches)
            c lbl T hg
      · exact splitEdge_flat a (some v) cs (Or.inl (by simp)) []
          (hM [] (Nat.le_refl _) _ hs.noDeadBranches)
          c lbl T hg
  | cons e r ih =>
      intro hM s c lbl T hs hg
      obtain ⟨v, cs⟩ := s
      rcases v with _ | v
      · rcases cs with _ | ⟨⟨d, s'⟩, _ | ⟨p2, ps⟩⟩
        · exact absurd rfl (hs.1 rfl)
        · obtain ⟨L', T', hg'⟩ := glue_eq_cons d (ofTrie s')
          have ho : ofTrie (.node none [(d, s')]) = .node none [(d :: L', T')] := by
            simp only [ofTrie, ofTrieAux, hg']
          rw [ho] at hg
          simp only [glue, Prod.mk.injEq, List.cons.injEq, true_and] at hg
          obtain ⟨rfl, rfl⟩ := hg
          by_cases hed : e = d
          · subst hed
            rw [splitEdge_cons,
              ih (fun r' hr' => hM r' (by simp only [List.length_cons]; omega)) s' e L' T'
                hs.2.1 hg']
            obtain ⟨L2, T2, h2⟩ := glue_eq_cons e (ofTrie (Trie.insert s' r a))
            have hi : Trie.insert (.node none [(e, s')]) (e :: r) a
                = .node none [(e, Trie.insert s' r a)] := by
              simp [Trie.insert, Trie.updateChild]
            rw [hi, h2]
            simp only [ofTrie, ofTrieAux, h2]
            rfl
          · have hde : ¬ d = e := fun h => hed h.symm
            have hi : Trie.insert (.node none [(d, s')]) (e :: r) a
                = .node none [(d, s'), (e, Trie.insert Trie.empty r a)] := by
              simp [Trie.insert, hde]
            rw [hi]
            simp only [ofTrie, ofTrieAux, hg', glue_ofTrie_chain]
            simp only [splitEdge, splitCommon, hde, ↓reduceIte]
            rfl
        · exact splitEdge_flat a none _ (Or.inr (by simp)) (e :: r)
            (hM _ (Nat.le_refl _) _ hs.noDeadBranches) c lbl T hg
      · exact splitEdge_flat a (some v) cs (Or.inl (by simp)) (e :: r)
          (hM _ (Nat.le_refl _) _ hs.noDeadBranches) c lbl T hg

/-- The child-list step of `insert_ofTrie`: `insertAux` over a compressed child list is the
compression of the child list `Trie.insert` produces. -/
private theorem insertAux_ofTrieAux {α : Type} (c : Nat) (rest : List Nat) (a : α)
    (hE : ∀ (s : Trie α) (lbl : List Nat) (T : Patricia α), NoDeadBranchesNode s →
      glue c (ofTrie s) = (c :: lbl, T) →
      splitEdge c lbl T rest a = glue c (ofTrie (Trie.insert s rest a))) :
    (cs : List (Nat × Trie α)) → NoDeadBranchesChildren cs →
      insertAux (ofTrieAux cs) c rest a
        = ofTrieAux (if cs.any (fun p => p.1 == c)
            then Trie.updateChild c (fun t => Trie.insert t rest a) cs
            else cs ++ [(c, Trie.insert Trie.empty rest a)])
  | [], _ => by
      simp only [ofTrieAux, List.any_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append,
        glue_ofTrie_chain]
      rfl
  | (d, s) :: ps, ⟨h1, h2⟩ => by
      obtain ⟨L, T, hg⟩ := glue_eq_cons d (ofTrie s)
      by_cases hdc : d = c
      · subst hdc
        have hany : ((d, s) :: ps).any (fun p => p.1 == d) = true := by simp
        simp only [hany, ↓reduceIte]
        simp only [ofTrieAux, hg, insertAux_cons_self, Trie.updateChild, beq_self_eq_true,
          ↓reduceIte, hE s L T h1 hg]
      · have hb : (d == c) = false := by simp [hdc]
        have ih := insertAux_ofTrieAux c rest a hE ps h2
        have hl : insertAux ((d :: L, T) :: ofTrieAux ps) c rest a
            = (d :: L, T) :: insertAux (ofTrieAux ps) c rest a := by
          simp only [insertAux, hdc, ↓reduceIte]
        simp only [ofTrieAux, hg, hl, ih, List.any_cons, hb, Bool.false_or]
        split
        · simp only [Trie.updateChild, hb, Bool.false_eq_true, ↓reduceIte, ofTrieAux, hg]
        · simp only [List.cons_append, ofTrieAux, hg]

private theorem insert_ofTrie_le {α : Type} (a : α) :
    (n : Nat) → (k : List Nat) → k.length ≤ n → (t : Trie α) → NoDeadBranches t →
      insert (ofTrie t) k a = ofTrie (Trie.insert t k a)
  | _, [], _, .node _ _, _ => rfl
  | 0, _ :: _, hk, _, _ => by simp at hk
  | n + 1, c :: rest, hk, .node v cs, h => by
      have hE := splitEdge_ofTrie a rest (fun r hr s hs =>
        insert_ofTrie_le a n r (by simp only [List.length_cons] at hk; omega) s hs)
      have hA := insertAux_ofTrieAux c rest a (fun s lbl T hs hg => hE s c lbl T hs hg) cs h
      change Patricia.node v (insertAux (ofTrieAux cs) c rest a) = _
      rw [hA]
      simp only [Trie.insert]
      split <;> rfl

/-- **Inserting into the compressed tree is compressing after the trie insert**, on every
`NoDeadBranches` trie: `insert` splits exactly the edge whose trie chain the new key leaves, at the
symbol where it leaves it, and appends a new edge exactly where the trie appends a new child. -/
theorem insert_ofTrie {α : Type} (t : Trie α) (k : List Nat) (a : α) (h : NoDeadBranches t) :
    insert (ofTrie t) k a = ofTrie (Trie.insert t k a) :=
  insert_ofTrie_le a k.length k (Nat.le_refl _) t h

/-- The tree `insert` builds from a list of key/value pairs, starting from the empty tree. -/
def ofList {α : Type} (kvs : List (List Nat × α)) : Patricia α :=
  kvs.foldl (fun t p => insert t p.1 p.2) (.node none [])

private theorem foldl_insert_ofTrie {α : Type} :
    (kvs : List (List Nat × α)) → (t : Trie α) → NoDeadBranches t →
      kvs.foldl (fun p q => insert p q.1 q.2) (ofTrie t)
        = ofTrie (kvs.foldl (fun p q => Trie.insert p q.1 q.2) t)
  | [], _, _ => rfl
  | q :: qs, t, h => by
      simp only [List.foldl_cons]
      rw [insert_ofTrie t q.1 q.2 h]
      exact foldl_insert_ofTrie qs _ (noDeadBranches_insert q.1 q.2 h)

/-- **The two constructions build the same tree.** Inserting the pairs one by one, splitting
edges, gives exactly the compression of the trie the same insertions build: the same labels, the
same values (the last one inserted for a repeated key), and the same child order. -/
theorem ofList_eq_ofTrie {α : Type} (kvs : List (List Nat × α)) :
    ofList kvs = ofTrie (kvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty) :=
  foldl_insert_ofTrie kvs Trie.empty noDeadBranches_empty

/-- The key list of an incrementally built tree is the key list of the trie the same insertions
build, in the same order. -/
theorem words_ofList {α : Type} (kvs : List (List Nat × α)) :
    (ofList kvs).words = (kvs.foldl (fun t p => Trie.insert t p.1 p.2) Trie.empty).words := by
  rw [ofList_eq_ofTrie, words_ofTrie]

end Patricia

end AlgoDesign.Strings
