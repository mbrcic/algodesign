/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Patricia.Sorted

/-!
# Patricia: removal
`remove`, as `patricia.rs` runs it. On a tree with `NoEmptyBranches` and `DistinctFirstLetters` it
removes exactly its key (`get_remove`, `get_remove_other`, `words_remove`), and it keeps each piece
of `Valid` (`distinctFirstLetters_remove`, `branchesUnlessWordEnds_remove`,
`noEmptyBranches_remove`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Patricia

/-! ## Removal

Removal as `patricia.rs` and `patricia.py` run it. A key that holds no
value changes nothing. Otherwise its value is cleared at the node the key ends on (the *target*),
and then, below the root only:

- a target left with no child is unlinked from its parent, and the parent, if that leaves it
  valueless with a single child, is merged into that child;
- a target left with one child is merged into it;
- a target with two or more children stays, valueless, as a branch point.

A merge concatenates the two labels and takes the lower node's value and children; the merged edge
begins with the same symbol, so it stays where it was filed. `delAux` states this recursively: the
target's edge is rewritten by `dropTarget`, and the edge above a node whose child was unlinked by
`collapse`, which merges exactly when that node is left valueless with one child after having had
two — the Rust's `parent.children.len() == 1` after the unlink. The root is never merged: it has no
edge. -/

/-- A node's child list. -/
def children {α : Type} : Patricia α → List (List Nat × Patricia α)
  | .node _ cs => cs

/-- The target's edge, labelled `lbl`, once its value is cleared: gone if it had no child, merged
into its only child if it had one, a valueless branch point otherwise. -/
def dropTarget {α : Type} (lbl : List Nat) :
    List (List Nat × Patricia α) → List (List Nat × Patricia α)
  | [] => []
  | [(l2, u)] => [(lbl ++ l2, u)]
  | e :: f :: rest => [(lbl, .node none (e :: f :: rest))]

/-- The edge `lbl` above a node `t` below which a removal happened: merged into `t`'s only child
when `t` is valueless with one child and had `n = 2` before, that is when the removal unlinked its
other child. -/
def collapse {α : Type} (lbl : List Nat) (n : Nat) : Patricia α → List Nat × Patricia α
  | .node none [(l2, u)] => if n = 2 then (lbl ++ l2, u) else (lbl, .node none [(l2, u)])
  | .node none [] => (lbl, .node none [])
  | .node none (e :: f :: rest) => (lbl, .node none (e :: f :: rest))
  | .node (some a) cs => (lbl, .node (some a) cs)

mutual

/-- Clear the value at a key and restore the shape below the root. -/
def del {α : Type} : Patricia α → List Nat → Patricia α
  | .node _ cs, [] => .node none cs
  | .node v cs, c :: rest => .node v (delAux cs c rest)

/-- The child-list half of `del`: find the edge `getAux` would take, then rewrite it. -/
def delAux {α : Type} :
    List (List Nat × Patricia α) → Nat → List Nat → List (List Nat × Patricia α)
  | [], _, _ => []
  | ([], t) :: ps, c, rest => ([], t) :: delAux ps c rest
  | (c' :: lbl, t) :: ps, c, rest =>
      if c' = c then
        if lbl.isPrefixOf rest then
          match rest.drop lbl.length with
          | [] => dropTarget (c' :: lbl) (children t) ++ ps
          | e :: r => collapse (c' :: lbl) (children t).length (del t (e :: r)) :: ps
        else (c' :: lbl, t) :: ps
      else (c' :: lbl, t) :: delAux ps c rest

end

/-- Removal: nothing changes unless `k` holds a value. -/
def remove {α : Type} (t : Patricia α) (k : List Nat) : Patricia α :=
  if (get t k).isSome then del t k else t

/-! ### Lookups after removal -/

private theorem edge_merge {α : Type} {l2 : List Nat} (hl2 : l2 ≠ []) (lbl : List Nat)
    (u : Patricia α) (r : List Nat) :
    edge lbl (.node none [(l2, u)]) r = edge (lbl ++ l2) u r := by
  by_cases hp : lbl <+: r
  · obtain ⟨s, rfl⟩ := hp
    rw [edge_prefix, edge_append]
    obtain ⟨h, l2', rfl⟩ := List.exists_cons_of_ne_nil hl2
    cases s with
    | nil => simp [get, edge, List.isPrefixOf]
    | cons e s =>
        rw [edge_cons]
        simp only [get, getAux_cons_cons]
        split <;> rfl
  · rw [edge_none hp, edge_of_not_prefix hp]

/-- An edge's answer depends on the value at its end only for the key that ends there. -/
private theorem edge_value {α : Type} {lbl r : List Nat} (h : r ≠ lbl) (v w : Option α)
    (cs : List (List Nat × Patricia α)) :
    edge lbl (.node v cs) r = edge lbl (.node w cs) r := by
  by_cases hp : lbl <+: r
  · obtain ⟨s, rfl⟩ := hp
    rw [edge_prefix, edge_prefix]
    cases s with
    | nil => simp at h
    | cons e s => rfl
  · rw [edge_none hp, edge_none hp]

private theorem edge_none_self {α : Type} (lbl : List Nat) (cs : List (List Nat × Patricia α)) :
    edge lbl (.node none cs) lbl = none := by
  rw [edge_self]; rfl

private theorem edge_long {α : Type} {l2 : List Nat} (hl2 : l2 ≠ []) (lbl : List Nat)
    (u : Patricia α) : edge (lbl ++ l2) u lbl = none := by
  apply edge_none
  intro hp
  have := hp.length_le
  simp only [List.length_append] at this
  have : 0 < l2.length := List.length_pos_iff.mpr hl2
  omega

private theorem getAux_of_not_head {α : Type} {c : Nat} :
    ∀ {ps : List (List Nat × Patricia α)}, some c ∉ ps.map (·.1.head?) →
      ∀ r, getAux ps c r = none
  | [], _, _ => rfl
  | ([], t) :: ps, h, r => by
      simp only [getAux]
      exact getAux_of_not_head (fun hm => h (List.mem_cons_of_mem _ hm)) r
  | (c' :: lbl, t) :: ps, h, r => by
      have hne : c' ≠ c := fun he => h (by simp [he])
      rw [getAux_cons_cons]
      simp only [hne, ↓reduceIte]
      exact getAux_of_not_head (fun hm => h (List.mem_cons_of_mem _ hm)) r

private theorem getAux_dropTarget {α : Type} (c : Nat) (lbl : List Nat) (v : Option α)
    (tcs : List (List Nat × Patricia α)) (htcs : ∀ e ∈ tcs, e.1 ≠ [])
    (ps : List (List Nat × Patricia α)) (hps : some c ∉ ps.map (·.1.head?)) (d : Nat)
    (r : List Nat) :
    getAux (dropTarget (c :: lbl) tcs ++ ps) d r
      = if d = c ∧ r = lbl then none else getAux ((c :: lbl, .node v tcs) :: ps) d r := by
  rw [getAux_cons_cons]
  by_cases hdc : c = d
  · subst hdc
    simp only [true_and, ↓reduceIte]
    match tcs, htcs with
    | [], _ =>
        simp only [dropTarget, List.nil_append]
        rw [getAux_of_not_head hps]
        split
        · rfl
        · rename_i hne
          by_cases hp : lbl <+: r
          · obtain ⟨s, rfl⟩ := hp
            rw [edge_prefix]
            cases s with
            | nil => simp at hne
            | cons e s => rfl
          · rw [edge_none hp]
    | [(l2, u)], htcs =>
        have hl2 : l2 ≠ [] := htcs _ (List.mem_singleton_self _)
        simp only [dropTarget, List.cons_append, List.nil_append]
        rw [getAux_cons_cons]
        simp only [↓reduceIte]
        split
        · rename_i h; rw [h]; exact edge_long hl2 lbl u
        · rename_i hne
          rw [edge_value hne v none, edge_merge hl2]
    | e :: f :: rest, _ =>
        simp only [dropTarget, List.cons_append, List.nil_append]
        rw [getAux_cons_cons]
        simp only [↓reduceIte]
        split
        · rename_i h; rw [h]; exact edge_none_self _ _
        · rename_i hne
          exact edge_value hne none v _
  · have hdc' : ¬ d = c := fun h => hdc h.symm
    simp only [hdc, hdc', false_and, ↓reduceIte]
    match tcs with
    | [] => simp only [dropTarget, List.nil_append]
    | [(l2, u)] =>
        simp only [dropTarget, List.cons_append, List.nil_append]
        rw [getAux_cons_cons]
        simp only [hdc, ↓reduceIte]
    | e :: f :: rest =>
        simp only [dropTarget, List.cons_append, List.nil_append]
        rw [getAux_cons_cons]
        simp only [hdc, ↓reduceIte]

private theorem getAux_collapse {α : Type} (c : Nat) (lbl : List Nat) (n : Nat) (t : Patricia α)
    (ht : ∀ e ∈ children t, e.1 ≠ []) (ps : List (List Nat × Patricia α)) (d : Nat)
    (r : List Nat) :
    getAux (collapse (c :: lbl) n t :: ps) d r = getAux ((c :: lbl, t) :: ps) d r := by
  match t, ht with
  | .node none [(l2, u)], ht =>
      have hl2 : l2 ≠ [] := ht _ (List.mem_singleton_self _)
      simp only [collapse]
      split
      · rw [List.cons_append, getAux_cons_cons, getAux_cons_cons, edge_merge hl2]
      · rfl
  | .node none [], _ => rfl
  | .node none (e :: f :: rest), _ => rfl
  | .node (some a) cs, _ => rfl

private theorem labels_ne_delAux {α : Type} (c : Nat) (rest : List Nat) :
    ∀ {cs : List (List Nat × Patricia α)}, (∀ e ∈ cs, e.1 ≠ []) →
      ∀ e ∈ delAux cs c rest, e.1 ≠ []
  | [], _, _, he => by simp [delAux] at he
  | ([], t) :: ps, h, _, _ => absurd rfl (h _ (List.mem_cons_self ..))
  | (c' :: lbl, t) :: ps, h, e, he => by
      have hps : ∀ e ∈ ps, e.1 ≠ [] := fun e he => h e (List.mem_cons_of_mem _ he)
      simp only [delAux] at he
      split at he
      · split at he
        · split at he
          · rcases List.mem_append.mp he with he | he
            · match hc : children t, he with
              | [], he => simp [dropTarget] at he
              | [(l2, u)], he => simp only [dropTarget, List.mem_singleton] at he; subst he; simp
              | _ :: _ :: _, he => simp only [dropTarget, List.mem_singleton] at he; subst he; simp
            · exact hps e he
          · rcases List.mem_cons.mp he with rfl | he
            · unfold collapse; split <;> (try split) <;> simp
            · exact hps e he
        · rcases List.mem_cons.mp he with rfl | he
          · simp
          · exact hps e he
      · rcases List.mem_cons.mp he with rfl | he
        · simp
        · exact labels_ne_delAux c rest hps e he

mutual

/-- **What `del` does to lookups**, on a tree with no empty branch and distinct heads: `k` maps to
nothing, every other key to what it did before. Merging an edge into the one below it changes no
lookup, because the merged label is the two labels read one after the other. -/
theorem get_del {α : Type} : (t : Patricia α) → (k : List Nat) → NoEmptyBranches t →
    DistinctFirstLetters t → ∀ k', get (del t k) k' = if k' = k then none else get t k'
  | .node v cs, [], _, _, k' => by
      cases k' <;> simp [del, get]
  | .node v cs, c :: rest, hc, ⟨hnd, hdh⟩, k' => by
      cases k' with
      | nil => simp [del, get]
      | cons d rest' =>
          simp only [del, get, List.cons.injEq]
          rw [getAux_delAux cs c rest hc hdh hnd d rest']

/-- The child-list half of `get_del`. -/
theorem getAux_delAux {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → NoEmptyBranchesChildren cs → DistinctFirstLettersChildren cs →
    (cs.map (·.1.head?)).Nodup → ∀ d r,
      getAux (delAux cs c rest) d r = if d = c ∧ r = rest then none else getAux cs d r
  | [], _, _, _, _, _, d, r => by simp [delAux, getAux]
  | ([], t) :: ps, _, _, hc, _, _, _, _ => absurd rfl hc.1
  | (c' :: lbl, t) :: ps, c, rest, ⟨_, hct, hcps⟩, ⟨hdt, hdps⟩, hnd, d, r => by
      rw [List.map_cons, List.nodup_cons] at hnd
      have hhead : some c' ∉ ps.map (·.1.head?) := by simpa using hnd.1
      by_cases hcc : c' = c
      · subst hcc
        simp only [delAux, ↓reduceIte]
        by_cases hpre : lbl.isPrefixOf rest
        · simp only [hpre, ↓reduceIte]
          obtain ⟨s, rfl⟩ := List.isPrefixOf_iff_prefix.mp hpre
          simp only [List.drop_left]
          match t, hct, hdt, s with
          | .node tv tcs, hct, hdt, [] =>
              simp only [children, List.append_nil]
              exact getAux_dropTarget c' lbl tv tcs
                (NoEmptyBranchesChildren.labels_ne (cs := tcs) hct) ps hhead d r
          | .node tv tcs, hct, hdt, e :: s =>
              have hlab : ∀ x ∈ children (del (.node tv tcs) (e :: s)), x.1 ≠ [] := by
                simp only [del, children]
                exact labels_ne_delAux e s (NoEmptyBranchesChildren.labels_ne (cs := tcs) hct)
              rw [getAux_collapse c' lbl _ _ hlab, getAux_cons_cons, getAux_cons_cons]
              by_cases hdc : d = c'
              · subst hdc
                simp only [↓reduceIte, true_and]
                by_cases hp : lbl <+: r
                · obtain ⟨s', rfl⟩ := hp
                  rw [edge_prefix, edge_prefix,
                    get_del (.node tv tcs) (e :: s) hct hdt s']
                  simp
                · rw [edge_none hp, edge_none hp]
                  split <;> rfl
              · have hdc' : ¬ c' = d := fun h => hdc h.symm
                simp [hdc, hdc']
        · have hpre' : lbl.isPrefixOf rest = false := Bool.eq_false_iff.mpr hpre
          simp only [hpre', Bool.false_eq_true, ↓reduceIte]
          by_cases h : d = c' ∧ r = rest
          · obtain ⟨rfl, rfl⟩ := h
            rw [getAux_cons_cons]
            simp [edge, hpre']
          · simp only [h, ↓reduceIte]
      · simp only [delAux, hcc, ↓reduceIte]
        rw [getAux_cons_cons, getAux_cons_cons]
        by_cases hdc : c' = d
        · subst hdc
          simp [hcc]
        · simp only [hdc, ↓reduceIte]
          exact getAux_delAux ps c rest hcps hdps hnd.2 d r

end

/-- **Removal removes the key** on a tree with no empty branch and distinct heads. -/
theorem get_remove {α : Type} (t : Patricia α) (hc : NoEmptyBranches t)
    (hd : DistinctFirstLetters t)
    (k : List Nat) : get (remove t k) k = none := by
  unfold remove
  split
  · simp [get_del t k hc hd]
  · rename_i hs; simpa using hs

/-- **And nothing else**: every other key maps to what it did before. -/
theorem get_remove_other {α : Type} (t : Patricia α) (hc : NoEmptyBranches t)
    (hd : DistinctFirstLetters t)
    {k k' : List Nat} (hk : k' ≠ k) : get (remove t k) k' = get t k' := by
  unfold remove
  split
  · simp [get_del t k hc hd, hk]
  · rfl

/-! ### The shape after removal -/

private theorem length_delAux {α : Type} (c : Nat) (rest : List Nat) :
    ∀ cs : List (List Nat × Patricia α),
      (delAux cs c rest).length = cs.length ∨ (delAux cs c rest).length + 1 = cs.length
  | [] => Or.inl rfl
  | ([], t) :: ps => by
      simp only [delAux, List.length_cons]
      rcases length_delAux c rest ps with h | h <;> omega
  | (c' :: lbl, t) :: ps => by
      simp only [delAux]
      split
      · split
        · split
          · match children t with
            | [] => simp [dropTarget]
            | [_] => simp [dropTarget]
            | _ :: _ :: _ => simp [dropTarget]
          · simp
        · simp
      · simp only [List.length_cons]
        rcases length_delAux c rest ps with h | h <;> omega

private theorem heads_delAux {α : Type} (c : Nat) (rest : List Nat) :
    ∀ cs : List (List Nat × Patricia α),
      ((delAux cs c rest).map (·.1.head?)).Sublist (cs.map (·.1.head?))
  | [] => List.Sublist.slnil
  | ([], t) :: ps => by
      simp only [delAux, List.map_cons]
      exact (heads_delAux c rest ps).cons_cons _
  | (c' :: lbl, t) :: ps => by
      simp only [delAux]
      split
      · split
        · split
          · match children t with
            | [] => simp [dropTarget]
            | [_] => simp [dropTarget]
            | _ :: _ :: _ => simp [dropTarget]
          · rename_i e r _
            have :
                (collapse (c' :: lbl) (children t).length (del t (e :: r))).1.head? = some c' := by
              unfold collapse; split <;> (try split) <;> simp
            simp [this]
        · exact List.Sublist.refl _
      · simp only [List.map_cons]
        exact (heads_delAux c rest ps).cons_cons _

private theorem branchesUnlessWordEndsChildren_append {α : Type} :
    ∀ {cs ds : List (List Nat × Patricia α)}, BranchesUnlessWordEndsChildren cs →
      BranchesUnlessWordEndsChildren ds → BranchesUnlessWordEndsChildren (cs ++ ds)
  | [], _, _, h => h
  | _ :: _, _, ⟨h2, h3⟩, h => ⟨h2, branchesUnlessWordEndsChildren_append h3 h⟩

private theorem noEmptyBranchesChildren_append {α : Type} :
    ∀ {cs ds : List (List Nat × Patricia α)}, NoEmptyBranchesChildren cs →
      NoEmptyBranchesChildren ds → NoEmptyBranchesChildren (cs ++ ds)
  | [], _, _, h => h
  | _ :: _, _, ⟨h1, h2, h3⟩, h => ⟨h1, h2, noEmptyBranchesChildren_append h3 h⟩

private theorem distinctFirstLettersChildren_append {α : Type} :
    ∀ {cs ds : List (List Nat × Patricia α)}, DistinctFirstLettersChildren cs →
      DistinctFirstLettersChildren ds → DistinctFirstLettersChildren (cs ++ ds)
  | [], _, _, h => h
  | _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, distinctFirstLettersChildren_append h2 h⟩

private theorem branchesUnlessWordEndsNode_collapse {α : Type} {c : Nat} {lbl : List Nat}
    {tv : Option α} {tcs D : List (List Nat × Patricia α)} (ht : tv ≠ none ∨ 2 ≤ tcs.length)
    (hD : BranchesUnlessWordEndsChildren D)
    (hlen : D.length = tcs.length ∨ D.length + 1 = tcs.length) :
    BranchesUnlessWordEndsNode (collapse (c :: lbl) tcs.length (.node tv D)).2 := by
  match tv, D, hD, hlen with
  | none, [(l2, u)], hD, hlen =>
      simp only [collapse]
      split
      · exact hD.1
      · rename_i hn
        simp only [List.length_singleton] at hlen
        have : 2 ≤ tcs.length := ht.resolve_left (by simp)
        omega
  | none, [], _, hlen =>
      have : 2 ≤ tcs.length := ht.resolve_left (by simp)
      simp at hlen; omega
  | none, e :: f :: rest, hD, _ =>
      simpa [collapse, BranchesUnlessWordEndsNode] using hD
  | some a, D, hD, _ => simpa [collapse, BranchesUnlessWordEndsNode] using hD

private theorem noEmptyBranches_collapse {α : Type} {c : Nat} {lbl : List Nat} {n : Nat}
    {t : Patricia α} (ht : NoEmptyBranches t) :
    (collapse (c :: lbl) n t).1 ≠ [] ∧ NoEmptyBranches (collapse (c :: lbl) n t).2 := by
  match t, ht with
  | .node none [(l2, u)], ht =>
      simp only [collapse]
      split
      · exact ⟨by simp, ht.2.1⟩
      · exact ⟨by simp, ht⟩
  | .node none [], ht => exact ⟨by simp [collapse], ht⟩
  | .node none (_ :: _ :: _), ht => exact ⟨by simp [collapse], ht⟩
  | .node (some _) _, ht => exact ⟨by simp [collapse], ht⟩

private theorem distinctFirstLetters_collapse {α : Type} (lbl : List Nat) (n : Nat) :
    ∀ t : Patricia α, DistinctFirstLetters t → DistinctFirstLetters (collapse lbl n t).2
  | .node none [(l2, u)], h => by
      simp only [collapse]
      split
      · exact h.2.1
      · exact h
  | .node none [], h => h
  | .node none (_ :: _ :: _), h => h
  | .node (some _) _, h => h

mutual

/-- **`del` keeps `BranchesUnlessWordEnds`**, the shape the Rust maintains: a target left with one
child and a parent left valueless with one child are both merged away, and the root is exempt. -/
theorem branchesUnlessWordEnds_del {α : Type} : (t : Patricia α) → (k : List Nat) →
    BranchesUnlessWordEnds t → BranchesUnlessWordEnds (del t k)
  | .node _ _, [], h => h
  | .node _ cs, c :: rest, h => branchesUnlessWordEndsChildren_delAux cs c rest h

theorem branchesUnlessWordEndsChildren_delAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) →
      BranchesUnlessWordEndsChildren cs → BranchesUnlessWordEndsChildren (delAux cs c rest)
  | [], _, _, _ => trivial
  | ([], _) :: ps, c, rest, ⟨h2, h3⟩ =>
      ⟨h2, branchesUnlessWordEndsChildren_delAux ps c rest h3⟩
  | (c' :: lbl, t) :: ps, c, rest, ⟨h2, h3⟩ => by
      simp only [delAux]
      split
      · split
        · match t, h2 with
          | .node tv tcs, ⟨hv, htcs⟩ =>
            split
            · apply branchesUnlessWordEndsChildren_append _ h3
              match tcs, htcs with
              | [], _ => trivial
              | [(l2, u)], htcs => exact ⟨htcs.1, trivial⟩
              | e :: f :: rest, htcs => exact ⟨⟨Or.inr (by simp), htcs⟩, trivial⟩
            · rename_i e r _
              have hD := branchesUnlessWordEnds_del (.node tv tcs) (e :: r) htcs
              simp only [del, BranchesUnlessWordEnds] at hD
              exact ⟨branchesUnlessWordEndsNode_collapse (c := c') (lbl := lbl) hv hD
                (length_delAux e r tcs), h3⟩
        · exact ⟨h2, h3⟩
      · exact ⟨h2, branchesUnlessWordEndsChildren_delAux ps c rest h3⟩

end

mutual

/-- **`del` keeps `NoEmptyBranches`**: every label it writes is an old label, or two run
together. -/
theorem noEmptyBranches_del {α : Type} : (t : Patricia α) → (k : List Nat) →
    NoEmptyBranches t → NoEmptyBranches (del t k)
  | .node _ _, [], h => h
  | .node _ cs, c :: rest, h => noEmptyBranchesChildren_delAux cs c rest h

theorem noEmptyBranchesChildren_delAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) →
      NoEmptyBranchesChildren cs → NoEmptyBranchesChildren (delAux cs c rest)
  | [], _, _, _ => trivial
  | ([], _) :: _, _, _, h => absurd rfl h.1
  | (c' :: lbl, t) :: ps, c, rest, ⟨h1, h2, h3⟩ => by
      simp only [delAux]
      split
      · split
        · match t, h2 with
          | .node tv tcs, htcs =>
            split
            · apply noEmptyBranchesChildren_append _ h3
              match tcs, htcs with
              | [], _ => trivial
              | [(l2, u)], htcs => exact ⟨by simp, htcs.2.1, trivial⟩
              | e :: f :: rest, htcs => exact ⟨by simp, htcs, trivial⟩
            · rename_i e r _
              obtain ⟨hne, hnode⟩ := noEmptyBranches_collapse (c := c') (lbl := lbl)
                (n := (children (.node tv tcs)).length)
                (noEmptyBranches_del (.node tv tcs) (e :: r) htcs)
              exact ⟨hne, hnode, h3⟩
        · exact ⟨h1, h2, h3⟩
      · exact ⟨h1, h2, noEmptyBranchesChildren_delAux ps c rest h3⟩

end

mutual

/-- **`del` keeps `DistinctFirstLetters`**: every edge it rewrites keeps its first symbol. -/
theorem distinctFirstLetters_del {α : Type} : (t : Patricia α) → (k : List Nat) →
    DistinctFirstLetters t →
    DistinctFirstLetters (del t k)
  | .node _ _, [], h => h
  | .node _ cs, c :: rest, ⟨hnd, h⟩ =>
      ⟨(heads_delAux c rest cs).nodup hnd, distinctFirstLettersChildren_delAux cs c rest h⟩

theorem distinctFirstLettersChildren_delAux {α : Type} :
    (cs : List (List Nat × Patricia α)) → (c : Nat) → (rest : List Nat) →
      DistinctFirstLettersChildren cs → DistinctFirstLettersChildren (delAux cs c rest)
  | [], _, _, _ => trivial
  | ([], t) :: ps, c, rest, ⟨h1, h2⟩ => ⟨h1, distinctFirstLettersChildren_delAux ps c rest h2⟩
  | (c' :: lbl, t) :: ps, c, rest, ⟨h1, h2⟩ => by
      simp only [delAux]
      split
      · split
        · match t, h1 with
          | .node tv tcs, ⟨hnd, htcs⟩ =>
            split
            · apply distinctFirstLettersChildren_append _ h2
              match tcs, hnd, htcs with
              | [], _, _ => trivial
              | [(l2, u)], _, htcs => exact ⟨htcs.1, trivial⟩
              | e :: f :: rest, hnd, htcs => exact ⟨⟨hnd, htcs⟩, trivial⟩
            · rename_i e r _
              exact ⟨distinctFirstLetters_collapse _ _ _
                (distinctFirstLetters_del (.node tv tcs) (e :: r) ⟨hnd, htcs⟩), h2⟩
        · exact ⟨h1, h2⟩
      · exact ⟨h1, distinctFirstLettersChildren_delAux ps c rest h2⟩

end

/-- **`remove` keeps `BranchesUnlessWordEnds`**, so a tree the Rust builds stays one it could have
built. -/
theorem branchesUnlessWordEnds_remove {α : Type} {t : Patricia α} (k : List Nat)
    (h : BranchesUnlessWordEnds t) : BranchesUnlessWordEnds (remove t k) := by
  unfold remove; split
  · exact branchesUnlessWordEnds_del t k h
  · exact h

/-- **`remove` keeps `NoEmptyBranches`.** -/
theorem noEmptyBranches_remove {α : Type} {t : Patricia α} (k : List Nat)
    (h : NoEmptyBranches t) : NoEmptyBranches (remove t k) := by
  unfold remove; split
  · exact noEmptyBranches_del t k h
  · exact h

/-- **`remove` keeps `DistinctFirstLetters`.** -/
theorem distinctFirstLetters_remove {α : Type} {t : Patricia α} (k : List Nat)
    (h : DistinctFirstLetters t) :
    DistinctFirstLetters (remove t k) := by
  unfold remove; split
  · exact distinctFirstLetters_del t k h
  · exact h

/-! ### The key set after removal -/

/-- A key of a child list is a child's label followed by one of that child's words. -/
theorem mem_wordsAux' {α : Type} :
    ∀ (cs : List (List Nat × Patricia α)) (x : List Nat),
      x ∈ wordsAux cs ↔ ∃ p ∈ cs, ∃ y ∈ words p.2, x = p.1 ++ y
  | [], x => by simp [wordsAux]
  | p :: rest, x => by
      rw [wordsAux, List.mem_append, mem_wordsAux' rest x, List.mem_map]
      constructor
      · rintro (⟨y, hy, rfl⟩ | ⟨q, hq, y, hy, rfl⟩)
        · exact ⟨p, List.mem_cons_self .., y, hy, rfl⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq, y, hy, rfl⟩
      · rintro ⟨q, hq, y, hy, rfl⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr ⟨q, hq', y, hy, rfl⟩

private theorem head_mem_of_mem_wordsAux {α : Type} {cs : List (List Nat × Patricia α)}
    (hc : NoEmptyBranchesChildren cs) {x : List Nat} (hx : x ∈ wordsAux cs) :
    x.head? ∈ cs.map (·.1.head?) := by
  obtain ⟨p, hp, y, _, rfl⟩ := (mem_wordsAux' cs x).mp hx
  obtain ⟨h, l, hl⟩ := List.exists_cons_of_ne_nil (hc.labels_ne p hp)
  exact List.mem_map.mpr ⟨p, hp, by simp [hl]⟩

mutual

/-- **The words are the words that hold a value**, on a tree with no empty branch and distinct
heads. -/
theorem mem_words_iff {α : Type} : (t : Patricia α) → NoEmptyBranches t → DistinctFirstLetters t →
    ∀ x, x ∈ words t ↔ (get t x).isSome
  | .node v cs, hc, _, [] => by
      have : [] ∉ wordsAux cs := fun hm => by
        obtain ⟨p, hp, y, _, hpy⟩ := (mem_wordsAux' cs []).mp hm
        exact NoEmptyBranchesChildren.labels_ne (cs := cs) hc p hp
          (List.append_eq_nil_iff.mp hpy.symm).1
      cases v <;> simp [words, get, this]
  | .node v cs, hc, ⟨hnd, hdh⟩, d :: r => by
      have hx : d :: r ∈ words (.node v cs) ↔ d :: r ∈ wordsAux cs := by
        cases v <;> simp [words]
      rw [hx]
      exact mem_wordsAux_iff cs hc hdh hnd d r

theorem mem_wordsAux_iff {α : Type} : (cs : List (List Nat × Patricia α)) →
    NoEmptyBranchesChildren cs → DistinctFirstLettersChildren cs → (cs.map (·.1.head?)).Nodup →
    ∀ d r, d :: r ∈ wordsAux cs ↔ (getAux cs d r).isSome
  | [], _, _, _, _, _ => by simp [wordsAux, getAux]
  | ([], _) :: _, hc, _, _, _, _ => absurd rfl hc.1
  | (c' :: lbl, t) :: ps, ⟨h1, hct, hcps⟩, ⟨hdt, hdps⟩, hnd, d, r => by
      rw [List.map_cons, List.nodup_cons] at hnd
      rw [wordsAux, List.mem_append, getAux_cons_cons, List.mem_map]
      by_cases hcd : c' = d
      · subst hcd
        have hnot : c' :: r ∉ wordsAux ps := fun hm => hnd.1 (by
          simpa using head_mem_of_mem_wordsAux hcps hm)
        simp only [hnot, or_false, ↓reduceIte]
        by_cases hp : lbl <+: r
        · obtain ⟨s, rfl⟩ := hp
          rw [edge_prefix, ← mem_words_iff t hct hdt s]
          constructor
          · rintro ⟨y, hy, he⟩
            simp only [List.cons_append, List.cons.injEq, List.append_cancel_left_eq, true_and]
              at he
            rw [← he]
            exact hy
          · intro hs
            exact ⟨s, hs, rfl⟩
        · rw [edge_none hp]
          simp only [Option.isSome_none, Bool.false_eq_true, iff_false]
          rintro ⟨y, _, he⟩
          simp only [List.cons_append, List.cons.injEq, true_and] at he
          exact hp ⟨y, he⟩
      · simp only [hcd, ↓reduceIte]
        rw [← mem_wordsAux_iff ps hcps hdps hnd.2 d r]
        constructor
        · rintro (⟨y, _, he⟩ | hm)
          · simp only [List.cons_append, List.cons.injEq] at he
            exact absurd he.1 hcd
          · exact hm
        · exact Or.inr

end

/-- **The key set loses exactly the removed key**, on a tree with no empty branch and distinct
heads. -/
theorem words_remove {α : Type} (t : Patricia α) (hc : NoEmptyBranches t)
    (hd : DistinctFirstLetters t)
    (k x : List Nat) : x ∈ words (remove t k) ↔ x ∈ words t ∧ x ≠ k := by
  rw [mem_words_iff _ (noEmptyBranches_remove k hc) (distinctFirstLetters_remove k hd) x,
    mem_words_iff t hc hd x]
  by_cases hx : x = k
  · subst hx; simp [get_remove t hc hd]
  · simp [get_remove_other t hc hd hx, hx]

/-- **`remove` keeps the invariant**: `distinctFirstLetters_remove`,
`branchesUnlessWordEnds_remove` and `noEmptyBranches_remove`. -/
theorem valid_remove {α : Type} {t : Patricia α} (k : List Nat) (h : Valid t) :
    Valid (remove t k) :=
  ⟨distinctFirstLetters_remove k h.distinctFirstLetters,
    branchesUnlessWordEnds_remove k h.branchesUnlessWordEnds,
    noEmptyBranches_remove k h.noEmptyBranches⟩

/-! ### The Rust's remove keeps the child order

`remove` runs on the Rust's sorted tree as on any other, so `valid_remove` already covers it; what
is left is the order. `dropTarget` deletes an edge or replaces it by one whose label begins with the
same symbol, and so does `collapse` (`patricia.rs`'s `absorb_only_child`, which keeps the first
byte), so every child list's first symbols
after `del` are a sublist of those before, and a sublist of a strictly ascending list ascends
strictly. -/

private theorem headSyms_delAux {α : Type} (c : Nat) (rest : List Nat)
    (cs : List (List Nat × Patricia α)) :
    ((delAux cs c rest).map headSym).Sublist (cs.map headSym) := by
  have hf : (headSym : List Nat × Patricia α → Nat) = fun e => e.1.head?.getD 0 := by
    funext e; simp [headSym]
  have := (heads_delAux c rest cs).map (fun o => o.getD 0)
  simpa [List.map_map, Function.comp_def, hf] using this

private theorem sortedHeadsAux_append {α : Type} :
    ∀ {cs ds : List (List Nat × Patricia α)}, SortedHeadsAux cs → SortedHeadsAux ds →
      SortedHeadsAux (cs ++ ds)
  | [], _, _, h => h
  | _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, sortedHeadsAux_append h2 h⟩

private theorem sortedHeads_collapse {α : Type} (lbl : List Nat) (n : Nat) :
    ∀ t : Patricia α, SortedHeads t → SortedHeads (collapse lbl n t).2
  | .node none [(l2, u)], h => by
      simp only [collapse]
      split
      · exact h.2.1
      · exact h
  | .node none [], h => h
  | .node none (_ :: _ :: _), h => h
  | .node (some _) _, h => h

mutual

/-- **`del` keeps `SortedHeads`**: every child list it rewrites keeps its first symbols in order,
with at most one dropped. -/
theorem sortedHeads_del {α : Type} : (t : Patricia α) → (k : List Nat) → SortedHeads t →
    SortedHeads (del t k)
  | .node _ _, [], h => h
  | .node _ cs, c :: rest, ⟨hs, h⟩ =>
      ⟨List.pairwise_map.mp ((List.pairwise_map.mpr hs).sublist (headSyms_delAux c rest cs)),
        sortedHeadsAux_delAux cs c rest h⟩

/-- The child-list half of `sortedHeads_del`. -/
theorem sortedHeadsAux_delAux {α : Type} : (cs : List (List Nat × Patricia α)) → (c : Nat) →
    (rest : List Nat) → SortedHeadsAux cs → SortedHeadsAux (delAux cs c rest)
  | [], _, _, _ => trivial
  | ([], t) :: ps, c, rest, ⟨h1, h2⟩ => ⟨h1, sortedHeadsAux_delAux ps c rest h2⟩
  | (c' :: lbl, t) :: ps, c, rest, ⟨h1, h2⟩ => by
      simp only [delAux]
      split
      · split
        · match t, h1 with
          | .node tv tcs, ⟨hs, htcs⟩ =>
            split
            · apply sortedHeadsAux_append _ h2
              match tcs, hs, htcs with
              | [], _, _ => trivial
              | [(l2, u)], _, htcs => exact ⟨htcs.1, trivial⟩
              | e :: f :: rest, hs, htcs => exact ⟨⟨hs, htcs⟩, trivial⟩
            · rename_i e r _
              exact ⟨sortedHeads_collapse _ _ _
                (sortedHeads_del (.node tv tcs) (e :: r) ⟨hs, htcs⟩), h2⟩
        · exact ⟨h1, h2⟩
      · exact ⟨h1, sortedHeadsAux_delAux ps c rest h2⟩

end

/-- **The Rust's remove keeps the child order.** With `valid_remove`, which holds on any tree, the
Rust's tree stays `Valid` and `SortedHeads` under removal. -/
theorem sortedHeads_remove {α : Type} {t : Patricia α} (k : List Nat) (h : SortedHeads t) :
    SortedHeads (remove t k) := by
  unfold remove; split
  · exact sortedHeads_del t k h
  · exact h

/-- `get_remove` on a `Valid` tree: `Valid` supplies both its hypotheses. -/
theorem get_remove_of_valid {α : Type} {t : Patricia α} (h : Valid t) (k : List Nat) :
    get (remove t k) k = none :=
  get_remove t h.noEmptyBranches h.distinctFirstLetters k

end Patricia

end AlgoDesign.Strings
