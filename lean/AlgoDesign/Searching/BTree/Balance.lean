/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Search

/-!
# B-tree: height and occupancy

What `Valid` buys. `two_mul_pow_height_le_size_succ` is CLRS Theorem 18.1's shape — a B-tree of
minimum degree `t` and height `h` holds at least `2 * t ^ h - 1` keys — so every operation walks
`O(log_t n)` nodes (`Cost.lean` turns this into `time_searchM_le_log` and its siblings).
`height_child_succ` is balance: every child stands exactly one level below its parent.
`occupancy_bounds` is the per-block floor and ceiling.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## Height against size -/

mutual

/-- A non-root subtree with `depth? = some h` holds at least `t ^ (h + 1) - 1` keys:
`t ^ (h + 1) ≤ size + 1`. -/
theorem size_ge_of_keyCountOk {deg : ℕ} (hdeg : 2 ≤ deg) :
    ∀ {lo hi : Option α} {t : BTree α} {h : ℕ}, Bounded lo hi t → KeyCountOk deg false t →
      t.depth? = some h → deg ^ (h + 1) ≤ t.size + 1
  | _, _, leaf ks, h, _, hk, hd => by
      simp only [depth?, Option.some.injEq] at hd
      have hk1 : deg - 1 ≤ ks.length := by simpa using hk.1
      have hh : h = 0 := hd.symm
      subst hh
      simp only [size_leaf, Nat.zero_add, Nat.pow_one]
      omega
  | lo, hi, node ks cs, h, hb, hk, hd => by
      obtain ⟨-, hlen, hbc⟩ := hb
      have hk1 : deg - 1 ≤ ks.length := by simpa using hk.1
      have hkc : ChildrenKeyCountOk deg cs := hk.2.2
      simp only [depth?] at hd
      rcases hcd : childrenDepth? cs with _ | h'
      · simp [hcd] at hd
      · rw [hcd] at hd
        have hh : h' + 1 = h := Option.some.inj hd
        have huniform : ∀ {c : BTree α}, c ∈ cs → c.depth? = some h' :=
          childrenDepth?_uniform hcd
        have hsum := sizeChildren_ge_of_keyCountOk hdeg hbc hkc huniform
        have hdle : deg ≤ cs.length := by omega
        have hmul := Nat.mul_le_mul_left (deg ^ (h' + 1)) hdle
        rw [← hh, size_node, Nat.pow_succ]
        omega

/-- Companion to `size_ge_of_keyCountOk` for a `List`-valued children list: summed over `cs`, the
same per-child bound (`deg ^ (h + 1) ≤ c.size + 1`) at one common `h` — this is exactly where the
uniform `∀ c ∈ cs, c.depth? = some h` hypothesis (as opposed to a per-child, possibly differing,
depth) gets used, one child at a time. -/
theorem sizeChildren_ge_of_keyCountOk {deg : ℕ} (hdeg : 2 ≤ deg) {h : ℕ} :
    ∀ {bs : List (Option α × Option α)} {cs : List (BTree α)}, BoundedChildren bs cs →
      ChildrenKeyCountOk deg cs → (∀ {c : BTree α}, c ∈ cs → c.depth? = some h) →
      deg ^ (h + 1) * cs.length ≤ sizeChildren cs + cs.length
  | [], [], _, _, _ => by simp
  | (_, _) :: bs, c :: cs, hbc, hkc, hduni => by
      obtain ⟨hb, hbcs⟩ := hbc
      obtain ⟨hk, hkcs⟩ := hkc
      have hc := size_ge_of_keyCountOk hdeg hb hk (hduni (List.mem_cons_self ..))
      have hcs := sizeChildren_ge_of_keyCountOk hdeg hbcs hkcs
        (fun hc' => hduni (List.mem_cons_of_mem _ hc'))
      simp only [sizeChildren_cons, List.length_cons, Nat.mul_succ]
      omega
  | [], _ :: _, hbc, _, _ => by simp [BoundedChildren] at hbc
  | _ :: _, [], hbc, _, _ => by simp [BoundedChildren] at hbc

end

/-- CLRS Theorem 18.1: a `Valid` B-tree of minimum degree `t` and height `h` holds at least
`2 * t ^ h - 1` keys, stated as `2 * t ^ h ≤ size + 1`. Needs `1 ≤ bt.size`: an empty leaf root
fails it. -/
theorem two_mul_pow_height_le_size_succ {deg : ℕ} :
    ∀ {bt : BTree α}, Valid deg bt → 1 ≤ bt.size → 2 * deg ^ bt.height ≤ bt.size + 1
  | leaf ks, _, hsize => by
      simp only [height_leaf, Nat.pow_zero, size_leaf] at hsize ⊢
      omega
  | node ks cs, hv, _ => by
      obtain ⟨hb, hsd, hk, hdeg⟩ := valid_iff_legal.1 hv
      obtain ⟨-, hlen, hbc⟩ := hb
      have hk1 : 1 ≤ ks.length := by simpa using hk.1
      have hkc : ChildrenKeyCountOk deg cs := hk.2.2
      have hsd' := depth?_eq_some_height hsd
      simp only [depth?] at hsd'
      rcases hcd : childrenDepth? cs with _ | h'
      · simp [hcd] at hsd'
      · rw [hcd] at hsd'
        have hheight : (node ks cs).height = h' + 1 := (Option.some.inj hsd').symm
        have huniform : ∀ {c : BTree α}, c ∈ cs → c.depth? = some h' :=
          childrenDepth?_uniform hcd
        have hsum := sizeChildren_ge_of_keyCountOk hdeg hbc hkc huniform
        have hlen2 : 2 ≤ cs.length := by omega
        have hmul := Nat.mul_le_mul_left (deg ^ (h' + 1)) hlen2
        rw [hheight, size_node]
        omega

/-! ## Balance -/

omit [LinearOrder α] in
/-- **A valid B-tree is balanced, stated as a fact about the tree rather than as a conjunct
of `Valid`.** Every child of a node stands at exactly the same height, one below its parent --
which is what "all leaves sit at the same depth" comes to, level by level. -/
theorem height_child_succ_of_sameDepth {ks : List α} {cs : List (BTree α)}
    (h : SameDepth (node ks cs)) :
    ∀ c ∈ cs, c.height + 1 = height (node ks cs) := by
  intro c hc
  have hcd : (childrenDepth? cs).isSome := by
    simpa [SameDepth, depth?, ← Option.isSome_iff_ne_none] using h
  have heq : childrenDepth? cs = some (childrenHeight cs) := childrenDepth?_isSome hcd
  have hcu : c.depth? = some (childrenHeight cs) := childrenDepth?_uniform heq hc
  have hcsd : SameDepth c := by simp [SameDepth, hcu]
  have hch : depth? c = some c.height := depth?_eq_some_height hcsd
  rw [hch] at hcu
  have : c.height = childrenHeight cs := Option.some_inj.mp hcu
  simp only [height_node]
  omega

/-- The same fact for a `Valid` tree, which is the form a chapter would cite. -/
theorem height_child_succ {deg : ℕ} {ks : List α} {cs : List (BTree α)}
    (hv : Valid deg (node ks cs)) : ∀ c ∈ cs, c.height + 1 = height (node ks cs) :=
  height_child_succ_of_sameDepth (valid_iff_legal.1 hv).2.1

/-! ## How much of the space is idle -/

mutual

/-- How many nodes (blocks) the tree occupies. -/
def nodeCount : BTree α → ℕ
  | leaf _ => 1
  | node _ cs => childrenNodeCount cs + 1

/-- How many nodes a list of children occupies. -/
def childrenNodeCount : List (BTree α) → ℕ
  | [] => 0
  | c :: cs => nodeCount c + childrenNodeCount cs

end

omit [LinearOrder α] in
mutual

/-- **Every non-root block is at least `deg - 1` keys full.** This is the occupancy floor that
the chapter's trips table rests on: with room for `2*deg - 1` keys per block, no block below the
root may sit emptier than `(deg-1)/(2*deg-1)` of its capacity. -/
theorem size_ge_of_nonRoot {deg : ℕ} :
    ∀ {bt : BTree α}, KeyCountOk deg false bt → (deg - 1) * nodeCount bt ≤ bt.size
  | leaf ks, h => by
      simp only [KeyCountOk] at h
      simp only [nodeCount, size_leaf, Nat.mul_one]
      rcases h.1 with h' | h'
      · exact absurd h' (by simp)
      · exact h'
  | node ks cs, h => by
      simp only [KeyCountOk] at h
      simp only [nodeCount, size_node]
      have hk : deg - 1 ≤ ks.length := by simpa using h.1
      have hc := sizeChildren_ge_of_childrenKeyCountOk h.2.2
      have hd : (deg - 1) * (childrenNodeCount cs + 1)
           = (deg - 1) * childrenNodeCount cs + (deg - 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

theorem sizeChildren_ge_of_childrenKeyCountOk {deg : ℕ} :
    ∀ {cs : List (BTree α)}, ChildrenKeyCountOk deg cs →
      (deg - 1) * childrenNodeCount cs ≤ sizeChildren cs
  | [], _ => by simp [childrenNodeCount, sizeChildren]
  | c :: cs, h => by
      simp only [ChildrenKeyCountOk] at h
      simp only [childrenNodeCount, sizeChildren_cons]
      have h1 := size_ge_of_nonRoot h.1
      have h2 := sizeChildren_ge_of_childrenKeyCountOk h.2
      have hd : (deg - 1) * (nodeCount c + childrenNodeCount cs)
           = (deg - 1) * nodeCount c + (deg - 1) * childrenNodeCount cs := Nat.mul_add ..
      omega

end

omit [LinearOrder α] in
mutual

/-- The matching ceiling: no block holds more than `2*deg - 1` keys. -/
theorem size_le_of_keyCountOk {deg : ℕ} {r : Bool} :
    ∀ {bt : BTree α}, KeyCountOk deg r bt → bt.size ≤ (2 * deg - 1) * nodeCount bt
  | leaf ks, h => by
      simp only [KeyCountOk] at h
      simpa [nodeCount, size_leaf] using h.2
  | node ks cs, h => by
      simp only [KeyCountOk] at h
      simp only [nodeCount, size_node]
      have hk : ks.length ≤ 2 * deg - 1 := h.2.1
      have hc := sizeChildren_le_of_childrenKeyCountOk h.2.2
      have hd : (2 * deg - 1) * (childrenNodeCount cs + 1)
           = (2 * deg - 1) * childrenNodeCount cs + (2 * deg - 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega

theorem sizeChildren_le_of_childrenKeyCountOk {deg : ℕ} :
    ∀ {cs : List (BTree α)}, ChildrenKeyCountOk deg cs →
      sizeChildren cs ≤ (2 * deg - 1) * childrenNodeCount cs
  | [], _ => by simp [childrenNodeCount, sizeChildren]
  | c :: cs, h => by
      simp only [ChildrenKeyCountOk] at h
      simp only [childrenNodeCount, sizeChildren_cons]
      have h1 := size_le_of_keyCountOk h.1
      have h2 := sizeChildren_le_of_childrenKeyCountOk h.2
      have hd : (2 * deg - 1) * (nodeCount c + childrenNodeCount cs)
           = (2 * deg - 1) * nodeCount c + (2 * deg - 1) * childrenNodeCount cs := Nat.mul_add ..
      omega

end

omit [LinearOrder α] in
/-- **What a non-root block's occupancy is pinned between**, with no division: at least
`deg - 1` keys and at most `2*deg - 1`, per block. -/
theorem occupancy_bounds {deg : ℕ} {bt : BTree α} (h : KeyCountOk deg false bt) :
    (deg - 1) * nodeCount bt ≤ bt.size ∧ bt.size ≤ (2 * deg - 1) * nodeCount bt :=
  ⟨size_ge_of_nonRoot h, size_le_of_keyCountOk h⟩

/-- Measured in keys, the floor is strictly below half: `2 * (deg - 1) < 2 * deg - 1`, one third
full at `deg = 2`. Measured in children it is exactly half (`branching_bounds`). -/
theorem occupancy_floor_lt_half {deg : ℕ} (h : 1 ≤ deg) :
    2 * (deg - 1) < 2 * deg - 1 := by omega

/-- **Measured in branching, the floor is exactly half.** A non-root node carries between `deg`
and `2*deg` children, so its minimum branching is exactly half its maximum — which is what makes
the worst-case search base `deg` rather than `2*deg`, and what the trips table rests on. -/
theorem branching_bounds {deg : ℕ} {lo hi : Option α} {ks : List α} {cs : List (BTree α)}
    (hdeg : 1 ≤ deg) (hb : Bounded lo hi (node ks cs)) (hk : KeyCountOk deg false (node ks cs)) :
    deg ≤ cs.length ∧ cs.length ≤ 2 * deg := by
  simp only [KeyCountOk] at hk
  obtain ⟨-, hlen, -⟩ := hb
  have h1 : deg - 1 ≤ ks.length := by simpa using hk.1
  have h2 : ks.length ≤ 2 * deg - 1 := hk.2.1
  omega

end BTree

end AlgoDesign.Searching
