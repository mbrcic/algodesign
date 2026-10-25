/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Delete

/-!
# B-tree: cost

An I/O-count cost model via `Cslib.Algorithms.Lean.TimeM`, charging one block transfer per node
entered and nothing for the keys scanned inside a block already fetched. Search, insertion
(`insertM`, at the end of `Insert.lean`) and deletion are each one descent, charged
`log_deg((n+1)/2) + 2` block transfers at most: `time_searchM_le_log`, `time_insertM_le_log`,
`time_deleteM_le_log`. Each timed twin erases to its algorithm (`ret_searchM`, `ret_insertM`,
`ret_deleteM`). Writes are counted in `IO.lean`.

Of the `Ω(log_B N)` lower bound only the counting step is proved, `decisionTree_depth_ge`; that
every comparison-based search is such a tree is argued in prose.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree.Node

variable {α : Type} [LinearOrder α] {deg : ℕ}

/-! ## Search -/

mutual

/-- `search`, charged one block transfer per node entered. -/
def searchM (a : α) : Node α → TimeM ℕ Bool
  | leaf ks => do
      tick 1
      pure (decide (a ∈ ks))
  | node ks cs => do
      tick 1
      searchChildrenM a ks cs

/-- The in-node walk. Charges nothing: these keys are in a block already fetched. -/
def searchChildrenM (a : α) : List α → List (Node α) → TimeM ℕ Bool
  | k :: ks, c :: cs =>
      if a < k then searchM a c
      else if k < a then searchChildrenM a ks cs
      else pure true
  | [], c :: _ => searchM a c
  | _, [] => pure false

end

mutual

/-- **Erasing the cost gives ordinary `search`.** Without this the timed version could be
measuring a different algorithm. -/
theorem ret_searchM (a : α) : ∀ t : Node α, (searchM a t).ret = search a t
  | leaf ks => by simp [searchM, search]
  | node ks cs => by
      simp only [searchM, search, ret_bind]
      exact ret_searchChildrenM a ks cs

theorem ret_searchChildrenM (a : α) :
    ∀ (ks : List α) (cs : List (Node α)),
      (searchChildrenM a ks cs).ret = searchChildren a ks cs
  | k :: ks, c :: cs => by
      simp only [searchChildrenM, searchChildren]
      split_ifs
      · exact ret_searchM a c
      · exact ret_searchChildrenM a ks cs
      · rfl
  | [], c :: _ => by simp only [searchChildrenM, searchChildren]; exact ret_searchM a c
  | [], [] => by simp [searchChildrenM, searchChildren]
  | _ :: _, [] => by simp [searchChildrenM, searchChildren]

end

mutual

/-- **One block transfer per level.** The walk inside a node is free: those keys sit in a
block already fetched. -/
theorem time_searchM_le_height_succ (a : α) :
    ∀ t : Node α, (searchM a t).time ≤ t.height + 1
  | leaf ks => by simp [searchM, height]
  | node ks cs => by
      simp only [searchM, time_bind, time_tick, height_node]
      have := time_searchChildrenM_le a ks cs
      omega

theorem time_searchChildrenM_le (a : α) :
    ∀ (ks : List α) (cs : List (Node α)),
      (searchChildrenM a ks cs).time ≤ childrenHeight cs + 1
  | k :: ks, c :: cs => by
      simp only [searchChildrenM]
      split_ifs
      · have h1 := time_searchM_le_height_succ a c
        have h2 : c.height ≤ childrenHeight (c :: cs) :=
          height_le_childrenHeight_of_mem (List.mem_cons_self ..)
        omega
      · have h1 := time_searchChildrenM_le a ks cs
        have h2 := childrenHeight_le_cons c cs
        omega
      · simp
  | [], c :: cs => by
      simp only [searchChildrenM]
      have h1 := time_searchM_le_height_succ a c
      have h2 : c.height ≤ childrenHeight (c :: cs) :=
        height_le_childrenHeight_of_mem (List.mem_cons_self ..)
      omega
  | [], [] => by simp [searchChildrenM]
  | _ :: _, [] => by simp [searchChildrenM]

end

/-- A search of a valid B-tree of minimum degree `deg` costs at most `log_deg((n+1)/2) + 1` block
transfers, at every `n`, constant included. -/
theorem time_searchM_le_log {deg : ℕ} {bt : Node α} (hv : RootLegal deg bt) (hsz : 1 ≤ bt.size)
    (a : α) : (searchM a bt).time ≤ Nat.log deg ((bt.size + 1) / 2) + 1 := by
  have hdeg : 2 ≤ deg := hv.2.2.2
  have hstruct : 2 * deg ^ bt.height ≤ bt.size + 1 :=
    two_mul_pow_height_le_size_succ hv hsz
  have hdiv : deg ^ bt.height ≤ (bt.size + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hlog : bt.height ≤ Nat.log deg ((bt.size + 1) / 2) :=
    Nat.le_log_of_pow_le (by omega) hdiv
  have := time_searchM_le_height_succ a bt
  omega

/-! ## Deletion

`delete`'s descent, charged in the same unit as `searchM` and `insertM`. -/

/-- The block transfers `takeMax` makes: one per node on the walk to the rightmost leaf. -/
def takeMaxCost (deg : ℕ) : Node α → ℕ
  | leaf _ => 1
  | node ks cs =>
      match _hc : cs.getLast? with
      | none => 1
      | some c => takeMaxCost deg (ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩).target + 1
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast _hc
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The mirror, for the walk to the leftmost leaf. -/
def takeMinCost (deg : ℕ) : Node α → ℕ
  | leaf _ => 1
  | node _ [] => 1
  | node ks (c :: cs') => takeMinCost deg (ensureSpare deg ⟨[], [], c, ks, cs'⟩).target + 1
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

omit [LinearOrder α] in
/-- **One block transfer per level on the way to the extreme key.** -/
theorem takeMaxCost_le (deg : ℕ) : ∀ t : Node α, takeMaxCost deg t ≤ t.height + 1
  | leaf _ => by simp [takeMaxCost]
  | node ks cs => by
      have ih : ∀ c : Node α, cs.getLast? = some c →
          takeMaxCost deg (ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩).target
            ≤ (ensureSpare deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)).target.height + 1 := by
        intro c hc
        exact takeMaxCost_le deg _
      rw [takeMaxCost]
      split
      · simp [height_node]
      · rename_i c hc
        have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
        have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
          simp only [Spot.children]
          exact dropLast_append_getLast hc
        rw [h2] at h1
        have := ih c hc
        simp only [height_node]
        omega
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast hc
    rw [h2] at h1
    simp only [height_node]
    omega

omit [LinearOrder α] in
/-- The mirror. -/
theorem takeMinCost_le (deg : ℕ) : ∀ t : Node α, takeMinCost deg t ≤ t.height + 1
  | leaf _ => by simp [takeMinCost]
  | node _ [] => by simp [takeMinCost, height_node]
  | node ks (c :: cs') => by
      have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
      have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
        simp only [Spot.children, List.nil_append]
      rw [h2] at h1
      have ih := takeMinCost_le deg
        (ensureSpare deg (⟨[], [], c, ks, cs'⟩ : Spot α)).target
      rw [takeMinCost]
      simp only [height_node]
      omega
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The block transfers `delRec` makes: one per node entered, plus whatever the walk to a
predecessor or successor costs when the key turns up inside an internal node. -/
def delRecCost (deg : ℕ) (a : α) : Node α → ℕ
  | leaf _ => 1
  | node ks cs =>
      match _hkr : ks.drop (slot a ks), _hcr : cs.drop (slot a ks) with
      | k :: kr, c :: r :: rest =>
          if a < k then
            delRecCost deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                               k :: kr, r :: rest⟩).target + 1
          else if hasSpare deg c then takeMaxCost deg c + 1
          else if hasSpare deg r then takeMinCost deg r + 1
          else delRecCost deg a (mergeNodes c k r) + 1
      | [], [c] =>
          delRecCost deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                             [], []⟩).target + 1
      | _, _ => 1
  termination_by t => t.height
  decreasing_by
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega
    · have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      simp only [height_node]
      omega
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega

section DelRecCostEqns

variable {deg : ℕ} {a : α} {ks : List α} {cs : List (Node α)}
  {k : α} {kr : List α} {c r : Node α} {rest : List (Node α)}

/-- The descent branch. -/
theorem delRecCost_descend (hkr : ks.drop (slot a ks) = k :: kr)
    (hcr : cs.drop (slot a ks) = c :: r :: rest) (hlt : a < k) :
    delRecCost deg a (node ks cs)
      = delRecCost deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                           k :: kr, r :: rest⟩).target + 1 := by
  rw [delRecCost]
  split
  · rename_i k1 kr1 c1 r1 rest1 h1 h2
    rw [hkr] at h1
    rw [hcr] at h2
    simp only [List.cons.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp [hlt]
  · rename_i c1 h1 h2
    rw [hkr] at h1
    simp at h1
  · rename_i h1 h2
    exact (h1 k kr c r rest hkr hcr).elim

/-- The predecessor branch. -/
theorem delRecCost_max (hkr : ks.drop (slot a ks) = k :: kr)
    (hcr : cs.drop (slot a ks) = c :: r :: rest) (hnlt : ¬ a < k)
    (hsc : hasSpare deg c = true) :
    delRecCost deg a (node ks cs) = takeMaxCost deg c + 1 := by
  rw [delRecCost]
  split
  · rename_i k1 kr1 c1 r1 rest1 h1 h2
    rw [hkr] at h1
    rw [hcr] at h2
    simp only [List.cons.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp [hnlt, hsc]
  · rename_i c1 h1 h2
    rw [hkr] at h1
    simp at h1
  · rename_i h1 h2
    exact (h1 k kr c r rest hkr hcr).elim

/-- The successor branch. -/
theorem delRecCost_min (hkr : ks.drop (slot a ks) = k :: kr)
    (hcr : cs.drop (slot a ks) = c :: r :: rest) (hnlt : ¬ a < k)
    (hnsc : ¬ hasSpare deg c = true) (hsr : hasSpare deg r = true) :
    delRecCost deg a (node ks cs) = takeMinCost deg r + 1 := by
  rw [delRecCost]
  split
  · rename_i k1 kr1 c1 r1 rest1 h1 h2
    rw [hkr] at h1
    rw [hcr] at h2
    simp only [List.cons.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp [hnlt, hnsc, hsr]
  · rename_i c1 h1 h2
    rw [hkr] at h1
    simp at h1
  · rename_i h1 h2
    exact (h1 k kr c r rest hkr hcr).elim

/-- The merge branch. -/
theorem delRecCost_merge (hkr : ks.drop (slot a ks) = k :: kr)
    (hcr : cs.drop (slot a ks) = c :: r :: rest) (hnlt : ¬ a < k)
    (hnsc : ¬ hasSpare deg c = true) (hnsr : ¬ hasSpare deg r = true) :
    delRecCost deg a (node ks cs) = delRecCost deg a (mergeNodes c k r) + 1 := by
  rw [delRecCost]
  split
  · rename_i k1 kr1 c1 r1 rest1 h1 h2
    rw [hkr] at h1
    rw [hcr] at h2
    simp only [List.cons.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl, rfl⟩ := h2
    simp [hnlt, hnsc, hnsr]
  · rename_i c1 h1 h2
    rw [hkr] at h1
    simp at h1
  · rename_i h1 h2
    exact (h1 k kr c r rest hkr hcr).elim

/-- The last-child branch. -/
theorem delRecCost_last (hkr : ks.drop (slot a ks) = [])
    (hcr : cs.drop (slot a ks) = [c]) :
    delRecCost deg a (node ks cs)
      = delRecCost deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                           [], []⟩).target + 1 := by
  rw [delRecCost]
  split
  · rename_i k1 kr1 c1 r1 rest1 h1 h2
    rw [hkr] at h1
    simp at h1
  · rename_i c1 h1 h2
    rw [hcr] at h2
    simp only [List.cons.injEq, and_true] at h2
    obtain rfl := h2
    rfl
  · rename_i h1 h2
    exact (h2 c hkr hcr).elim

end DelRecCostEqns

/-- **A deletion costs one descent, plus the walk to a neighbour if the key sits inside.**
The two never add up: the walk starts where the descent stopped. -/
theorem delRecCost_le (deg : ℕ) (a : α) :
    ∀ t : Node α, delRecCost deg a t ≤ t.height + 2 := by
  intro t
  induction t using delRecCost.induct (deg := deg) (a := a) with
  | case1 ks => simp [delRecCost]
  | case2 ks cs k kr c r rest hkr hcr hlt ih =>
      rw [delRecCost_descend hkr hcr hlt]
      have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega
  | case3 ks cs k kr c r rest hkr hcr hnlt hsc =>
      rw [delRecCost_max hkr hcr hnlt hsc]
      have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := takeMaxCost_le deg c
      simp only [height_node]
      omega
  | case4 ks cs k kr c r rest hkr hcr hnlt hnsc hsr =>
      rw [delRecCost_min hkr hcr hnlt hnsc hsr]
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hr
      have h2 := takeMinCost_le deg r
      simp only [height_node]
      omega
  | case5 ks cs k kr c r rest hkr hcr hnlt hnsc hnsr ih =>
      rw [delRecCost_merge hkr hcr hnlt hnsc hnsr]
      have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      simp only [height_node]
      omega
  | case6 ks cs c hkr hcr ih =>
      rw [delRecCost_last hkr hcr]
      have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega
  | case7 ks cs h1 h2 =>
      rw [delRecCost]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        exact (h1 k1 kr1 c1 r1 rest1 e1 e2).elim
      · rename_i c1 e1 e2
        exact (h2 c1 e1 e2).elim
      · simp

/-- `delete`, charged one block transfer per node entered: its value is `delete`'s, its cost
`delRecCost`, which follows `delRec`'s descent branch for branch. -/
def deleteM (deg : ℕ) (a : α) (t : Node α) : TimeM ℕ (Node α × Bool) :=
  ⟨delete deg a t, delRecCost deg a t⟩

/-- Erasing the cost gives `delete`. -/
theorem ret_deleteM (deg : ℕ) (a : α) (t : Node α) :
    (deleteM deg a t).ret = delete deg a t := rfl

/-- A deletion costs at most `log_deg((n+1)/2) + 2` block transfers. -/
theorem time_deleteM_le_log {deg : ℕ} {bt : Node α} (hv : RootLegal deg bt) (hsz : 1 ≤ bt.size)
    (a : α) : (deleteM deg a bt).time ≤ Nat.log deg ((bt.size + 1) / 2) + 2 := by
  have hdeg : 2 ≤ deg := hv.2.2.2
  have hstruct : 2 * deg ^ bt.height ≤ bt.size + 1 := two_mul_pow_height_le_size_succ hv hsz
  have hdiv : deg ^ bt.height ≤ (bt.size + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hlog : bt.height ≤ Nat.log deg ((bt.size + 1) / 2) :=
    Nat.le_log_of_pow_le (by omega) hdiv
  have := delRecCost_le deg a bt
  simp only [deleteM]
  omega

end BTree.Node

namespace BTree

variable {α : Type} [LinearOrder α]

/-- `search`, charged one block transfer per node entered. -/
def searchM (a : α) (t : BTree α) : TimeM ℕ Bool := Node.searchM a t.root

/-- **Erasing the cost gives ordinary `search`.** -/
theorem ret_searchM (a : α) (t : BTree α) : (searchM a t).ret = search a t :=
  Node.ret_searchM a t.root

/-- **A search costs at most `log_deg((n+1)/2) + 1` block transfers**, at the tree's own minimum
degree. -/
theorem time_searchM_le_log {t : BTree α} (hv : Valid t) (hsz : 1 ≤ t.size) (a : α) :
    (searchM a t).time ≤ Nat.log t.deg ((t.size + 1) / 2) + 1 :=
  Node.time_searchM_le_log (valid_iff_legal.1 hv) hsz a

/-- `delete`, charged one block transfer per node entered. -/
def deleteM (a : α) (t : BTree α) : TimeM ℕ (BTree α × Bool) :=
  ⟨delete a t, Node.delRecCost t.deg a t.root⟩

/-- Erasing the cost gives `delete`. -/
theorem ret_deleteM (a : α) (t : BTree α) : (deleteM a t).ret = delete a t := rfl

/-- A deletion costs at most `log_deg((n+1)/2) + 2` block transfers. -/
theorem time_deleteM_le_log {t : BTree α} (hv : Valid t) (hsz : 1 ≤ t.size) (a : α) :
    (deleteM a t).time ≤ Nat.log t.deg ((t.size + 1) / 2) + 2 :=
  Node.time_deleteM_le_log (valid_iff_legal.1 hv) hsz a

end BTree

/-! ## The `Ω(log_B N)` lower bound, counting step

A comparison-based search procedure modelled as a `DecisionTree`, outside `namespace BTree`. -/

/-- A decision tree: a leaf is an answer, an internal node one question whose possible answers
lead to its children. The arity bound lives in `DecisionTree.Arity`, not in the type, so one
datatype serves every `k`. -/
inductive DecisionTree : Type where
  /-- An answer: the procedure stops here. -/
  | leaf : DecisionTree
  /-- One question; each child is what happens after one of its answers. -/
  | node (children : List DecisionTree) : DecisionTree

namespace DecisionTree

/-- How many answers the tree can return: its leaf count. -/
def leaves : DecisionTree → ℕ
  | leaf => 1
  | node cs => (cs.attach.map fun ⟨c, _⟩ => leaves c).sum

/-- The worst-case number of questions asked: the longest root-to-leaf path, in internal nodes. -/
def depth : DecisionTree → ℕ
  | leaf => 0
  | node cs => (cs.attach.map fun ⟨c, _⟩ => depth c).foldr max 0 + 1

/-- Every question has at most `k` answers. -/
inductive Arity (k : ℕ) : DecisionTree → Prop where
  /-- A leaf asks nothing. -/
  | leaf : Arity k leaf
  /-- A node with at most `k` children, each of arity at most `k`. -/
  | node {cs : List DecisionTree} : cs.length ≤ k → (∀ c ∈ cs, Arity k c) → Arity k (node cs)

private theorem le_foldr_max {x : ℕ} : ∀ {L : List ℕ}, x ∈ L → x ≤ L.foldr max 0
  | _ :: _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max h) (le_max_right _ _)

private theorem sum_le_length_mul {B : ℕ} :
    ∀ {L : List ℕ}, (∀ x ∈ L, x ≤ B) → L.sum ≤ L.length * B
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have ih := sum_le_length_mul (L := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **A tree of depth `d` and arity `k` has at most `k ^ d` leaves**: the leaf count can at most
multiply by `k` per level. -/
theorem leaves_le_pow {k : ℕ} {t : DecisionTree} (ht : Arity k t) : leaves t ≤ k ^ depth t := by
  induction ht with
  | leaf => simp [leaves, depth]
  | @node cs hlen _ ih =>
    rw [leaves, depth, Nat.pow_succ]
    set D := (cs.attach.map fun ⟨c, _⟩ => depth c).foldr max 0
    have hD : ∀ c ∈ cs, depth c ≤ D := fun c hc' =>
      le_foldr_max (List.mem_map.mpr ⟨⟨c, hc'⟩, List.mem_attach _ _, rfl⟩)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : cs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst this; simp
    have hbound : ∀ x ∈ (cs.attach.map fun ⟨c, _⟩ => leaves c), x ≤ k ^ D := by
      intro x hx
      obtain ⟨⟨c, hcm⟩, _, rfl⟩ := List.mem_map.mp hx
      exact le_trans (ih c hcm) (Nat.pow_le_pow_right hk (hD c hcm))
    calc (cs.attach.map fun ⟨c, _⟩ => leaves c).sum
        ≤ (cs.attach.map fun ⟨c, _⟩ => leaves c).length * k ^ D := sum_le_length_mul hbound
      _ = cs.length * k ^ D := by simp
      _ ≤ k * k ^ D := Nat.mul_le_mul_right _ hlen
      _ = k ^ D * k := Nat.mul_comm _ _

end DecisionTree

/-- **The abstract decision-tree depth lower bound.** A decision tree whose questions have at most
`k` answers each, and which can return at least `m` different answers, asks at least
`Nat.clog k m` questions on some input: `Nat.clog k m` is the least `e` with `m ≤ k ^ e`, and the
tree has at most `k ^ depth` leaves (`DecisionTree.leaves_le_pow`).

With one I/O per node, `k := B + 1` routing outcomes per node and `m := N + 1` answers (Vitter,
§11.1), a comparison-based external-memory search needs at least `Nat.clog (B + 1) (N + 1)` I/Os;
that the search is such a tree is the unformalised modelling step. Hashing is not comparison-based
and is not covered. -/
theorem decisionTree_depth_ge {k m : ℕ} (hk : 2 ≤ k) {t : DecisionTree} (ht : t.Arity k)
    (hm : m ≤ t.leaves) : Nat.clog k m ≤ t.depth :=
  (Nat.clog_le_iff_le_pow hk).2 (le_trans hm (DecisionTree.leaves_le_pow ht))

end AlgoDesign.Searching
