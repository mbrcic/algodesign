import AlgoDesign
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! Regression checks for the Search chapter's public specifications. Run with
`lake env lean -DwarningAsError=true AlgoDesignTests/Searching.lean`. -/
namespace AlgoDesignTests
open AlgoDesign.Searching


-- The empty tree is valid at degree two, but degrees zero and one are excluded.
example : BTree.Valid 2 (.leaf [] : BTree Nat) := by decide
example : ¬ BTree.Valid 0 (.leaf [] : BTree Nat) := by simp [BTree.Valid]
example : ¬ BTree.Valid 1 (.leaf [] : BTree Nat) := by simp [BTree.Valid]

-- The `Ω(log_B N)` bound is about a modelled decision tree, not a restated `Nat.clog` fact. A
-- ternary question with a binary follow-up on one answer: four answers, two questions deep, and
-- `decisionTree_depth_ge` bounds the depth of any ternary tree with four answers by
-- `Nat.clog 3 4 = 2`, which this one attains.
private def dt : DecisionTree := .node [.leaf, .node [.leaf, .leaf], .leaf]
example : dt.leaves = 4 ∧ dt.depth = 2 := by simp [dt, DecisionTree.leaves, DecisionTree.depth]
example : Nat.clog 3 4 = 2 := by decide
example : Nat.clog 3 dt.leaves ≤ dt.depth :=
  decisionTree_depth_ge (by norm_num) (.node (by decide) (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact .leaf
    · exact .node (by decide) (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact .leaf)
    · exact .leaf)) le_rfl

-- `floor?`/`ceiling?` are the ends of a one-sided range query, the link `RangeQuery.lean` names.
private def fcTree : BST Nat := .node (.node .leaf 2 (.node .leaf 4 .leaf)) 6 (.node .leaf 8 .leaf)
example : BST.floor? 5 fcTree = some 4 ∧
    (BST.range .unbounded (.included 5) fcTree).getLast? = some 4 := by decide
example : BST.ceiling? 5 fcTree = some 6 ∧
    (BST.range (.included 5) .unbounded fcTree).head? = some 6 := by decide
example : BST.floor? 1 fcTree = none ∧ BST.ceiling? 9 fcTree = none := by decide

-- An internal root must have two children. Its children must meet non-root occupancy bounds.
example : ¬ BTree.RootBranches (.node [] [.leaf [1]] : BTree Nat) := by decide
example : ¬ BTree.Valid 2 (.node [] [.leaf [1]] : BTree Nat) := by decide
example : ¬ BTree.HalfFullToFull 2 (.node [2] [.leaf [], .leaf [3]] : BTree Nat) := by decide
example : ¬ BTree.Valid 2 (.node [2] [.leaf [], .leaf [3]] : BTree Nat) := by decide
example : BTree.Valid 2 (.node [2] [.leaf [1], .leaf [3]] : BTree Nat) := by decide

-- `insert` at degree two, CLRS-style: three keys still fit one block; the fourth splits the
-- root proactively on the way down, and the tree gains a level on every path at once.
-- `rfl` will not do it any more -- the descent recurses on height, not on a subterm.
example : BTree.insert 2 3 (.leaf [1, 2] : BTree Nat) = .leaf [1, 2, 3] := by
  simp [BTree.insert, BTree.insNonfull, BTree.isFull, BTree.nodeKeys, BTree.insKeys]
-- Reads and writes apart (`BTree/IO.lean`). Inserting into a full leaf root: the root split
-- writes the two halves and the new root (3), the leaf the key lands in is written (1); the new
-- root and that leaf are read (2, root included). Into a leaf with room: one read, one write.
example : (BTree.insertIO 2 4 (.leaf [1, 2, 3] : BTree Nat)).time = (2, 4) := by
  simp [BTree.insertIO, BTree.insNonfullIO, BTree.prepare, BTree.prepareSplits, BTree.splitNode,
    BTree.isFull, BTree.nodeKeys, BTree.insKeys]
example : (BTree.insertIO 2 3 (.leaf [1, 2] : BTree Nat)).time = (1, 1) := by
  simp [BTree.insertIO, BTree.insNonfullIO, BTree.isFull, BTree.nodeKeys, BTree.insKeys]
example : (BTree.deleteIO 2 1 (.leaf [1, 2] : BTree Nat)).time = (1, 1) := by
  simp [BTree.deleteIO, BTree.delRecCost, BTree.delRecWrites, BTree.delRecSibReads]
example : (BTree.searchIO 2 (.node [2] [.leaf [1], .leaf [3, 4]] : BTree Nat)).time = (1, 0) := by
  decide
example : BTree.insert 2 4 (.leaf [1, 2, 3] : BTree Nat) = .node [2] [.leaf [1], .leaf [3, 4]] := by
  simp [BTree.insert, BTree.insNonfull, BTree.prepare, BTree.splitNode, BTree.isFull,
    BTree.nodeKeys, BTree.insKeys]
example : (BTree.insert 2 4 (.leaf [1, 2, 3] : BTree Nat)).height = 1 := by
  simp [BTree.insert, BTree.insNonfull, BTree.prepare, BTree.splitNode, BTree.isFull,
    BTree.nodeKeys, BTree.insKeys, BTree.height, BTree.childrenHeight]

-- Re-inserting a key already present adds no key -- and, with the duplicate test folded into
-- the descent, it still splits the full root on the way down before the scan reaches the key.
-- Same three keys, one level taller. That is the price of a single pass, and all three
-- implementations pay it identically.
example : BTree.insert 2 2 (.leaf [1, 2, 3] : BTree Nat) = .node [2] [.leaf [1], .leaf [3]] := by
  simp [BTree.insert, BTree.insNonfull, BTree.prepare, BTree.splitNode, BTree.isFull,
    BTree.nodeKeys]
example : (BTree.insert 2 2 (.leaf [1, 2, 3] : BTree Nat)).size = 3 := by
  simp [BTree.insert, BTree.insNonfull, BTree.prepare, BTree.splitNode, BTree.isFull,
    BTree.nodeKeys, BTree.size, BTree.sizeChildren]

-- The proved obligation, on a concrete tree at a concrete degree. `insertSpec` needs the input
-- to be valid, because the descent's key scan only finds the slot `a` belongs in when the keys
-- above it are actually in order.
private theorem valid_123 : BTree.Valid 2 (.leaf [1, 2, 3] : BTree Nat) := by decide

example : BTree.InsertSpec 2 4 (.leaf [1, 2, 3] : BTree Nat)
    (BTree.insert 2 4 (.leaf [1, 2, 3])) := BTree.insertSpec valid_123 4

-- Descents before split are not rotations: the former can average more than two.
private def chain : Treap Nat :=
  .node .leaf 0 12 (.node .leaf 1 10 (.node .leaf 2 8
    (.node .leaf 3 6 (.node .leaf 4 4 (.node .leaf 5 2 .leaf)))))
example : Treap.Valid chain := by
  norm_num [chain, Treap.Valid, Treap.Sorted, Treap.All, Treap.HeapOrdered, Treap.AllPriority]
example : ¬ Treap.Mem 6 chain := by norm_num [chain, Treap.Mem]
example : chain.size = 6 := by rfl
example : ∀ i, i ≤ 6 → (chain.priorityList.filter (· < (2 * i + 1))).length = i := by
  intro i hi
  interval_cases i <;> norm_num [chain, Treap.priorityList]
example : ((List.range 7).map (fun i ↦ Treap.insertSteps 6 (2 * i + 1) chain)).sum = 21 := by
  norm_num [chain, Treap.insertSteps, List.range_succ]
example : ¬ ((List.range 7).map (fun i ↦ Treap.insertSteps 6 (2 * i + 1) chain)).sum ≤ 2 * 7 := by
  norm_num [chain, Treap.insertSteps, List.range_succ]

-- Duplicates do not change the builder's key set; the miss/hit contract is an equivalence.
example (a : Nat) : a ∈ (buildM [2, 1, 2]).ret ↔ a = 2 ∨ a = 1 := by
  simp only [mem_buildM, List.mem_cons, List.not_mem_nil, or_false]
  tauto
example : (containsM tickEq 2 [1, 2, 3]).ret = true := by
  rw [ret_containsM_tickEq]
  decide
example : (containsM tickEq 4 [1, 2, 3]).ret = false := by
  rw [ret_containsM_tickEq]
  decide
example : (buildM [2, 1, 2]).ret.Nodup := nodup_buildM _

-- CLRS Lemma 13.1 and deletion validity on a one-node tree.
example : RBTree.height (RBTree.insert (1 : Nat) .leaf) ≤ 2 * Nat.log2 2 := by
  have h : RBTree.Valid (RBTree.insert (1 : Nat) .leaf) :=
    RBTree.valid_insert (t := .leaf) (by simp [RBTree.Valid, RBTree.Sorted, RBTree.RootBlack,
      RBTree.NoRedRed, RBTree.BlackHeightOk, RBTree.blackHeight]) 1
  have bound := RBTree.height_le_two_log h
  have hsz : (RBTree.insert (1 : Nat) .leaf).size = 1 := rfl
  rw [hsz] at bound
  exact bound
example : RBTree.Valid (RBTree.delete (1 : Nat) (RBTree.insert 1 .leaf)) :=
  RBTree.valid_delete
    (RBTree.valid_insert (t := (RBTree.leaf : RBTree Nat)) (by
      simp [RBTree.Valid, RBTree.Sorted, RBTree.RootBlack, RBTree.NoRedRed,
        RBTree.BlackHeightOk, RBTree.blackHeight]) 1) 1
-- The standard tree's rotation bounds are counted on the operations themselves: `insertRot`
-- and `deleteRot` tick once per rotation and are proved to return `insert`'s and `delete`'s trees.
-- Both bounds are attained. Inserting 7 below 10 and 5 is Case 2 (a triangle), a rotation at the
-- red child and one at the root; deleting 2 from the tree built from 2, 3, 12, 9, 14, 7 is Case 1
-- falling through to Case 3, three rotations. If a counting run stopped following its operation,
-- the `ret` lines would fail; if it stopped charging a rotation, the `time` lines would.
private def rbBuild (xs : List Nat) : RBTree Nat := xs.foldl (fun t a => RBTree.insert a t) .leaf
example : (RBTree.insertRot 7 (rbBuild [10, 5])).time = 2 := by decide
example : (RBTree.insertRot 7 (rbBuild [10, 5])).ret = RBTree.insert 7 (rbBuild [10, 5]) := by
  decide
example : (RBTree.insertRot 7 (rbBuild [10, 5])).ret =
    .node .black (.node .red .leaf 5 .leaf) 7 (.node .red .leaf 10 .leaf) := by decide
example : (RBTree.deleteRot 2 (rbBuild [2, 3, 12, 9, 14, 7])).time = 3 := by decide
example : (RBTree.deleteRot 2 (rbBuild [2, 3, 12, 9, 14, 7])).ret =
    RBTree.delete 2 (rbBuild [2, 3, 12, 9, 14, 7]) := by decide
-- Case 1's rotation is fused into a reconstruction in `deleteFixupL`; the counting run makes it a
-- literal `rotateLeft`, charges it, and must still return the same tree.
private def rbCase1Sibling : RBTree Nat :=
  .node .red (.node .black .leaf 2 .leaf) 3 (.node .black .leaf 4 .leaf)
example : (RBTree.deleteFixupLRot .black .leaf 1 rbCase1Sibling).ret =
    RBTree.deleteFixupL .black .leaf 1 rbCase1Sibling := by decide
example : (RBTree.deleteFixupLRot .black .leaf 1 rbCase1Sibling).time = 1 := by decide

example : LLRB.height (LLRB.insert (1 : Nat) .leaf) ≤ 2 * Nat.log2 2 := by
  have h : LLRB.Valid (LLRB.insert (1 : Nat) .leaf) :=
    LLRB.valid_insert (t := .leaf) (by
      simp [LLRB.Valid, LLRB.Sorted, LLRB.RootBlack, LLRB.LeftLeaning, LLRB.NoRedRed,
        LLRB.BlackHeightOk, LLRB.blackHeight]) 1
  have bound := LLRB.height_le_two_log h
  have hsz : (LLRB.insert (1 : Nat) .leaf).size = 1 := rfl
  rw [hsz] at bound
  exact bound

-- LLRB deletion's recursive precondition is strictly stronger than `Valid`, and the one-element
-- tree witnesses the gap: it is `Valid`, but `NotTwoNode` needs a red link at the root or its left
-- child and `Valid` forces a black root, so `valid_deleteMin` cannot be applied to it at all.
-- `deleteMinTop`'s priming step is exactly what closes this; `valid_deleteMinTop` has no such
-- side condition. (Unprimed, the recursion does not merely resist proof -- it breaks the color
-- invariants on thousands of random valid trees.)
private def llrbOne : LLRB Nat := .node .black .leaf 1 .leaf
private theorem valid_llrbOne : LLRB.Valid llrbOne :=
  ⟨⟨trivial, trivial, trivial, trivial⟩, rfl, ⟨by simp [LLRB.IsRed], trivial, trivial⟩,
    ⟨by simp, trivial, trivial⟩, by simp [llrbOne, LLRB.BlackHeightOk, LLRB.blackHeight]⟩
example : ¬ LLRB.NotTwoNode llrbOne := by
  rintro (h | h) <;> simp [llrbOne, LLRB.IsRed, LLRB.left] at h
example : LLRB.Valid (LLRB.deleteMinTop llrbOne) := LLRB.valid_deleteMinTop valid_llrbOne
example : LLRB.deleteMinTop llrbOne = .leaf := by
  simp [llrbOne, LLRB.deleteMinTop, LLRB.prime, LLRB.deleteMin, LLRB.blacken, LLRB.isRed]
-- General deletion is verified too, for a present key and for an absent one.
example : LLRB.Valid (LLRB.deleteTop 1 llrbOne) := LLRB.valid_deleteTop valid_llrbOne 1
example : LLRB.Valid (LLRB.deleteTop 99 llrbOne) := LLRB.valid_deleteTop valid_llrbOne 99

-- LLRB has no constant rotation bound. The "at most two per insert" bound is the standard tree's
-- (`RBTree.insert_rotations_le`); an earlier `LLRB.lean` header attributed it to LLRB. Inserting
-- 2, 6, 1, 7, 3, 5 builds the encoding of the 2-3 tree with root (2, 6) over (1), (3, 5), (7);
-- inserting 4 then splits both 3-nodes, and each split costs a left and a right rotation. Four
-- rotations on a tree of height four: `time_insertRot_le_height` is attained.
private def llrbCascade : LLRB Nat := [2, 6, 1, 7, 3, 5].foldl (fun t k => LLRB.insert k t) .leaf
private theorem valid_llrbCascade : LLRB.Valid llrbCascade := by
  have h0 : LLRB.Valid (.leaf : LLRB Nat) := by
    simp [LLRB.Valid, LLRB.Sorted, LLRB.RootBlack, LLRB.LeftLeaning, LLRB.NoRedRed,
      LLRB.BlackHeightOk, LLRB.blackHeight]
  exact LLRB.valid_insert (LLRB.valid_insert (LLRB.valid_insert (LLRB.valid_insert
    (LLRB.valid_insert (LLRB.valid_insert h0 2) 6) 1) 7) 3) 5
example : (LLRB.insertRot 4 llrbCascade).time = 4 := by decide
example : LLRB.height llrbCascade = 4 := by decide
example : ¬ ∀ (t : LLRB Nat) (a : Nat), LLRB.Valid t → (LLRB.insertRot a t).time ≤ 2 := by
  intro h
  have := h llrbCascade 4 valid_llrbCascade
  revert this
  decide

-- The same insert on the 2-3 side. `llrbCascade` encodes the 2-3 tree with root (2, 6); inserting
-- 4 makes (3, 4, 5) a 4-node, which splits and passes 4 up, making the root a 4-node, which splits
-- in turn: the tree grows one level, at the root. The LLRB's four rotations and two color flips
-- compute exactly its encoding (`T23.toLlrb_insert`).
private def t23Cascade : T23 Nat :=
  .three (.two .leaf 1 .leaf) 2 (.three .leaf 3 .leaf 5 .leaf) 6 (.two .leaf 7 .leaf)
example : T23.toLlrb t23Cascade = llrbCascade := rfl
example : T23.insert 4 t23Cascade =
    .two (.two (.two .leaf 1 .leaf) 2 (.two .leaf 3 .leaf)) 4
      (.two (.two .leaf 5 .leaf) 6 (.two .leaf 7 .leaf)) := rfl
example : T23.height (T23.insert 4 t23Cascade) = T23.height t23Cascade + 1 := rfl
example : T23.toLlrb (T23.insert 4 t23Cascade) = LLRB.insert 4 llrbCascade := rfl

-- LLRB deletion has no constant rotation bound either. The standard tree's is three
-- (`RBTree.delete_rotations_le`); `LLRB.time_deleteTopRot_le_height` bounds an LLRB delete by
-- six rotations per level instead. On this valid tree of ten keys and height four, deleting 1
-- rotates four times. The count is the time of `deleteTopRot`, whose result is `deleteTop`'s tree
-- (`LLRB.ret_deleteTopRot`) and whose time is the count read off `delete`'s own branches
-- (`LLRB.time_deleteTopRot`). This tree does not make every rotation site fire; the per-site lines
-- below do, one site each.
private def llrbDel : LLRB Nat :=
  [5, 8, 3, 9, 1, 10, 7, 2, 4, 6].foldl (fun t k => LLRB.insert k t) .leaf
private theorem valid_llrbDel : LLRB.Valid llrbDel := by
  have h0 : LLRB.Valid (.leaf : LLRB Nat) := by
    simp [LLRB.Valid, LLRB.Sorted, LLRB.RootBlack, LLRB.LeftLeaning, LLRB.NoRedRed,
      LLRB.BlackHeightOk, LLRB.blackHeight]
  exact LLRB.valid_insert (LLRB.valid_insert (LLRB.valid_insert (LLRB.valid_insert
    (LLRB.valid_insert (LLRB.valid_insert (LLRB.valid_insert (LLRB.valid_insert
    (LLRB.valid_insert (LLRB.valid_insert h0 5) 8) 3) 9) 1) 10) 7) 2) 4) 6
example : (LLRB.deleteTopRot 1 llrbDel).time = 4 := by decide +kernel
example : LLRB.height llrbDel = 4 := by decide
example : ¬ ∀ (t : LLRB Nat) (a : Nat), LLRB.Valid t → (LLRB.deleteTopRot a t).time ≤ 3 := by
  intro h
  have := h llrbDel 1 valid_llrbDel
  have h4 : (LLRB.deleteTopRot 1 llrbDel).time = 4 := by decide +kernel
  omega
-- An absent key costs nothing: `deleteTop`'s membership check skips the walk.
example : (LLRB.deleteTopRot 11 llrbDel).time = 0 := by decide +kernel
-- Every rotation site of an LLRB delete, made to fire on a small tree, with the exact count. Each
-- line's count comes from one site, or from one site plus another pinned above it, so a counting
-- run that stopped charging that site fails the line (`LLRB.time_deleteRot` fails too). The
-- `fixUp` after an empty right child is the one site no tree reaches with a rotation.
private def llrbOf (ks : List Nat) : LLRB Nat := ks.foldl (fun t k => LLRB.insert k t) .leaf
-- `moveRedLeft` on the way down the left: both of its rotations, and nothing else.
example : (LLRB.deleteTopRot 1 (llrbOf [1, 2, 3, 4])).time = 2 := by decide +kernel
-- `moveRedLeft` inside `deleteMin`: both rotations, and nothing else.
example : (LLRB.deleteMinTopRot (llrbOf [1, 2, 3, 4])).time = 2 := by decide +kernel
-- The preliminary `rotateRight` before descending right, alone.
example : (LLRB.deleteTopRot 2 (llrbOf [1, 2])).time = 1 := by decide +kernel
-- `moveRedRight`'s rotation, alone.
example : (LLRB.deleteTopRot 3 (llrbOf [1, 3, 4, 2])).time = 1 := by decide +kernel
-- `fixUp` after the left descent, alone.
example : (LLRB.deleteTopRot 1 (llrbOf [1, 2, 3])).time = 1 := by decide +kernel
-- `fixUp` inside `deleteMin`, alone.
example : (LLRB.deleteMinTopRot (llrbOf [1, 2, 3])).time = 1 := by decide +kernel
-- `fixUp` after the right descent, with the preliminary `rotateRight` (pinned alone above).
example : (LLRB.deleteTopRot 4 (llrbOf [1, 2, 3, 4, 5, 6])).time = 2 := by decide +kernel
-- `fixUp` after the successor's `deleteMin`, with `moveRedRight` (pinned alone above).
example : (LLRB.deleteTopRot 10 (llrbOf [18, 10, 8, 1, 3, 14, 20, 18, 6, 6, 11, 4])).time = 2 := by
  decide +kernel


-- The LLRB delete is not the 2-3 delete. Deleting 2 from the 3-node root (2, 4) over 1, 3, 5:
-- the 2-3 delete (`T23.delete`, successor from the middle child, the empty middle child merged
-- with its right sibling) gives (3) over (1) and (4, 5); the LLRB delete, which restructures on
-- the way down, gives the encoding of (4) over (1, 3) and (5). Same keys in the same order
-- (`T23.deleteTop_toLlrb`), different trees. Smallest case in an exhaustive search over the
-- balanced 2-3 trees of height at most three: 8784 of 38453 deletions differ.
private def t23Del : T23 Nat :=
  .three (.two .leaf 1 .leaf) 2 (.two .leaf 3 .leaf) 4 (.two .leaf 5 .leaf)
example : T23.delete 2 t23Del = .two (.two .leaf 1 .leaf) 3 (.three .leaf 4 .leaf 5 .leaf) := rfl
example : LLRB.deleteTop 2 (T23.toLlrb t23Del) =
    T23.toLlrb (.two (.three .leaf 1 .leaf 3 .leaf) 4 (.two .leaf 5 .leaf)) := by
  with_unfolding_all rfl
example : ¬ ∀ (t : T23 Nat) (x : Nat), T23.SameDepth t → T23.Sorted t →
    T23.toLlrb (T23.delete x t) = LLRB.deleteTop x (T23.toLlrb t) := by
  intro h
  have he := h t23Del 2 (by simp [t23Del, T23.SameDepth, T23.height])
    (by simp [t23Del, T23.Sorted, T23.All])
  have hl : LLRB.deleteTop 2 (T23.toLlrb t23Del) =
      T23.toLlrb (.two (.three .leaf 1 .leaf 3 .leaf) 4 (.two .leaf 5 .leaf)) := by
    with_unfolding_all rfl
  rw [hl] at he
  have := T23.toLlrb_injective he
  rw [show T23.delete 2 t23Del = .two (.two .leaf 1 .leaf) 3 (.three .leaf 4 .leaf 5 .leaf)
    from rfl] at this
  cases this
-- The 2-3 delete's three shapes of repair on small trees: a leaf 2-node borrowing from a 3-node
-- sibling, a merge that shrinks the tree at the root, and a 3-node losing a key in place.
example : T23.delete 1 (.two (.two .leaf 1 .leaf) 2 (.three .leaf 3 .leaf 4 .leaf) : T23 Nat) =
    .two (.two .leaf 2 .leaf) 3 (.two .leaf 4 .leaf) := rfl
example : T23.delete 1 (.two (.two .leaf 1 .leaf) 2 (.two .leaf 3 .leaf) : T23 Nat) =
    .three .leaf 2 .leaf 3 .leaf := rfl
example : T23.delete 3 (.three .leaf 1 .leaf 3 .leaf : T23 Nat) = .two .leaf 1 .leaf := rfl

-- The 2-3 delete, arm by arm, each by `rfl` on the tree it computes. `d2 k` and `d3 a b` are the
-- bottom 2- and 3-nodes. A repair rule changed in any arm -- borrowing where the rule merges,
-- taking the other sibling, placing the separating key elsewhere -- changes one of these trees.
private def d2 (k : Nat) : T23 Nat := .two .leaf k .leaf
private def d3 (a b : Nat) : T23 Nat := .three .leaf a .leaf b .leaf
-- `del` at a leaf, and at a bottom 2-node on each side and at its key (successor, and none).
example : T23.delete 5 (.leaf : T23 Nat) = .leaf := rfl
example : T23.delete 3 (.two (d2 1) 2 (d2 3)) = .three .leaf 1 .leaf 2 .leaf := rfl
example : T23.delete 2 (.two (d2 1) 2 (d2 3)) = .three .leaf 1 .leaf 3 .leaf := rfl
example : T23.delete 1 (d2 1) = .leaf := rfl
-- `del` at a 3-node: below `a`, between the keys, above `b`, at `b` (successor, and none), and
-- at `a` with no successor below it. (At `a` with a successor is `t23Del` above.)
example : T23.delete 1 (.three (d2 1) 2 (d2 3) 4 (d2 5)) =
    .two (.three .leaf 2 .leaf 3 .leaf) 4 (d2 5) := rfl
example : T23.delete 3 (.three (d2 1) 2 (d2 3) 4 (d2 5)) =
    .two (d2 1) 2 (.three .leaf 4 .leaf 5 .leaf) := rfl
example : T23.delete 5 (.three (d2 1) 2 (d2 3) 4 (d2 5)) =
    .two (d2 1) 2 (.three .leaf 3 .leaf 4 .leaf) := rfl
example : T23.delete 4 (.three (d2 1) 2 (d2 3) 4 (d2 5)) =
    .two (d2 1) 2 (.three .leaf 3 .leaf 5 .leaf) := rfl
example : T23.delete 2 (d3 1 2) = d2 1 := rfl
example : T23.delete 1 (d3 1 2) = d2 2 := rfl
-- The middle child comes back short and its *left* sibling is a 3-node, its right a 2-node. The
-- rule repairs from the right sibling, merging; a repair that borrowed from the left 3-node first
-- would give `three (d2 0) 1 (d2 2) 4 (d2 5)` instead.
example : T23.delete 3 (.three (d3 0 1) 2 (d2 3) 4 (d2 5)) =
    .two (d3 0 1) 2 (.three .leaf 4 .leaf 5 .leaf) := rfl
-- Each repair's borrow from a 3-node sibling (`node21` is the `d3 3 4` case the earlier examples
-- pin).
example : T23.delete 4 (.two (d3 1 2) 3 (d2 4)) = .two (d2 1) 2 (d2 3) := rfl
example : T23.delete 1 (.three (d2 1) 2 (d3 3 4) 5 (d2 6)) =
    .three (d2 2) 3 (d2 4) 5 (d2 6) := rfl
example : T23.delete 3 (.three (d2 1) 2 (d2 3) 4 (d3 5 6)) =
    .three (d2 1) 2 (d2 4) 5 (d2 6) := rfl
example : T23.delete 6 (.three (d2 1) 2 (d3 3 4) 5 (d2 6)) =
    .three (d2 1) 2 (d2 3) 4 (d2 5) := rfl
-- Each repair's `same` arm: the child kept its height, so nothing moves.
example : T23.delete 0 (.two (d3 0 1) 2 (d2 3)) = .two (d2 1) 2 (d2 3) := rfl
example : T23.delete 4 (.two (d2 1) 2 (d3 3 4)) = .two (d2 1) 2 (d2 3) := rfl
example : T23.delete 0 (.three (d3 0 1) 2 (d2 3) 4 (d2 5)) = .three (d2 1) 2 (d2 3) 4 (d2 5) :=
  rfl
example : T23.delete 3 (.three (d2 1) 2 (d3 3 4) 5 (d2 6)) = .three (d2 1) 2 (d2 4) 5 (d2 6) :=
  rfl
example : T23.delete 6 (.three (d2 1) 2 (d2 3) 4 (d3 5 6)) = .three (d2 1) 2 (d2 3) 4 (d2 5) :=
  rfl
-- The `leaf`-sibling arms, which no balanced tree reaches, keep their keys.
example : T23.node21 (.short (d2 1)) 2 .leaf = .same (.two (d2 1) 2 .leaf) := rfl
example : T23.node22 .leaf 2 (.short (d2 3)) = .same (.two .leaf 2 (d2 3)) := rfl
example : T23.node31 (.short (d2 1)) 2 .leaf 3 (d2 4) = .same (.three (d2 1) 2 .leaf 3 (d2 4)) :=
  rfl
example : T23.node32 (d2 1) 2 (.short (d2 3)) 4 .leaf = .same (.three (d2 1) 2 (d2 3) 4 .leaf) :=
  rfl
example : T23.node33 (d2 1) 2 .leaf 3 (.short (d2 4)) = .same (.three (d2 1) 2 .leaf 3 (d2 4)) :=
  rfl
-- An internal key one level up: the successor comes from the bottom of the right subtree by
-- `splitMin`, through a 2-node (which underflows, and the whole tree shrinks) or a 3-node.
example : T23.delete 4 (.two (.two (d2 1) 2 (d2 3)) 4 (.two (d2 5) 6 (d2 7))) =
    .three (d2 1) 2 (d2 3) 5 (d3 6 7) := rfl
example : T23.delete 4 (.two (.two (d2 1) 2 (d2 3)) 4 (.three (d2 5) 6 (d2 7) 8 (d2 9))) =
    .two (.two (d2 1) 2 (d2 3)) 5 (.two (d3 6 7) 8 (d2 9)) := rfl
example : T23.delete 2 (.two (d2 1) 2 (d3 3 4)) = .two (d2 1) 3 (d2 4) := rfl
-- And one level up inside a 3-node: a key of the middle child (which underflows and merges with
-- the right sibling), `b` (successor from the right), `a` (successor from the middle).
example : T23.delete 6 (.three (.two (d2 1) 2 (d2 3)) 4 (.two (d2 5) 6 (d2 7)) 8
      (.two (d2 9) 10 (d2 11))) =
    .two (.two (d2 1) 2 (d2 3)) 4 (.three (d3 5 7) 8 (d2 9) 10 (d2 11)) := rfl
example : T23.delete 8 (.three (.two (d2 1) 2 (d2 3)) 4 (.two (d2 5) 6 (d2 7)) 8
      (.two (d2 9) 10 (d2 11))) =
    .two (.two (d2 1) 2 (d2 3)) 4 (.three (d2 5) 6 (d2 7) 9 (d3 10 11)) := rfl
example : T23.delete 4 (.three (.two (d2 1) 2 (d2 3)) 4 (.two (d2 5) 6 (d2 7)) 8
      (.two (d2 9) 10 (d2 11))) =
    .two (.two (d2 1) 2 (d2 3)) 5 (.three (d3 6 7) 8 (d2 9) 10 (d2 11)) := rfl
-- The LLRB delete shortens the tree exactly when the 2-3 delete does (`T23.bheight_deleteTop`):
-- deleting 1 below the root 2 merges everything into one 3-node on both sides, and the LLRB's
-- black height drops from 3 to 2 as the 2-3 height drops from 2 to 1.
example : LLRB.bheight (T23.toLlrb (.two (d2 1) 2 (d2 3))) = 3 ∧
    LLRB.bheight (LLRB.deleteTop 1 (T23.toLlrb (.two (d2 1) 2 (d2 3)))) = 2 ∧
    T23.height (T23.delete 1 (.two (d2 1) 2 (d2 3))) = 1 := by decide +kernel
-- `PriorityInjective` is load-bearing in `eq_of_valid`, not decoration: with a tied priority,
-- these two *distinct* treaps are both valid, hold the same keys, and answer every priority
-- lookup identically. Heap order stops pinning the root as soon as the maximum is not unique.
private def tieA : Treap Nat := .node .leaf 0 5 (.node .leaf 1 5 .leaf)
private def tieB : Treap Nat := .node (.node .leaf 0 5 .leaf) 1 5 .leaf
example : Treap.Valid tieA := by
  norm_num [tieA, Treap.Valid, Treap.Sorted, Treap.All, Treap.HeapOrdered, Treap.AllPriority]
example : Treap.Valid tieB := by
  norm_num [tieB, Treap.Valid, Treap.Sorted, Treap.All, Treap.HeapOrdered, Treap.AllPriority]
example : ∀ a, Treap.Mem a tieA ↔ Treap.Mem a tieB := by
  intro a; simp [tieA, tieB, Treap.Mem]
example : ∀ a, Treap.priorityOf a tieA = Treap.priorityOf a tieB := by
  rintro (_ | _ | n) <;> simp [tieA, tieB, Treap.priorityOf]
example : tieA ≠ tieB := by decide
-- Treap `delete` rotates the node down (`removeRoot`), as the book and the Rust's `remove_root`
-- do, not by a join. On a priority tie the right child is lifted, the Rust's rule: deleting 2 here
-- sinks it under 3, and 1 stays below 3 on the left. Lifting 1 instead, as a join would, gives a
-- different tree that is also valid.
private def tieDel : Treap Nat := .node (.node .leaf 1 5 .leaf) 2 9 (.node .leaf 3 5 .leaf)
example : Treap.delete 2 tieDel = Treap.removeRoot tieDel := Treap.delete_node_self _ _ _ _
example : Treap.delete 2 tieDel = .node (.node .leaf 1 5 .leaf) 3 5 .leaf := by
  simp [tieDel, Treap.delete, Treap.removeRoot, Treap.liftsLeft, Treap.rotateLeft,
    Treap.rotateRight]
-- With tied priorities `DeleteSpec` cannot pin the tree, so the tie rule lives in the test above
-- rather than in the spec: lifting 1 instead of 3 also meets the obligation, and is not what
-- `delete` builds.
private def tieOther : Treap Nat := .node .leaf 1 5 (.node .leaf 3 5 .leaf)
example : Treap.DeleteSpec 2 tieDel tieOther := by
  refine ⟨fun b => ?_, fun b hb => ?_, fun _ => ?_⟩
  · simp [tieDel, tieOther, Treap.Mem]; omega
  · rcases b with _ | _ | _ | _ | b
    · decide
    · decide
    · exact absurd rfl hb
    · decide
    · have h1 : ¬ b + 4 < 1 := by omega
      have h2 : ¬ b + 4 < 2 := by omega
      have h3 : ¬ b + 4 < 3 := by omega
      simp [tieDel, tieOther, Treap.priorityOf, h1, h2, h3]
  · norm_num [tieOther, Treap.Valid, Treap.Sorted, Treap.All, Treap.HeapOrdered, Treap.AllPriority]
example : tieOther ≠ Treap.delete 2 tieDel := by
  simp [tieOther, tieDel, Treap.delete, Treap.removeRoot, Treap.liftsLeft, Treap.rotateLeft,
    Treap.rotateRight]
-- `DeleteSpec` names priorities, as `InsertSpec` does. Deleting 2 below rotates 3 (priority 7)
-- up; the impostor is a valid treap on the same surviving keys in which key 1 now carries
-- priority 8. A keys-only spec accepts it; `DeleteSpec` must not, and `delete` does not produce it.
private def delBefore : Treap Nat := .node (.node .leaf 1 5 .leaf) 2 9 (.node .leaf 3 7 .leaf)
private def delImpostor : Treap Nat := .node .leaf 1 8 (.node .leaf 3 7 .leaf)
example : Treap.delete 2 delBefore = .node (.node .leaf 1 5 .leaf) 3 7 .leaf := by
  simp [delBefore, Treap.delete, Treap.removeRoot, Treap.liftsLeft, Treap.rotateLeft,
    Treap.rotateRight]
example : Treap.Valid delImpostor := by
  norm_num [delImpostor, Treap.Valid, Treap.Sorted, Treap.All, Treap.HeapOrdered,
    Treap.AllPriority]
example : ∀ b, Treap.Mem b delImpostor ↔ (b ≠ 2 ∧ Treap.Mem b delBefore) := by
  intro b; simp [delImpostor, delBefore, Treap.Mem]; omega
example : ¬ Treap.DeleteSpec 2 delBefore delImpostor :=
  fun h => absurd (h.2.1 1 (by decide)) (by decide)
example : Treap.DeleteSpec 2 delBefore (Treap.delete 2 delBefore) :=
  Treap.deleteSpec (by norm_num [delBefore, Treap.Valid, Treap.Sorted, Treap.All,
    Treap.HeapOrdered, Treap.AllPriority]) 2

-- Existence and uniqueness together, on a concrete list: exactly one valid treap holds this
-- data, and permuting the insertion order lands on exactly the same tree.
private def pairs : List (Nat × Nat) := [(2, 30), (1, 10), (3, 20)]
example : (pairs.map Prod.fst).Nodup := by decide
example : (pairs.map Prod.snd).Nodup := by decide
example : ∃! t : Treap Nat, Treap.Valid t ∧ Treap.Represents t pairs :=
  Treap.existsUnique_of_nodup (by decide) (by decide)
example : Treap.ofList pairs = Treap.ofList [(1, 10), (3, 20), (2, 30)] :=
  Treap.ofList_eq_of_perm (by decide) (by decide) (by decide)

-- Binary search on seven sorted keys: a hit returns its index, and a miss costs exactly the
-- `Nat.log2 7 + 1 = 3` probes `searchProbes_le` allows -- the bound is attained, not slack.
example : search 5 #[1, 3, 5, 7, 9, 11, 13] = some 2 := by decide +kernel
example : searchProbes 4 #[1, 3, 5, 7, 9, 11, 13] = 3 := by decide +kernel
-- The Search chapter's keyring: fifteen keys, hunting for 38. The closed stretch
-- glances at 23, 35, 41 and then 38 itself: four glances, as the chapter counts them.
example : search 38 #[2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 38, 41, 44] = some 12 ∧
    searchProbes 38 #[2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 38, 41, 44] = 4 := by
  decide +kernel

-- LSM compaction. The merge is newer-wins on a tied key: key 1's newer value 10 survives, the
-- older 5 is dropped unread, and the newer tombstone for 3 shadows the older 9. A merge that let
-- the older entry win would fail both.
example : Run.mergeRuns ([(1, some 10), (3, none)] : Run Nat Nat)
    [(1, some 5), (2, some 7), (3, some 9)] = [(1, some 10), (2, some 7), (3, none)] := by decide
-- A tombstone for key 1 above the run holding its older value 5.
private def tombAbove : List (Run Nat Nat) := [[(1, none)], [(1, some 5), (2, some 7)]]

-- The bottom merge collects the tombstone: nothing older is left for it to shadow.
example : LSM.compact tombAbove = [[(2, some 7)]] := by decide
-- So `lookup` moves (a deletion becomes silence) while `get` does not: exactly `PreservesGet`.
example : LSM.lookup 1 tombAbove = some none ∧
    LSM.lookup 1 (LSM.compact tombAbove) = none ∧
    LSM.get 1 (LSM.compact tombAbove) = none := by
  decide
-- Above the bottom the tombstone must stay: collecting it here would resurrect key 1's older
-- value 5 from the run beneath.
example : LSM.compactAt 0 ([[(1, none)], [(2, some 7)], [(1, some 5)]] : List (Run Nat Nat))
    = [[(1, none), (2, some 7)], [(1, some 5)]] := by decide
example : LSM.get 1
    (LSM.compactAt 0 ([[(1, none)], [(2, some 7)], [(1, some 5)]] : List (Run Nat Nat))) =
      none := by
  decide
-- The two steps apart, as the library takes them: level 0's fold merges at the bottom and keeps
-- the tombstone; collecting it is a separate step that removes no run.
example : LSM.mergeAt 0 ([[(1, none)], [(1, some 5)]] : List (Run Nat Nat)) = [[(1, none)]] := by
  decide
example : LSM.dropBottom ([[(2, some 7)], [(1, none), (3, some 4)]] : List (Run Nat Nat))
    = [[(2, some 7)], [(3, some 4)]] := by decide

-- `CompactSpec` admits collecting a spent tombstone at the bottom: the bottom merge drops
-- key 1's tombstone, so `lookup 1` moves from "deleted" to "never written", and the pair is still
-- a compaction in `CompactSpec`'s sense. Were `CompactSpec` to ask for `PreservesLookup`, no proof
-- of this conjunction could exist.
example : LSM.CompactSpec tombAbove [[(2, some 7)]] ∧
    ¬ LSM.PreservesLookup tombAbove [[(2, some 7)]] := by
  refine ⟨?_, fun h => absurd (h 1) (by decide)⟩
  have h := LSM.compactSpec_compact (t := tombAbove)
    (by decide)
  rwa [show LSM.compact tombAbove
    = [[(2, some 7)]] by decide] at h

-- The store and its policy, `lsm.rs` run by hand. Writes as a list of (key, value-or-tombstone).
private def lsmRun (sh : LSM.Shape) (ops : List (Nat × Option Nat)) : LSM.Store Nat Nat :=
  ops.foldl (fun s (a, v) => LSM.Store.write a v s) (LSM.Store.empty sh)

-- The chapter's two pages (`the_chapters_two_pages_are_two_sealed_runs`): charger 1, passport 2,
-- scissors 3, umbrella 4. A memtable of three fills twice; Page 2 is filed in front of Page 1,
-- which keeps its stale entries, and the tombstone for scissors stays because Page 1 is older.
private def twoPages : LSM.Store Nat Nat :=
  lsmRun ⟨3, 10, 4⟩ [(1, some 10), (2, some 20), (3, some 30), (1, some 11), (3, none),
    (4, some 40)]
example : twoPages.memtable = [] ∧
    twoPages.levels = [[[(1, some 11), (3, none), (4, some 40)],
      [(1, some 10), (2, some 20), (3, some 30)]]] := by decide
example : twoPages.lookup 1 = some (some 11) ∧ twoPages.lookup 3 = some none ∧
    twoPages.lookup 2 = some (some 20) ∧ twoPages.lookup 5 = none := by decide
-- `compact_fully` merges both pages and collects the tombstone: scissors is now never-written.
example : (LSM.Store.compactFully twoPages).levels =
    [[[(1, some 11), (2, some 20), (4, some 40)]]] ∧
    (LSM.Store.compactFully twoPages).lookup 3 = none := by decide

-- A cascade (capacity 2, ratio 2, level 0 merged when it reaches three runs; level 1 may hold 4
-- entries, level 2 eight), checked against the Python `LSM` at the same shape. The third flush
-- fills level 0: its three runs merge and land in a new deepest level 1, where 5's tombstone is
-- collected.
private def cascadeOps : List (Nat × Option Nat) :=
  [(5, some 50), (3, some 30), (5, none), (1, some 10), (7, some 70), (2, some 20)]
example : (lsmRun ⟨2, 2, 3⟩ cascadeOps).levels =
    [[], [[(1, some 10), (2, some 20), (3, some 30), (7, some 70)]]] := by decide
-- Two flushes later a tombstone for 3 is filed in level 0 and kept, since level 1 is older.
private def cascadeOps' : List (Nat × Option Nat) :=
  cascadeOps ++ [(9, some 90), (4, some 40), (3, none), (6, some 60)]
example : (lsmRun ⟨2, 2, 3⟩ cascadeOps').levels =
    [[[(3, none), (6, some 60)], [(4, some 40), (9, some 90)]],
      [[(1, some 10), (2, some 20), (3, some 30), (7, some 70)]]] := by decide
-- The next spill merges into level 1, the deepest, collecting 3's tombstone; level 1 then holds
-- eight entries against a budget of four and is pushed into a new level 2, staying behind as an
-- empty slot. A cascade that renumbered levels or kept the tombstone would fail this.
example : (lsmRun ⟨2, 2, 3⟩ (cascadeOps' ++ [(8, some 80), (10, some 100)])).levels =
    [[], [], [[(1, some 10), (2, some 20), (4, some 40), (6, some 60), (7, some 70),
      (8, some 80), (9, some 90), (10, some 100)]]] := by decide
-- A push with something below keeps its tombstones; with nothing below it collects them, and a
-- merge left holding nothing leaves the level an empty slot, not a slot holding an empty run.
example : LSM.Store.pushInto ([(4, none)] : Run Nat Nat) [] false = [[(4, none)]] ∧
    LSM.Store.pushInto ([(4, none)] : Run Nat Nat) [] true = [] := by decide
-- The cascade's fuel is enough, and not by a wide margin. A memtable of one entry and level 0
-- merged at nine runs: the ninth write spills nine entries into level 1, and the cascade pushes
-- them through budgets 2, 4 and 8 to level 4, whose budget of 16 holds them. The Python `LSM` gives
-- the same level sizes. A fuel of one more than the number of levels stops the cascade at level
-- 3, over budget; `flush_fuel_add` proves `Store.fuel` is enough.
private def deepCascade : LSM.Store Nat Nat :=
  lsmRun ⟨1, 2, 9⟩ ((List.range 9).map fun i => (i + 1, some (i + 1)))
example : deepCascade.levels.map List.length = [0, 0, 0, 0, 1] := by decide
example : (deepCascade.levels.map fun l => l.map List.length) = [[], [], [], [], [9]] := by decide
-- The Rust's `is_valid`, every conjunct, holds on the stores the tests above build: here every
-- level between 0 and the deepest within budget, and below a store whose oldest run is clean
-- although a tombstone was written (3's, collected by the push into the deepest level).
example : LSM.Store.Valid deepCascade := by decide
example : LSM.Store.Valid
    (lsmRun ⟨2, 2, 3⟩ [(5, some 50), (3, some 30), (5, none), (1, some 10), (7, some 70),
      (2, some 20), (9, some 90), (4, some 40), (3, none), (6, some 60), (8, some 80),
      (10, some 100)]) := by decide
-- And it is not vacuous: a level over budget above the deepest, or a tombstone in the oldest run
-- below level 0, fails it. In level 0 a tombstone is allowed: a flush drops none.
example : ¬ LSM.Store.Valid
    (⟨⟨1, 2, 9⟩, [], [[], [[(1, some 1), (2, some 2), (3, some 3)]], [[(4, some 4)]]]⟩ :
      LSM.Store Nat Nat) := by decide
example : ¬ LSM.Store.Valid
    (⟨⟨1, 2, 9⟩, [], [[], [[(1, none)]]]⟩ : LSM.Store Nat Nat) := by decide
example : LSM.Store.Valid
    (⟨⟨1, 2, 9⟩, [], [[[(1, none)]]]⟩ : LSM.Store Nat Nat) := by decide
-- The same store at an unusable shape fails `ShapeUsable` alone: a ratio below two, a memtable of
-- no entries, a level 0 of no runs (the empty store, at each).
example : ¬ LSM.Store.Valid (⟨⟨1, 1, 9⟩, [], [[[(1, none)]]]⟩ : LSM.Store Nat Nat) ∧
    LSM.Store.FewBatches (⟨⟨1, 1, 9⟩, [], [[[(1, none)]]]⟩ : LSM.Store Nat Nat) := by decide
example : ¬ LSM.Store.Valid (LSM.Store.empty ⟨0, 2, 1⟩ : LSM.Store Nat Nat) ∧
    ¬ LSM.Store.Valid (LSM.Store.empty ⟨1, 2, 0⟩ : LSM.Store Nat Nat) ∧
    LSM.Store.Valid (LSM.Store.empty ⟨1, 2, 1⟩ : LSM.Store Nat Nat) := by decide

-- A merge that cancels out leaves its level an empty slot, not a slot holding an empty run
-- (`a_merge_that_cancels_out_leaves_its_level_empty`). A memtable of one entry and level 0
-- merged at two runs: writing 1 files it, deleting 1 spills both into a new level 1, where the
-- tombstone meets its value with nothing below, and both go. The next flush, of a tombstone for
-- 2, files it in level 0 as it is -- a flush drops no tombstone, even into a store holding no
-- run -- and the flush after that carries it into level 1, where nothing lies below, and drops it.
private def cancelled : LSM.Store Nat Nat := lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none)]
example : cancelled.levels = [[], []] := by decide
example : LSM.Store.Valid cancelled := by decide
example : (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none)]).levels = [[[(2, none)]], []] := by
  decide
example : LSM.Store.lookup 2 (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none)]) =
    some none := by
  decide
example : (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none), (3, some 3)]).levels =
    [[], [[(3, some 3)]]] := by decide
example : LSM.Store.get 1 (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none)]) = none := by
  decide
example : LSM.Store.Valid
    (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none)]) := by
  decide
example : LSM.Store.get 3
    (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none), (3, some 3), (4, some 4)]) = some 3 := by
  decide
example : LSM.Store.Valid
    (lsmRun ⟨1, 2, 2⟩ [(1, some 1), (1, none), (2, none), (3, some 3), (4, some 4)]) := by
  decide

-- A tombstone above an emptied level is dropped (`a_tombstone_above_an_emptied_level_is_dropped`):
-- tombstones go in a merge with nothing below it, not only in one into the last slot. Four writes
-- reach level 2; four deletes cancel them there, leaving three empty slots; then 5 and its
-- tombstone merge into level 1, above the empty level 2, and cancel out too. The Rust test asserts
-- three levels, a four-entry run in level 2, and every slot empty; the exact level lists are the
-- model's.
private def fourWrites : List (Nat × Option Nat) :=
  (List.range 4).map fun i => (i + 1, some (i + 1))
private def fourDeletes : List (Nat × Option Nat) := (List.range 4).map fun i => (i + 1, none)
example : ((lsmRun ⟨1, 2, 2⟩ fourWrites).levels.map fun l => l.map List.length) =
    [[], [], [4]] := by decide
example : (lsmRun ⟨1, 2, 2⟩ (fourWrites ++ fourDeletes)).levels = [[], [], []] := by decide
private def aboveEmptied : LSM.Store Nat Nat :=
  lsmRun ⟨1, 2, 2⟩ (fourWrites ++ fourDeletes ++ [(5, some 5), (5, none)])
example : aboveEmptied.levels = [[], [], []] := by decide
example : LSM.Store.lookup 5 aboveEmptied = none := by decide
example : LSM.Store.Valid aboveEmptied := by decide

/-! ## Each piece of a `Valid` decides on its own -/

-- A BST with a smaller key on the right breaks box invariant 1.
example : ¬ BST.Valid (BST.node .leaf (2 : ℕ) (BST.node .leaf 1 .leaf)) := by decide
-- An LLRB with a red right link breaks box invariant 3 alone.
example : LLRB.Sorted (LLRB.node .black .leaf (1 : ℕ) (LLRB.node .red .leaf 2 .leaf)) ∧
    LLRB.RootBlack (LLRB.node .black .leaf (1 : ℕ) (LLRB.node .red .leaf 2 .leaf)) ∧
    ¬ LLRB.LeftLeaning (LLRB.node .black .leaf (1 : ℕ) (LLRB.node .red .leaf 2 .leaf)) := by
  decide
-- A treap whose child outranks its parent breaks `HeapOrdered` alone.
example : Treap.Sorted (Treap.node .leaf (1 : ℕ) 1 (Treap.node .leaf 2 5 .leaf)) ∧
    ¬ Treap.HeapOrdered (Treap.node .leaf (1 : ℕ) 1 (Treap.node .leaf 2 5 .leaf)) := by decide
-- A 2-3 tree with one deeper side breaks `SameDepth` alone.
example : T23.Sorted (T23.two .leaf (1 : ℕ) (T23.two .leaf 2 .leaf)) ∧
    ¬ T23.SameDepth (T23.two .leaf (1 : ℕ) (T23.two .leaf 2 .leaf)) := by decide
-- Binary search's bracket: in `#[1, 3, 5]` the key 3 lies in `[0, 2]` and not in `[2, 2]`.
example : BinarySearch.Valid (BinarySearch.Stretch.first 3 #[(1 : ℕ), 3, 5]) ∧
    ¬ BinarySearch.KeyInStretch (⟨3, #[1, 3, 5], 2, 2⟩ : BinarySearch.Stretch ℕ) := by decide
-- The scan's state: no 4 among the first two of `[1, 2, 4]`, but there is one among all three.
example : SequentialSearch.Valid (⟨4, [1, 2, 4], 2, by decide⟩ : SequentialSearch.Scan ℕ) ∧
    ¬ SequentialSearch.Valid (⟨4, [1, 2, 4], 3, by decide⟩ : SequentialSearch.Scan ℕ) := by
  decide
-- A B-tree of minimum degree 2: a root over two leaves meets every piece; a child holding a key
-- outside its bounds breaks `KeysInOrder` (box invariant 1) alone.
example : BTree.Valid 2 (BTree.node [5] [BTree.leaf [1, 3], BTree.leaf [7]]) := by decide
example : BTree.OneMoreChild (BTree.node [5] [BTree.leaf [1, 6], BTree.leaf [7]] : BTree ℕ) ∧
    BTree.HalfFullToFull 2 (BTree.node [5] [BTree.leaf [1, 6], BTree.leaf [7]] : BTree ℕ) ∧
    BTree.RootBranches (BTree.node [5] [BTree.leaf [1, 6], BTree.leaf [7]] : BTree ℕ) ∧
    BTree.SameDepth (BTree.node [5] [BTree.leaf [1, 6], BTree.leaf [7]] : BTree ℕ) ∧
    ¬ BTree.KeysInOrder (BTree.node [5] [BTree.leaf [1, 6], BTree.leaf [7]] : BTree ℕ) := by
  decide
-- The whole conjunctions decide too, black balance included.
example : LLRB.Valid (LLRB.node .black (LLRB.node .red .leaf (1 : ℕ) .leaf) 2 .leaf) := by decide
example : RBTree.Valid (RBTree.node .black .leaf (1 : ℕ) (RBTree.node .red .leaf 2 .leaf)) := by
  decide
example :
    ¬ LLRB.BlackHeightOk (LLRB.node .black (LLRB.node .black .leaf (1 : ℕ) .leaf) 2 .leaf) := by
  decide

/-! ### The contracts reject the naive candidates

A design that keeps its keys as the bits of one number, in one node or one entry, fails the BST's,
the LLRB's, the B-tree's and the LSM's promise, read through the structure's own listing or `get`.
An insert that deletes the key first, so a present key takes the new priority, fails `InsertSpec`,
which keeps a present key's priority. -/

section Contracts

/-- Clear bit `a` of `m`. -/
private def clearBit (m a : ℕ) : ℕ := if m.testBit a then m ^^^ 2 ^ a else m

private def bstCode : BST ℕ → ℕ | .node .leaf m .leaf => m | _ => 0

private def bitsetBST : BST.Ops ℕ where
  empty := .node .leaf 0 .leaf
  insert a t := .node .leaf (bstCode t ||| 2 ^ a) .leaf
  delete a t := .node .leaf (clearBit (bstCode t) a) .leaf
  search a t := (bstCode t).testBit a
  Valid := BST.Valid
  searchM a t := ⟨(bstCode t).testBit a, min 1 (BST.height t)⟩
  insertM a t := ⟨.node .leaf (bstCode t ||| 2 ^ a) .leaf, min 1 (BST.height t)⟩
  counted _ _ := ⟨rfl, rfl⟩

example : ¬ BST.Contract bitsetBST := by
  intro h
  have := h.promise.keys_empty
  revert this
  decide

private def llrbCode : LLRB ℕ → ℕ | .node _ .leaf m .leaf => m | _ => 0

private def bitsetLLRB : LLRB.Ops ℕ where
  empty := .node .black .leaf 0 .leaf
  insert a t := .node .black .leaf (llrbCode t ||| 2 ^ a) .leaf
  delete a t := .node .black .leaf (clearBit (llrbCode t) a) .leaf
  search a t := (llrbCode t).testBit a
  Valid := LLRB.Valid
  searchM a t := ⟨(llrbCode t).testBit a, 1⟩
  insertM a t := ⟨.node .black .leaf (llrbCode t ||| 2 ^ a) .leaf, 1⟩
  deleteRot a t := ⟨.node .black .leaf (clearBit (llrbCode t) a) .leaf, 0⟩
  counted _ _ := ⟨rfl, rfl, rfl⟩

example : ¬ LLRB.Contract bitsetLLRB := by
  intro h
  have := h.promise.keys_empty
  revert this
  decide

private def headCode : Run ℕ Unit → Option ℕ | (c, some ()) :: _ => some c | _ => none

private def storeCode (s : LSM.Store ℕ Unit) : ℕ :=
  ((headCode s.memtable).orElse fun _ => headCode ((s.levels.headD []).headD [])).getD 0

private def cell (c : ℕ) : Run ℕ Unit := [(c, some ())]

private def bitsetLSM : LSM.Ops ℕ Unit where
  empty sh := ⟨sh, [], []⟩
  write a _ s := { s with memtable := cell (storeCode s ||| 2 ^ a) }
  delete a s := { s with memtable := cell (clearBit (storeCode s) a) }
  Valid := LSM.Store.Valid
  getM a s := ⟨LSM.Store.get a s, 0⟩
  counted _ _ := rfl

example : ¬ LSM.Contract bitsetLSM := by
  intro h
  have := h.promise.1.1 0 () (bitsetLSM.empty ⟨1, 2, 1⟩) (h.promise.2.2.2.1 _ (by decide))
  revert this
  decide

/-- Insert by deleting the key first: a present key takes the new priority. -/
private def reinsert (a pr : ℕ) (t : Treap ℕ) : Treap ℕ := Treap.insert a pr (Treap.delete a t)

example :
    ¬ Treap.InsertSpec 1 9 (.node .leaf 1 5 .leaf) (reinsert 1 9 (.node .leaf 1 5 .leaf)) := by
  intro h
  have := h.2.1 1 (Or.inr (Or.inr (Or.inl rfl)))
  revert this
  decide +kernel

private def btreeCode : BTree ℕ → ℕ | .leaf [m] => m | _ => 0

private def bitsetBTree : BTree.Ops ℕ 2 where
  empty := .leaf [0]
  insert a t := .leaf [btreeCode t ||| 2 ^ a]
  delete a t := .leaf [clearBit (btreeCode t) a]
  search a t := (btreeCode t).testBit a
  Valid := BTree.Valid 2
  searchM a t := ⟨(btreeCode t).testBit a, 1⟩
  insertM a t := ⟨.leaf [btreeCode t ||| 2 ^ a], 1⟩
  deleteM a t := ⟨.leaf [clearBit (btreeCode t) a], 1⟩
  counted _ _ := ⟨rfl, rfl, rfl⟩

example : ¬ BTree.Contract bitsetBTree := by
  intro h
  have := h.promise.keys_empty
  revert this
  decide

end Contracts

end AlgoDesignTests
