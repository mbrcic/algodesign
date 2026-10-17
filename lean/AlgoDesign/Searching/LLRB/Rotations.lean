/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Cost

/-!
# LLRB: rotations

Rotations counted per operation. An insert rotates at most once per level of its search path
(`time_insertRot_le_height`); a delete at most three times per level of its recursion, six per
level of the 2-3 tree (`time_deleteTopRot_le_bheight`, `time_deleteTopRot_le_height`,
`time_deleteTopRot_le_log`). Unlike the standard tree, no constant bound holds. Each counting run
returns the operation's own tree, and the closed forms at the end pin its ticks to the
operation's rotations.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-! ### Rotations per insert

The standard red-black tree promises a constant: at most two rotations per insert and three per
delete (`RBTree.insert_rotations_le`, `RBTree.delete_rotations_le` in
`RedBlackStandard/Rotations.lean`). LLRB makes no such promise. Its insert runs `fixUp` at every
level of the search path on the way back up, and a split that cascades rotates at every level it
passes through. What holds is a bound by the
height: `fixUp` performs at most one rotation per call (`time_fixUpRot_le_one`), and `insertAux`
calls it once per node on the search path, so an insert rotates at most `height t` times
(`time_insertRot_le_height`), hence at most `2 ⌊lg(n+1)⌋` times on a valid tree
(`time_insertRot_le_two_log`).

The bound is attained. `AlgoDesignTests/Searching.lean` builds a valid tree of height four by
inserting 2, 6, 1, 7, 3, 5 and then inserts 4, which rotates four times: the 2-3 tree has a 3-node
root over a 3-node middle child, the new key splits both, and each of those splits costs a left
rotation and a right one. The same file states that no bound of two holds, so the constant bound
cannot be reinstated for this variant.

The count is the time of a `TimeM` run that ticks once per rotation and for nothing else, and
`ret_insertRot` says that run returns `insert`'s tree. Deletion's rotations are counted the same
way, after `delete_spec` below, whose induction the bound reuses (`time_deleteTopRot_le_height`).
-/

/-- Apply the rotation `f` when `b` holds, charging one tick if it does. -/
def rotIf (b : Bool) (f : LLRB α → LLRB α) (h : LLRB α) : TimeM ℕ (LLRB α) :=
  if b then ⟨f h, 1⟩ else ⟨h, 0⟩

omit [LinearOrder α] in
@[simp] theorem ret_rotIf (b : Bool) (f : LLRB α → LLRB α) (h : LLRB α) :
    (rotIf b f h).ret = if b then f h else h := by
  cases b <;> rfl

omit [LinearOrder α] in
@[simp] theorem time_rotIf (b : Bool) (f : LLRB α → LLRB α) (h : LLRB α) :
    (rotIf b f h).time = if b then 1 else 0 := by
  cases b <;> rfl

/-- `fixUp`, charging one tick for each rotation it performs; the color flip is free. -/
def fixUpRot (h : LLRB α) : TimeM ℕ (LLRB α) := do
  let h1 ← rotIf (h.right.isRed && !h.left.isRed) rotateLeft h
  let h2 ← rotIf (h1.left.isRed && h1.left.left.isRed) rotateRight h1
  pure (if h2.left.isRed && h2.right.isRed then flipColors h2 else h2)

/-- `insertAux`, charging only the rotations of each `fixUp` on the way back up. -/
def insertAuxRot (a : α) : LLRB α → TimeM ℕ (LLRB α)
  | leaf => pure (node .red leaf a leaf)
  | node c l k r =>
      if a < k then do
        let l' ← insertAuxRot a l
        fixUpRot (node c l' k r)
      else if k < a then do
        let r' ← insertAuxRot a r
        fixUpRot (node c l k r')
      else fixUpRot (node c l k r)

/-- `insert`, charging only rotations. Blackening the root is a recoloring and costs nothing. -/
def insertRot (a : α) (t : LLRB α) : TimeM ℕ (LLRB α) :=
  (fun t' ↦ match t' with
    | leaf => leaf
    | node _ l k r => node .black l k r) <$> insertAuxRot a t

omit [LinearOrder α] in
/-- The counting run of `fixUp` returns `fixUp`'s tree. -/
theorem ret_fixUpRot (h : LLRB α) : (fixUpRot h).ret = fixUp h := by
  simp only [fixUpRot, fixUp, ret_bind, ret_rotIf, ret_pure]

omit [LinearOrder α] in
/-- **At most one rotation per `fixUp`.** When the left rotation fires, the left child of the new
left child is the old left child, which the guard required to be black, so the right rotation
cannot fire after it. No invariant is needed. -/
theorem time_fixUpRot_le_one (h : LLRB α) : (fixUpRot h).time ≤ 1 := by
  rcases h with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩
  · simp [fixUpRot, isRed, right, LLRB.left]
  · simp only [fixUpRot, time_bind, time_rotIf, ret_rotIf, time_pure, right, isRed]
    split_ifs <;> simp_all
  · cases cr
    · cases l with
      | leaf => simp [fixUpRot, isRed, right, LLRB.left, rotateLeft]
      | node cl ll lk lr =>
        cases cl
        · simp only [fixUpRot, time_bind, time_rotIf, ret_rotIf, time_pure]
          split_ifs <;> simp_all [isRed, right, LLRB.left]
        · simp [fixUpRot, isRed, right, LLRB.left, rotateLeft]
    · simp only [fixUpRot, time_bind, time_rotIf, ret_rotIf, time_pure]
      split_ifs <;> simp_all [isRed, right, LLRB.left]

/-- The counting run of `insertAux` returns `insertAux`'s tree. -/
theorem ret_insertAuxRot (a : α) (t : LLRB α) : (insertAuxRot a t).ret = insertAux a t := by
  induction t with
  | leaf => simp [insertAuxRot, insertAux]
  | node c l k r ihl ihr =>
    simp only [insertAuxRot, insertAux]
    by_cases h : a < k
    · simp [h, ihl, ret_fixUpRot]
    · by_cases h' : k < a
      · simp [h, h', ihr, ret_fixUpRot]
      · simp [h, h', ret_fixUpRot]

/-- **The count is of `insert`'s own rotations**: the counting run returns exactly `insert`'s
tree, so its time is not the rotation count of some other procedure. -/
theorem ret_insertRot (a : α) (t : LLRB α) : (insertRot a t).ret = insert a t := by
  simp only [insertRot, ret_map, ret_insertAuxRot]
  rfl

/-- At most one rotation per node on the search path. -/
theorem time_insertAuxRot_le_height (a : α) (t : LLRB α) :
    (insertAuxRot a t).time ≤ height t := by
  induction t with
  | leaf => simp [insertAuxRot]
  | node c l k r ihl ihr =>
    simp only [insertAuxRot, height_node]
    split_ifs
    · simp only [time_bind]
      have := time_fixUpRot_le_one (node c (insertAuxRot a l).ret k r)
      have := Nat.le_max_left (height l) (height r)
      omega
    · simp only [time_bind]
      have := time_fixUpRot_le_one (node c l k (insertAuxRot a r).ret)
      have := Nat.le_max_right (height l) (height r)
      omega
    · have := time_fixUpRot_le_one (node c l k r)
      omega

/-- **An insert rotates at most `height t` times**, one rotation at most per level of the search
path. This is the LLRB's bound. It is attained, and no constant bound holds (see the section
docstring). -/
theorem time_insertRot_le_height (a : α) (t : LLRB α) : (insertRot a t).time ≤ height t := by
  simpa [insertRot] using time_insertAuxRot_le_height a t

/-- On a valid tree of `n` keys an insert rotates at most `2 ⌊lg(n+1)⌋` times. -/
theorem time_insertRot_le_two_log {t : LLRB α} (ht : Valid t) (a : α) :
    (insertRot a t).time ≤ 2 * Nat.log2 (t.size + 1) :=
  Nat.le_trans (time_insertRot_le_height a t) (height_le_two_log ht)

/-! ### Rotations per delete

Counted the way `insert`'s are (`insertRot`): `deleteRot` computes `delete`'s tree
(`ret_deleteRot`, and `ret_deleteTopRot` at the top level) and ticks once for each rotation
`delete` performs, in `moveRedLeft` (two), the preliminary `rotateRight` (one), `moveRedRight`
(one) and `fixUp` (one), and for nothing else. Each level of the recursion therefore costs at most
three rotations.

What bounds the number of levels is not the height of the tree handed to each call. `delete`
descends into a subtree it has just rotated, and on a valid tree that subtree can be as tall as
the node it came from: `moveRedLeft` can hang the old left child, of height `h - 1`, one level
lower. What does fall at every call is `levelPot`, twice the black height plus one for a red
root (`levelPot_lt`): a black node's children sit one black link lower, and a red node's children
are black at the same black height, a rule the restructuring steps keep. The induction that proves
it is `delete_spec`'s, case for case, because the facts that license each recursive call there are
exactly the ones this bound needs.

So a delete rotates at most six times per level of the 2-3 tree (`time_deleteTopRot_le_bheight`),
at most `6 * height t` times (`time_deleteTopRot_le_height`), and at most `6 ⌊lg(n+1)⌋` times on
a valid tree of `n` keys (`time_deleteTopRot_le_log`). The constant is not tight: a
measurement found at most thirteen rotations in one delete over 2000 keys, where the bound allows
about sixty. It is a bound by the height, and no constant bound holds:
`AlgoDesignTests/Searching.lean` pins a valid tree of ten keys on which one delete rotates four
times, more than the standard tree's three. -/

/-- Apply the rotation `f`, charging one tick. -/
def rot (f : LLRB α → LLRB α) (h : LLRB α) : TimeM ℕ (LLRB α) := ⟨f h, 1⟩

/-- `moveRedLeft`, charging one tick for each of its two rotations; the color flips are free. -/
def moveRedLeftRot (h : LLRB α) : TimeM ℕ (LLRB α) :=
  let h1 := flipColors h
  if h1.right.left.isRed then
    match h1 with
    | node c l k r => do
        let r' ← rot rotateRight r
        let h2 ← rot rotateLeft (node c l k r')
        pure (flipColors h2)
    | leaf => pure h1
  else pure h1

/-- `moveRedRight`, charging one tick for its rotation; the color flips are free. -/
def moveRedRightRot (h : LLRB α) : TimeM ℕ (LLRB α) :=
  let h1 := flipColors h
  if h1.left.left.isRed then do
    let h2 ← rot rotateRight h1
    pure (flipColors h2)
  else pure h1

omit [LinearOrder α] in
/-- The counting run of `moveRedLeft` returns `moveRedLeft`'s tree. -/
theorem ret_moveRedLeftRot (h : LLRB α) : (moveRedLeftRot h).ret = moveRedLeft h := by
  unfold moveRedLeftRot moveRedLeft
  dsimp only
  generalize flipColors h = h1
  cases h1 <;> split <;> rfl

omit [LinearOrder α] in
/-- The counting run of `moveRedRight` returns `moveRedRight`'s tree. -/
theorem ret_moveRedRightRot (h : LLRB α) : (moveRedRightRot h).ret = moveRedRight h := by
  unfold moveRedRightRot moveRedRight
  dsimp only
  split <;> rfl

/-- `moveRedLeft` when `b` holds, counted; otherwise the node unchanged, free. -/
def moveRedLeftIf (b : Bool) (h : LLRB α) : TimeM ℕ (LLRB α) :=
  if b then moveRedLeftRot h else pure h

/-- `moveRedRight` when `b` holds, counted; otherwise the node unchanged, free. -/
def moveRedRightIf (b : Bool) (h : LLRB α) : TimeM ℕ (LLRB α) :=
  if b then moveRedRightRot h else pure h

omit [LinearOrder α] in
theorem ret_moveRedLeftIf (b : Bool) (h : LLRB α) :
    (moveRedLeftIf b h).ret = if b then moveRedLeft h else h := by
  cases b <;> simp [moveRedLeftIf, ret_moveRedLeftRot]

omit [LinearOrder α] in
theorem ret_moveRedRightIf (b : Bool) (h : LLRB α) :
    (moveRedRightIf b h).ret = if b then moveRedRight h else h := by
  cases b <;> simp [moveRedRightIf, ret_moveRedRightRot]

/-- `deleteMin`, charging only rotations: the borrow on the way down (`moveRedLeftRot`) and the
repair on the way up (`fixUpRot`). The tree is computed exactly as `deleteMin` computes it. -/
def deleteMinRot : LLRB α → TimeM ℕ (LLRB α)
  | leaf => pure leaf
  | node _ leaf _ r => pure r
  | node c l k r =>
      match _hh : (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).ret with
      | leaf => ⟨leaf, (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).time⟩
      | node c' l' k' r' => do
          tick (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).time
          let l'' ← deleteMinRot l'
          fixUpRot (node c' l'' k' r')
termination_by t => t.size
decreasing_by
  have hsize : (node c' l' k' r').size = (node c l k r).size := by
    rw [← _hh, ret_moveRedLeftIf]
    split_ifs with h
    · exact size_moveRedLeft _
    · rfl
  simp only [size_node] at hsize ⊢
  omega

/-- `delete`, charging only rotations: `moveRedLeft`'s two, the preliminary `rotateRight`,
`moveRedRight`'s one and `fixUp`'s one, wherever `delete` performs them. The tree is computed
exactly as `delete` computes it (`ret_deleteRot`). -/
def deleteRot (a : α) : LLRB α → TimeM ℕ (LLRB α)
  | leaf => pure leaf
  | node c l k r =>
      if a < k then
        match _hh1 : (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).ret with
        | leaf => ⟨leaf, (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).time⟩
        | node c1 l1 k1 r1 => do
            tick (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).time
            let l1' ← deleteRot a l1
            fixUpRot (node c1 l1' k1 r1)
      else
        match _hh2 : (rotIf l.isRed rotateRight (node c l k r)).ret with
        | leaf => ⟨leaf, (rotIf l.isRed rotateRight (node c l k r)).time⟩
        | node c1 l1 k1 leaf => do
            tick (rotIf l.isRed rotateRight (node c l k r)).time
            if a = k1 then pure l1 else fixUpRot (node c1 l1 k1 leaf)
        | node c1 l1 k1 (node cr1 rl1 rk1 rr1) =>
            match _hh3 : (moveRedRightIf (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
                (node c1 l1 k1 (node cr1 rl1 rk1 rr1))).ret with
            | leaf => ⟨leaf, (rotIf l.isRed rotateRight (node c l k r)).time +
                (moveRedRightIf (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
                  (node c1 l1 k1 (node cr1 rl1 rk1 rr1))).time⟩
            | node c2 l2 k2 r2 => do
                tick (rotIf l.isRed rotateRight (node c l k r)).time
                tick (moveRedRightIf (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
                  (node c1 l1 k1 (node cr1 rl1 rk1 rr1))).time
                if a = k2 then
                  match r2.min? with
                  | some mn => do
                      let r2' ← deleteMinRot r2
                      fixUpRot (node c2 l2 mn r2')
                  | none => pure l2
                else do
                  let r2' ← deleteRot a r2
                  fixUpRot (node c2 l2 k2 r2')
termination_by t => t.size
decreasing_by
  · have hsize : (node c1 l1 k1 r1).size = (node c l k r).size := by
      rw [← _hh1, ret_moveRedLeftIf]
      split_ifs with h
      · exact size_moveRedLeft _
      · rfl
    simp only [size_node] at hsize ⊢
    omega
  · have hsize2 : (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).size = (node c l k r).size := by
      rw [← _hh2, ret_rotIf]
      split_ifs with h
      · exact size_rotateRight _
      · rfl
    have hsize3 : (node c2 l2 k2 r2).size = (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).size := by
      rw [← _hh3, ret_moveRedRightIf]
      split_ifs with h
      · exact size_moveRedRight _
      · rfl
    simp only [size_node] at hsize2 hsize3 ⊢
    omega

omit [LinearOrder α] in
/-- One level of `deleteMinRot` below a node with a left child. -/
theorem deleteMinRot_node {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hlne : l ≠ leaf)
    (hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
      = node c' l' k' r') :
    deleteMinRot (node c l k r) =
      (tick (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).time >>= fun _ =>
        deleteMinRot l' >>= fun l'' => fixUpRot (node c' l'' k' r')) := by
  have hh' : (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).ret
      = node c' l' k' r' := by rw [ret_moveRedLeftIf]; exact hh
  rcases l with _ | ⟨cl, ll, lk, lr⟩
  · exact absurd rfl hlne
  rw [deleteMinRot]
  · split
    · rename_i heq; exact absurd (heq.symm.trans hh') (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh'
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rfl
  · simp

omit [LinearOrder α] in
/-- One level of `deleteMin` below a node with a left child. -/
theorem deleteMin_node {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hlne : l ≠ leaf)
    (hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
      = node c' l' k' r') :
    deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩
  · exact absurd rfl hlne
  rw [deleteMin]
  · split
    · rename_i heq; exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rfl
  · simp

omit [LinearOrder α] in
/-- The counting run of `deleteMin` returns `deleteMin`'s tree. -/
theorem ret_deleteMinRot (t : LLRB α) : (deleteMinRot t).ret = deleteMin t := by
  induction t using deleteMin.induct with
  | case1 => simp [deleteMinRot, deleteMin]
  | case2 c k r => simp [deleteMinRot, deleteMin]
  | case3 c l k r hlne hh =>
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    rw [deleteMinRot_node hlne hh, deleteMin_node hlne hh]
    simp only [ret_bind, ret_fixUpRot, ih]

/-- `deleteRot` descending left, the counterpart of `delete_lt`. -/
theorem deleteRot_lt {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hak : a < k)
    (hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
            = node c' l' k' r') :
    deleteRot a (node c l k r) =
      (tick (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).time >>= fun _ =>
        deleteRot a l' >>= fun l1' => fixUpRot (node c' l1' k' r')) := by
  have hh' : (moveRedLeftIf (!l.isRed && !l.left.isRed) (node c l k r)).ret
      = node c' l' k' r' := by rw [ret_moveRedLeftIf]; exact hh
  rw [deleteRot]
  split
  case isFalse hcon => exact absurd hak hcon
  case isTrue =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh') (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh'
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rfl

/-- `deleteRot` at a node whose right child is empty after the preliminary rotation. -/
theorem deleteRot_ge_leaf {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} (hak : ¬ a < k)
    (hh : (if l.isRed then rotateRight (node c l k r) else node c l k r) = node c1 l1 k1 leaf) :
    deleteRot a (node c l k r) =
      (tick (rotIf l.isRed rotateRight (node c l k r)).time >>= fun _ =>
        if a = k1 then pure l1 else fixUpRot (node c1 l1 k1 leaf)) := by
  have hh' : (rotIf l.isRed rotateRight (node c l k r)).ret = node c1 l1 k1 leaf := by
    rw [ret_rotIf]; exact hh
  rw [deleteRot]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh') (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh'
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      rfl
    · rename_i heq
      have heq2 := heq.symm.trans hh'
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)

/-- `deleteRot` at a node whose right child is a node after the preliminary rotation. -/
theorem deleteRot_ge_node {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} {cr1 : Color} {rl1 : LLRB α} {rk1 : α} {rr1 : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hak : ¬ a < k)
    (hh2 : (if l.isRed then rotateRight (node c l k r) else node c l k r)
             = node c1 l1 k1 (node cr1 rl1 rk1 rr1))
    (hh3 : (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
              moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
            else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) = node c' l' k' r') :
    deleteRot a (node c l k r) =
      (tick (rotIf l.isRed rotateRight (node c l k r)).time >>= fun _ =>
        tick (moveRedRightIf (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
          (node c1 l1 k1 (node cr1 rl1 rk1 rr1))).time >>= fun _ =>
        if a = k' then
          match r'.min? with
          | some mn => deleteMinRot r' >>= fun r2' => fixUpRot (node c' l' mn r2')
          | none => pure l'
        else deleteRot a r' >>= fun r2' => fixUpRot (node c' l' k' r2')) := by
  have hh2' : (rotIf l.isRed rotateRight (node c l k r)).ret
      = node c1 l1 k1 (node cr1 rl1 rk1 rr1) := by rw [ret_rotIf]; exact hh2
  have hh3' : (moveRedRightIf (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
      (node c1 l1 k1 (node cr1 rl1 rk1 rr1))).ret = node c' l' k' r' := by
    rw [ret_moveRedRightIf]; exact hh3
  rw [deleteRot]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh2') (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2'
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2'
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      injection e4 with f1 f2 f3 f4
      subst f1; subst f2; subst f3; subst f4
      split
      · rename_i heq'; exact absurd (heq'.symm.trans hh3') (by simp)
      · rename_i heq'
        have heq3 := heq'.symm.trans hh3'
        injection heq3 with g1 g2 g3 g4
        subst g1; subst g2; subst g3; subst g4
        rfl

/-- **The count is of `delete`'s own rotations**: the counting run returns exactly `delete`'s
tree, so a change to `delete` that the run does not mirror breaks this theorem. -/
theorem ret_deleteRot (a : α) (t : LLRB α) : (deleteRot a t).ret = delete a t := by
  induction t using delete.induct (a := a) with
  | case1 => simp [deleteRot, delete]
  | case2 c l k r hak hh =>
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    rw [deleteRot_lt hak hh, delete_lt hak hh]
    simp only [ret_bind, ret_fixUpRot, ih]
  | case4 c l k r hak hh =>
    exfalso; revert hh; split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    rw [deleteRot_ge_leaf hak hh, delete_ge_splice hak hh]
    simp
  | case6 c l k r hak c1 l1 k1 hh hne =>
    rw [deleteRot_ge_leaf hak hh, delete_ge_fixUp hak hh hne]
    simp [hne, ret_fixUpRot]
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    exfalso; revert hh3; split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    rw [deleteRot_ge_node hak hh2 hh3, delete_ge_succ hak hh2 hh3 hmin]
    simp [hmin, ret_fixUpRot, ret_deleteMinRot]
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    rw [deleteRot_ge_node hak hh2 hh3, delete_ge_rec hak hh2 hh3 hne]
    simp [hne, ret_fixUpRot, ih]

omit [LinearOrder α] in
/-- `moveRedLeft` rotates at most twice. -/
theorem time_moveRedLeftRot_le (h : LLRB α) : (moveRedLeftRot h).time ≤ 2 := by
  unfold moveRedLeftRot
  dsimp only
  generalize flipColors h = h1
  cases h1 <;> split <;> simp [rot]

omit [LinearOrder α] in
/-- `moveRedRight` rotates at most once. -/
theorem time_moveRedRightRot_le (h : LLRB α) : (moveRedRightRot h).time ≤ 1 := by
  unfold moveRedRightRot
  dsimp only
  split <;> simp [rot]

omit [LinearOrder α] in
theorem time_moveRedLeftIf_le (b : Bool) (h : LLRB α) : (moveRedLeftIf b h).time ≤ 2 := by
  cases b
  · simp [moveRedLeftIf]
  · exact time_moveRedLeftRot_le h

omit [LinearOrder α] in
theorem time_moveRedRightIf_le (b : Bool) (h : LLRB α) : (moveRedRightIf b h).time ≤ 1 := by
  cases b
  · simp [moveRedRightIf]
  · exact time_moveRedRightRot_le h

omit [LinearOrder α] in
theorem time_rotIf_le (b : Bool) (f : LLRB α → LLRB α) (h : LLRB α) : (rotIf b f h).time ≤ 1 := by
  cases b <;> simp

/-- The potential the deletion recursion spends: twice the black height, plus one for a red root.
Every recursive call of `delete` or `deleteMin` lands on a subtree with a strictly smaller value
(`levelPot_lt`), and each level costs at most three rotations. -/
def levelPot (t : LLRB α) : ℕ := 2 * bheight t + if t.isRed then 1 else 0

omit [LinearOrder α] in
theorem levelPot_leaf : levelPot (leaf : LLRB α) = 2 := rfl

omit [LinearOrder α] in
theorem three_le_levelPot (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    3 ≤ levelPot (node c l k r) := by
  have := bheight_pos l
  cases c <;> simp [levelPot, bheight, isRed] <;> omega

omit [LinearOrder α] in
/-- The step the potential argument rests on. The recursion goes from `t` through a restructured
node `node c' l' k' r'` of the same black height, red only if `t` is, into the child `x`; if that
node is red, `x` is not. Then `x`'s potential is strictly below `t`'s. -/
theorem levelPot_lt {t x : LLRB α} {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α}
    (hbh : bheight (node c' l' k' r') = bheight t) (hx : bheight x = bheight l')
    (hred : c' = .red → ¬ x.IsRed) (hroot : c' = .red → t.IsRed) :
    levelPot x + 1 ≤ levelPot t := by
  cases c' with
  | red =>
    have hxr := isRed_eq_false (hred rfl)
    have htr : t.isRed = true := isRed_iff.mpr (hroot rfl)
    have hb : bheight l' = bheight t := by simpa [bheight] using hbh
    simp only [levelPot, hxr, htr, Bool.false_eq_true, ite_false, ite_true]
    omega
  | black =>
    have hb : bheight l' + 1 = bheight t := by simpa [bheight] using hbh
    unfold levelPot
    split <;> split <;> omega

omit [LinearOrder α] in
/-- **At most three rotations per level of `deleteMin`'s recursion**, measured by `levelPot`,
under `deleteMin_spec`'s own precondition. -/
theorem time_deleteMinRot_le {t : LLRB α} (ht_bal : Balanced t) (ht_ll : LeftLeaning t)
    (ht_nrr : NoRedRed t) (ht_ntn : NotTwoNode t) :
    (deleteMinRot t).time + 6 ≤ 3 * levelPot t := by
  induction t using deleteMin.induct with
  | case1 => simp [deleteMinRot, levelPot_leaf]
  | case2 c k r =>
    have := three_le_levelPot c leaf k r
    simp [deleteMinRot]
    omega
  | case3 c l k r hlne hh =>
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    rw [deleteMinRot_node hlne hh]
    simp only [time_bind, time_tick]
    have h1 := time_moveRedLeftIf_le (!l.isRed && !l.left.isRed) (node c l k r)
    have h2 := time_fixUpRot_le_one (node c' (deleteMinRot l').ret k' r')
    split at hh
    case isTrue hguard =>
      obtain ⟨hlnotred, hllnotred⟩ : ¬ l.IsRed ∧ ¬ l.left.IsRed := by
        have hb : l.isRed = false ∧ l.left.isRed = false := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;>
            simp_all
        exact ⟨isRed_eq_false_iff.mp hb.1, isRed_eq_false_iff.mp hb.2⟩
      have hc : c = .red := isRed_of_notTwoNode ht_ntn hlnotred
      subst hc
      rcases l with _ | ⟨cl, ll, lk, lr⟩
      · exact absurd rfl hlne
      have hcl : cl = .black := by
        rcases cl with _ | _
        · exact absurd rfl hlnotred
        · rfl
      subst hcl
      have hspec := moveRedLeft_spec (ll := ll) (lr := lr) (r := r) (k := k) (lk := lk)
        ht_ll ht_nrr ht_bal hllnotred
      rw [hh] at hspec
      obtain ⟨hl'_ll, hl'_nrr, hl'_bal, -, -, -, -, -, hcl', hbh_pres, hntn_l'⟩ := hspec
      have hih := ih hl'_bal hl'_ll hl'_nrr hntn_l'
      have hpot := levelPot_lt (x := l') hbh_pres rfl
        (fun hc => hcl' (by simp [IsRed, hc])) (fun _ => rfl)
      omega
    case isFalse hguard =>
      injection hh with hc hl hk hr
      subst hc; subst hl; subst hk; subst hr
      have hntn_l : NotTwoNode l := by
        have hb : l.isRed = true ∨ l.left.isRed = true := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;> simp_all
        rcases hb with hb | hb
        · exact Or.inl (isRed_iff.mp hb)
        · exact Or.inr (isRed_iff.mp hb)
      have hih := ih ht_bal.2.1 ht_ll.2.1 ht_nrr.2.1 hntn_l
      have hpot := levelPot_lt (t := node c l k r) (x := l) rfl rfl
        (fun hc => (ht_nrr.1 hc).1) (fun hc => by simp [IsRed, hc])
      omega

/-- **At most three rotations per level of `delete`'s recursion**, measured by `levelPot`, under
`delete_spec`'s own precondition. The induction is `delete_spec`'s, case for case: the facts that
license each recursive call there are the ones that bound it here. -/
theorem time_deleteRot_le {t : LLRB α} (a : α) :
    Sorted t → Balanced t → NoRedRed t → DeleteOk a t →
    (deleteRot a t).time + 6 ≤ 3 * levelPot t := by
  induction t using delete.induct (a := a) with
  | case1 =>
    intro _ _ _ _
    simp [deleteRot, levelPot_leaf]
  | case2 c l k r hak hh =>
    intro _ _ _ _
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    intro hs hbal hnrr hok
    have hstrict : LeftLeaning (node c l k r) ∧ NotTwoNode (node c l k r) := by
      rcases hok with hlf | h | ⟨-, -, -, -, hkey⟩
      · exact absurd hlf (by simp)
      · exact h
      · exact absurd hak (by simpa [KeyLe] using hkey)
    obtain ⟨ht_ll, ht_ntn⟩ := hstrict
    rw [deleteRot_lt hak hh]
    simp only [time_bind, time_tick]
    have h1 := time_moveRedLeftIf_le (!l.isRed && !l.left.isRed) (node c l k r)
    have h2 := time_fixUpRot_le_one (node c' (deleteRot a l').ret k' r')
    split at hh
    case isTrue hguard =>
      obtain ⟨hlnotred, hllnotred⟩ : ¬ l.IsRed ∧ ¬ l.left.IsRed := by
        have hb : l.isRed = false ∧ l.left.isRed = false := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;> simp_all
        exact ⟨isRed_eq_false_iff.mp hb.1, isRed_eq_false_iff.mp hb.2⟩
      have hc : c = Color.red := isRed_of_notTwoNode ht_ntn hlnotred
      subst hc
      rcases l with _ | ⟨cl, ll, lk, lr⟩
      · have hrleaf : r = leaf := by
          rcases r with _ | ⟨cr, rl, rk, rr⟩
          · rfl
          · exfalso
            have hcr : cr = Color.black := by
              cases cr with
              | red => exact absurd (show (node Color.red rl rk rr).IsRed from rfl) ht_ll.1
              | black => rfl
            subst hcr
            have := bheight_pos rl
            have h1 : bheight (leaf : LLRB α) = bheight (node Color.black rl rk rr) := hbal.1
            simp [bheight] at h1
            omega
        subst hrleaf
        have hml : moveRedLeft (node Color.red (leaf : LLRB α) k leaf)
            = node Color.red leaf k leaf := by
          simp [moveRedLeft, flipColors, left, right, isRed]
        rw [hml] at hh
        injection hh with e1 e2 e3 e4
        subst e1; subst e2; subst e3; subst e4
        have h0 : (deleteRot a (leaf : LLRB α)).time = 0 := by simp [deleteRot]
        have h3 : levelPot (node Color.red (leaf : LLRB α) k leaf) = 3 := rfl
        omega
      have hcl : cl = Color.black := by
        cases cl with
        | red => exact absurd (show (node Color.red ll lk lr).IsRed from rfl) hlnotred
        | black => rfl
      subst hcl
      have hspec := moveRedLeft_spec (ll := ll) (lr := lr) (r := r) (k := k) (lk := lk)
        ht_ll hnrr hbal hllnotred
      rw [hh] at hspec
      obtain ⟨hl'_ll, hl'_nrr, hl'_bal, -, -, -, -, -, hcl', hbh_pres, hntn_l'⟩ := hspec
      have hs' : Sorted (node c' l' k' r') := by rw [← hh]; exact sorted_moveRedLeft hs
      have hih := ih hs'.2.2.1 hl'_bal hl'_nrr (Or.inr (Or.inl ⟨hl'_ll, hntn_l'⟩))
      have hpot := levelPot_lt (x := l') hbh_pres rfl
        (fun hc => hcl' (by simp [IsRed, hc])) (fun _ => rfl)
      omega
    case isFalse hguard =>
      injection hh with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      have hntn_l : NotTwoNode l := by
        have hb : l.isRed = true ∨ l.left.isRed = true := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;> simp_all
        rcases hb with hb | hb
        · exact Or.inl (isRed_iff.mp hb)
        · exact Or.inr (isRed_iff.mp hb)
      have hih := ih hs.2.2.1 hbal.2.1 hnrr.2.1 (Or.inr (Or.inl ⟨ht_ll.2.1, hntn_l⟩))
      have hpot := levelPot_lt (t := node c l k r) (x := l) rfl rfl
        (fun hc => (hnrr.1 hc).1) (fun hc => by simp [IsRed, hc])
      omega
  | case4 c l k r hak hh =>
    intro _ _ _ _
    exfalso; revert hh; split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    intro _ _ _ _
    rw [deleteRot_ge_leaf hak hh]
    have h1 := time_rotIf_le l.isRed rotateRight (node c l k r)
    have h3 := three_le_levelPot c l k r
    simp only [time_bind, time_tick, ↓reduceIte, time_pure]
    omega
  | case6 c l k r hak c1 l1 k1 hh hne =>
    intro _ _ _ _
    rw [deleteRot_ge_leaf hak hh]
    have h1 := time_rotIf_le l.isRed rotateRight (node c l k r)
    have h2 := time_fixUpRot_le_one (node c1 l1 k1 leaf)
    have h3 := three_le_levelPot c l k r
    simp only [time_bind, time_tick, hne, ↓reduceIte]
    omega
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    intro _ _ _ _
    exfalso; revert hh3; split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    intro hs hbal hnrr hok
    obtain ⟨hbh1, hbal1, hnrr1, hs1, hll1, hllr1, hak1, hl1nr, hred1, hisred1⟩ :=
      rotateRight_guard_spec hs hbal hnrr hok hak hh2
    obtain ⟨hbh2, hbal2, hnrr2, hs2, hll2, hc2, hisred2, hl2red, hdisj⟩ :=
      moveRedRight_guard_spec hs1 hbal1 hnrr1 hll1 hllr1 hak1 hl1nr hred1 hh3
    obtain ⟨hllr2, hntn2⟩ : LeftLeaning r' ∧ NotTwoNode r' := by
      rcases hdisj with h | ⟨-, hk⟩
      · exact h
      · exact absurd hk (by simpa using hak1)
    have hdm := time_deleteMinRot_le hbal2.2.2 hllr2 hnrr2.2.2 hntn2
    rw [deleteRot_ge_node hak hh2 hh3]
    have h1 := time_rotIf_le l.isRed rotateRight (node c l k r)
    have h2 := time_moveRedRightIf_le (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
      (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
    have h3 := time_fixUpRot_le_one (node c' l' m (deleteMinRot r').ret)
    have hpot := levelPot_lt (t := node c l k r) (x := r') (hbh2.trans hbh1) hbal2.1.symm
      (fun hc => (hc2 hc).2) (fun hc => hisred1 (hisred2 (by simp [IsRed, hc])))
    simp only [time_bind, time_tick, ↓reduceIte, hmin]
    omega
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    intro _ _ _ _
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    intro hs hbal hnrr hok
    obtain ⟨hbh1, hbal1, hnrr1, hs1, hll1, hllr1, hak1, hl1nr, hred1, hisred1⟩ :=
      rotateRight_guard_spec hs hbal hnrr hok hak hh2
    obtain ⟨hbh2, hbal2, hnrr2, hs2, hll2, hc2, hisred2, hl2red, hdisj⟩ :=
      moveRedRight_guard_spec hs1 hbal1 hnrr1 hll1 hllr1 hak1 hl1nr hred1 hh3
    have hok2 : DeleteOk a r' := by
      rcases hdisj with h | ⟨h, -⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hih := ih hs2.2.2.2 hbal2.2.2 hnrr2.2.2 hok2
    rw [deleteRot_ge_node hak hh2 hh3]
    have h1 := time_rotIf_le l.isRed rotateRight (node c l k r)
    have h2 := time_moveRedRightIf_le (!(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed)
      (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
    have h3 := time_fixUpRot_le_one (node c' l' k' (deleteRot a r').ret)
    have hpot := levelPot_lt (t := node c l k r) (x := r') (hbh2.trans hbh1) hbal2.1.symm
      (fun hc => (hc2 hc).2) (fun hc => hisred1 (hisred2 (by simp [IsRed, hc])))
    simp only [time_bind, time_tick, hne, ↓reduceIte]
    omega

/-- `deleteMinTop`, charging only rotations. -/
def deleteMinTopRot (t : LLRB α) : TimeM ℕ (LLRB α) := blacken <$> deleteMinRot (prime t)

/-- `deleteTop`, charging only rotations. -/
def deleteTopRot (a : α) (t : LLRB α) : TimeM ℕ (LLRB α) :=
  if search a t then blacken <$> deleteRot a (prime t) else pure t

omit [LinearOrder α] in
/-- The counting run of `deleteMinTop` returns `deleteMinTop`'s tree. -/
theorem ret_deleteMinTopRot (t : LLRB α) : (deleteMinTopRot t).ret = deleteMinTop t := by
  simp only [deleteMinTopRot, deleteMinTop, ret_map, ret_deleteMinRot]

/-- The counting run of `deleteTop` returns `deleteTop`'s tree. -/
theorem ret_deleteTopRot (a : α) (t : LLRB α) : (deleteTopRot a t).ret = deleteTop a t := by
  simp only [deleteTopRot, deleteTop]
  split <;> simp [ret_deleteRot]

omit [LinearOrder α] in
/-- Priming a black-rooted tree does not raise the potential above twice its black height. -/
theorem levelPot_prime_le {t : LLRB α} (h : RootBlack t) : levelPot (prime t) ≤ 2 * bheight t := by
  cases t with
  | leaf => simp [prime, levelPot, bheight, isRed]
  | node c l k r =>
    have hc : c = .black := h
    subst hc
    simp only [prime]
    split
    · exact (by omega : 2 * bheight l + 1 ≤ 2 * (bheight l + 1))
    · exact (by omega : 2 * (bheight l + 1) + 0 ≤ 2 * (bheight l + 1))

omit [LinearOrder α] in
/-- The black links below the root lie on one root-to-leaf path. -/
theorem bheight_sub_one_le_height (t : LLRB α) : bheight t - 1 ≤ height t := by
  induction t with
  | leaf => simp [bheight]
  | node c l k r ihl _ =>
    simp only [bheight, height_node]
    have := Nat.le_max_left (height l) (height r)
    split <;> omega

/-- **A delete rotates at most six times per level of the 2-3 tree** (`bheight t - 1` is that
tree's height): three per LLRB level, and a 2-3 level is at most two LLRB levels. -/
theorem time_deleteTopRot_le_bheight {t : LLRB α} (hv : Valid t) (a : α) :
    (deleteTopRot a t).time ≤ 6 * (bheight t - 1) := by
  obtain ⟨hs, hrb, hll, hnrr, hbh⟩ := hv
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  have hpos := bheight_pos t
  simp only [deleteTopRot]
  split
  case isFalse => simp
  by_cases hne : t = leaf
  · subst hne
    simp [prime, deleteRot]
  · obtain ⟨hpb, hpl, hpn, hpt⟩ := prime_spec hne hbal hll hnrr
    have h := time_deleteRot_le a (sorted_prime hs) hpb hpn (Or.inr (Or.inl ⟨hpl, hpt⟩))
    have hp := levelPot_prime_le hrb
    simp only [time_map]
    omega

/-- The same bound for `deleteMinTop`. -/
theorem time_deleteMinTopRot_le_bheight {t : LLRB α} (hv : Valid t) :
    (deleteMinTopRot t).time ≤ 6 * (bheight t - 1) := by
  obtain ⟨-, hrb, hll, hnrr, hbh⟩ := hv
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  have hpos := bheight_pos t
  simp only [deleteMinTopRot, time_map]
  by_cases hne : t = leaf
  · subst hne
    simp [prime, deleteMinRot]
  · obtain ⟨hpb, hpl, hpn, hpt⟩ := prime_spec hne hbal hll hnrr
    have h := time_deleteMinRot_le hpb hpl hpn hpt
    have hp := levelPot_prime_le hrb
    omega

/-- **A delete rotates at most `6 * height t` times.** No constant bound holds;
`AlgoDesignTests/Searching.lean` pins a valid tree on which one delete rotates four times. -/
theorem time_deleteTopRot_le_height {t : LLRB α} (hv : Valid t) (a : α) :
    (deleteTopRot a t).time ≤ 6 * height t :=
  Nat.le_trans (time_deleteTopRot_le_bheight hv a)
    (Nat.mul_le_mul_left 6 (bheight_sub_one_le_height t))

/-- The 2-3 height of a valid tree is at most `⌊lg(n+1)⌋`. -/
theorem bheight_sub_one_le_log {t : LLRB α} (hv : Valid t) :
    bheight t - 1 ≤ Nat.log2 (t.size + 1) :=
  (Nat.le_log2 (Nat.succ_ne_zero _)).mpr
    (two_pow_bheight_le_size_succ (blackHeightOk_iff_balanced.mp hv.2.2.2.2))

/-- On a valid tree of `n` keys a delete rotates at most `6 ⌊lg(n+1)⌋` times. -/
theorem time_deleteTopRot_le_log {t : LLRB α} (hv : Valid t) (a : α) :
    (deleteTopRot a t).time ≤ 6 * Nat.log2 (t.size + 1) :=
  Nat.le_trans (time_deleteTopRot_le_bheight hv a)
    (Nat.mul_le_mul_left 6 (bheight_sub_one_le_log hv))

/-! ### The count in closed form

`deleteRot` is a transcription of `delete` with ticks added, and `ret_deleteRot` pins its *tree* to
`delete`'s, but not its *ticks* to `delete`'s rotations: a run that forgot to charge one rotation
would still return the right tree. The counts below are written from `delete`'s own branches and
trees, with the rotation each site performs read off that site's guard — two for a `moveRedLeft`
whose guard fires (`moveRedLeftRotations`), one for the preliminary `rotateRight`, one for a
`moveRedRight` whose guard fires (`moveRedRightRotations`), and `fixUp`'s own two guards
(`fixUpRotations`) — and `time_deleteRot`, `time_deleteMinRot`, `time_deleteTopRot` and
`time_deleteMinTopRot` prove the runs' time equal to them. Dropping or adding a tick at any site of
a run breaks one of those proofs, which is what makes the bounds above bounds on `delete`'s
rotations rather than on a lookalike's. `AlgoDesignTests/Searching.lean` pins, for every site but
one, a small tree on which that site rotates. The exception is the `fixUp` after an empty right
child (`delete`'s `a ≠ k1` arm): it never rotates, since reaching it needs a left child that is not
red, so no test can see its tick; only `time_deleteRot` does. -/

/-- The rotations `fixUp` performs, read off its two guards. -/
def fixUpRotations (h : LLRB α) : ℕ :=
  (if h.right.isRed && !h.left.isRed then 1 else 0) +
    (if (if h.right.isRed && !h.left.isRed then rotateLeft h else h).left.isRed &&
        (if h.right.isRed && !h.left.isRed then rotateLeft h else h).left.left.isRed then 1
     else 0)

/-- The rotations `moveRedLeft` performs: two when its guard fires, none otherwise. -/
def moveRedLeftRotations (h : LLRB α) : ℕ :=
  if (flipColors h).right.left.isRed then 2 else 0

/-- The rotations `moveRedRight` performs: one when its guard fires, none otherwise. -/
def moveRedRightRotations (h : LLRB α) : ℕ :=
  if (flipColors h).left.left.isRed then 1 else 0

omit [LinearOrder α] in
theorem time_fixUpRot (h : LLRB α) : (fixUpRot h).time = fixUpRotations h := by
  simp only [fixUpRot, fixUpRotations, time_bind, time_rotIf, ret_rotIf, time_pure]
  omega

omit [LinearOrder α] in
theorem time_moveRedLeftRot (h : LLRB α) :
    (moveRedLeftRot h).time = moveRedLeftRotations h := by
  unfold moveRedLeftRot moveRedLeftRotations
  dsimp only
  generalize flipColors h = h1
  cases h1 <;> split <;> simp_all [rot, right, LLRB.left, isRed]

omit [LinearOrder α] in
theorem time_moveRedRightRot (h : LLRB α) :
    (moveRedRightRot h).time = moveRedRightRotations h := by
  unfold moveRedRightRot moveRedRightRotations
  dsimp only
  split <;> simp_all [rot]

omit [LinearOrder α] in
theorem time_moveRedLeftIf (b : Bool) (h : LLRB α) :
    (moveRedLeftIf b h).time = if b then moveRedLeftRotations h else 0 := by
  cases b <;> simp [moveRedLeftIf, time_moveRedLeftRot]

omit [LinearOrder α] in
theorem time_moveRedRightIf (b : Bool) (h : LLRB α) :
    (moveRedRightIf b h).time = if b then moveRedRightRotations h else 0 := by
  cases b <;> simp [moveRedRightIf, time_moveRedRightRot]

/-- `deleteMin`'s rotations in closed form, following `deleteMin`'s own branches and trees. -/
def deleteMinRotations : LLRB α → ℕ
  | leaf => 0
  | node _ leaf _ _ => 0
  | node c l k r =>
      match _hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
      with
      | leaf => if !l.isRed && !l.left.isRed then moveRedLeftRotations (node c l k r) else 0
      | node c' l' k' r' =>
          (if !l.isRed && !l.left.isRed then moveRedLeftRotations (node c l k r) else 0) +
            deleteMinRotations l' + fixUpRotations (node c' (deleteMin l') k' r')
termination_by t => t.size
decreasing_by
  have hsize : (node c' l' k' r').size = (node c l k r).size := by
    rw [← _hh]
    split_ifs with h
    · exact size_moveRedLeft _
    · rfl
  simp only [size_node] at hsize ⊢
  omega

omit [LinearOrder α] in
theorem deleteMinRotations_node {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hlne : l ≠ leaf)
    (hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
      = node c' l' k' r') :
    deleteMinRotations (node c l k r) =
      (if !l.isRed && !l.left.isRed then moveRedLeftRotations (node c l k r) else 0) +
        deleteMinRotations l' + fixUpRotations (node c' (deleteMin l') k' r') := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩
  · exact absurd rfl hlne
  rw [deleteMinRotations]
  · split
    · rename_i heq; exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rfl
  · simp

omit [LinearOrder α] in
theorem time_deleteMinRot (t : LLRB α) : (deleteMinRot t).time = deleteMinRotations t := by
  induction t using deleteMin.induct with
  | case1 => simp [deleteMinRot, deleteMinRotations]
  | case2 c k r => simp [deleteMinRot, deleteMinRotations]
  | case3 c l k r hlne hh =>
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    rw [deleteMinRot_node hlne hh, deleteMinRotations_node hlne hh]
    simp only [time_bind, time_tick, time_fixUpRot, ret_deleteMinRot, ih, time_moveRedLeftIf]
    omega

/-- `delete`'s rotations in closed form, following `delete`'s own branches and trees: two for a
`moveRedLeft` whose guard fires, one for the preliminary `rotateRight`, one for a `moveRedRight`
whose guard fires, and `fixUp`'s on the way back up. -/
def deleteRotations (a : α) : LLRB α → ℕ
  | leaf => 0
  | node c l k r =>
      if a < k then
        match _hh1 :
            (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r) with
        | leaf => if !l.isRed && !l.left.isRed then moveRedLeftRotations (node c l k r) else 0
        | node c1 l1 k1 r1 =>
            (if !l.isRed && !l.left.isRed then moveRedLeftRotations (node c l k r) else 0) +
              deleteRotations a l1 + fixUpRotations (node c1 (delete a l1) k1 r1)
      else
        match _hh2 : (if l.isRed then rotateRight (node c l k r) else node c l k r) with
        | leaf => if l.isRed then 1 else 0
        | node c1 l1 k1 leaf =>
            (if l.isRed then 1 else 0) +
              if a = k1 then 0 else fixUpRotations (node c1 l1 k1 leaf)
        | node c1 l1 k1 (node cr1 rl1 rk1 rr1) =>
            match _hh3 :
                (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
                    moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
                  else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) with
            | leaf =>
                (if l.isRed then 1 else 0) +
                  if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
                    moveRedRightRotations (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
                  else 0
            | node c2 l2 k2 r2 =>
                (if l.isRed then 1 else 0) +
                  (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
                    moveRedRightRotations (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
                  else 0) +
                  if a = k2 then
                    match r2.min? with
                    | some mn =>
                        deleteMinRotations r2 + fixUpRotations (node c2 l2 mn (deleteMin r2))
                    | none => 0
                  else deleteRotations a r2 + fixUpRotations (node c2 l2 k2 (delete a r2))
termination_by t => t.size
decreasing_by
  · have hsize : (node c1 l1 k1 r1).size = (node c l k r).size := by
      rw [← _hh1]
      split_ifs with h
      · exact size_moveRedLeft _
      · rfl
    simp only [size_node] at hsize ⊢
    omega
  · have hsize2 : (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).size = (node c l k r).size := by
      rw [← _hh2]
      split_ifs with h
      · exact size_rotateRight _
      · rfl
    have hsize3 : (node c2 l2 k2 r2).size = (node c1 l1 k1 (node cr1 rl1 rk1 rr1)).size := by
      rw [← _hh3]
      split_ifs with h
      · exact size_moveRedRight _
      · rfl
    simp only [size_node] at hsize2 hsize3 ⊢
    omega

theorem deleteRotations_lt {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hak : a < k)
    (hh : (if !l.isRed && !l.left.isRed then moveRedLeft (node c l k r) else node c l k r)
            = node c' l' k' r') :
    deleteRotations a (node c l k r) =
      (if !l.isRed && !l.left.isRed then moveRedLeftRotations (node c l k r) else 0) +
        deleteRotations a l' + fixUpRotations (node c' (delete a l') k' r') := by
  rw [deleteRotations]
  split
  case isFalse hcon => exact absurd hak hcon
  case isTrue =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rfl

theorem deleteRotations_ge_leaf {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} (hak : ¬ a < k)
    (hh : (if l.isRed then rotateRight (node c l k r) else node c l k r) = node c1 l1 k1 leaf) :
    deleteRotations a (node c l k r) =
      (if l.isRed then 1 else 0) + if a = k1 then 0 else fixUpRotations (node c1 l1 k1 leaf) := by
  rw [deleteRotations]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      rfl
    · rename_i heq
      have heq2 := heq.symm.trans hh
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)

theorem deleteRotations_ge_node {a : α} {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    {c1 : Color} {l1 : LLRB α} {k1 : α} {cr1 : Color} {rl1 : LLRB α} {rk1 : α} {rr1 : LLRB α}
    {c' : Color} {l' : LLRB α} {k' : α} {r' : LLRB α} (hak : ¬ a < k)
    (hh2 : (if l.isRed then rotateRight (node c l k r) else node c l k r)
             = node c1 l1 k1 (node cr1 rl1 rk1 rr1))
    (hh3 : (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
              moveRedRight (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
            else node c1 l1 k1 (node cr1 rl1 rk1 rr1)) = node c' l' k' r') :
    deleteRotations a (node c l k r) =
      (if l.isRed then 1 else 0) +
        (if !(node cr1 rl1 rk1 rr1).isRed && !rl1.isRed then
          moveRedRightRotations (node c1 l1 k1 (node cr1 rl1 rk1 rr1))
        else 0) +
        if a = k' then
          match r'.min? with
          | some mn => deleteMinRotations r' + fixUpRotations (node c' l' mn (deleteMin r'))
          | none => 0
        else deleteRotations a r' + fixUpRotations (node c' l' k' (delete a r')) := by
  rw [deleteRotations]
  split
  case isTrue h => exact absurd h hak
  case isFalse =>
    split
    · rename_i heq; exact absurd (heq.symm.trans hh2) (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2
      injection heq2 with e1 e2 e3 e4
      exact absurd e4 (by simp)
    · rename_i heq
      have heq2 := heq.symm.trans hh2
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3
      injection e4 with f1 f2 f3 f4
      subst f1; subst f2; subst f3; subst f4
      split
      · rename_i heq'; exact absurd (heq'.symm.trans hh3) (by simp)
      · rename_i heq'
        have heq3 := heq'.symm.trans hh3
        injection heq3 with g1 g2 g3 g4
        subst g1; subst g2; subst g3; subst g4
        rfl

/-- **Every rotation `deleteRot` charges is one `delete` performs, and conversely**: the run's time
is the closed-form count read off `delete`'s own branches. Removing a tick from any site of the
run, or adding one, breaks this theorem. -/
theorem time_deleteRot (a : α) (t : LLRB α) : (deleteRot a t).time = deleteRotations a t := by
  induction t using delete.induct (a := a) with
  | case1 => simp [deleteRot, deleteRotations]
  | case2 c l k r hak hh =>
    exfalso; revert hh; split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case3 c l k r hak c' l' k' r' hh ih =>
    rw [deleteRot_lt hak hh, deleteRotations_lt hak hh]
    simp only [time_bind, time_tick, time_fixUpRot, ret_deleteRot, ih, time_moveRedLeftIf]
    omega
  | case4 c l k r hak hh =>
    exfalso; revert hh; split
    · simp [rotateRight_eq_leaf_iff]
    · simp
  | case5 c l k r hak c1 l1 hh =>
    rw [deleteRot_ge_leaf hak hh, deleteRotations_ge_leaf hak hh]
    simp
  | case6 c l k r hak c1 l1 k1 hh hne =>
    rw [deleteRot_ge_leaf hak hh, deleteRotations_ge_leaf hak hh]
    simp [hne, time_fixUpRot]
  | case7 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 hh3 =>
    exfalso; revert hh3; split
    · simp [moveRedRight_eq_leaf_iff]
    · simp
  | case8 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' m hmin hh3 =>
    rw [deleteRot_ge_node hak hh2 hh3, deleteRotations_ge_node hak hh2 hh3]
    simp [hmin, time_fixUpRot, ret_deleteMinRot, time_deleteMinRot, time_moveRedRightIf]
    omega
  | case9 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' r' hmin hh3 =>
    exact absurd (min?_eq_none_iff.mp hmin) (ite_moveRedRight_right_ne_leaf hh3)
  | case10 c l k r hak c1 l1 k1 cr1 rl1 rk1 rr1 hh2 c' l' k' r' hh3 hne ih =>
    rw [deleteRot_ge_node hak hh2 hh3, deleteRotations_ge_node hak hh2 hh3]
    simp [hne, time_fixUpRot, ret_deleteRot, ih, time_moveRedRightIf]
    omega

/-- `deleteTop`'s rotations in closed form: `delete`'s, on the primed tree, when the key is
present; none otherwise. -/
def deleteTopRotations (a : α) (t : LLRB α) : ℕ :=
  if search a t then deleteRotations a (prime t) else 0

/-- `deleteMinTop`'s rotations in closed form. -/
def deleteMinTopRotations (t : LLRB α) : ℕ := deleteMinRotations (prime t)

theorem time_deleteTopRot (a : α) (t : LLRB α) :
    (deleteTopRot a t).time = deleteTopRotations a t := by
  simp only [deleteTopRot, deleteTopRotations]
  split <;> simp [time_deleteRot]

omit [LinearOrder α] in
theorem time_deleteMinTopRot (t : LLRB α) :
    (deleteMinTopRot t).time = deleteMinTopRotations t := by
  simp [deleteMinTopRot, deleteMinTopRotations, time_deleteMinRot]

end LLRB

end AlgoDesign.Searching
