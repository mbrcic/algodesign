/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Insert

/-!
# Red-black tree: deletion

CLRS's `RB-DELETE` and `RB-DELETE-FIXUP` (`del`, `delMin`, `deleteFixupL`/`deleteFixupR`):
`mem_delete` (an iff: exactly the key removed), `sorted_delete`, `valid_delete`, and
`deleteSpec`: `delete` discharges `DeleteSpec`.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RBTree

variable {α : Type}
variable [LinearOrder α]

/-! ### `delete` + `RB-DELETE-FIXUP`

CLRS's "extra blackness" device: when a black node is spliced out (or recolored away) during an
ordinary BST delete, whatever took its place is one black node *short* relative to its sibling --
CLRS represents this by (temporarily) letting a node be "doubly black." `Color` has no room for a
third case (it's fixed at exactly `red`/`black`, same restriction `insert`'s fixups work under),
so here the deficiency is tracked the same way `insert`'s residual violation is: as a plain `Bool`
returned alongside the rebuilt tree, propagated up the recursion exactly like CLRS's `x := x.p`
loop restart, and consumed by `deleteFixupL`/`deleteFixupR` (the recursive-return analogues of one
`RB-DELETE-FIXUP` loop iteration, in the same style as `insertFixupL`/`insertFixupR`). -/

omit [LinearOrder α] in
/-- Shared by `deleteFixupL` (called with `s := w`, `c' := c`) and by `Case 1`'s fall-through
(called with `s := w.left`, `c' := .red`): `RB-DELETE-FIXUP`'s `Case 2`/`3`/`4`, run against a
sibling `s` already known black-rooted-or-`leaf` (`Case 1`'s own rotate-and-recolor step is handled
by `deleteFixupL` itself, before this is reached). Pulled out to a top-level `def` so it has its own
name to state `Mem`/`Sorted`-preservation lemmas against, instead of being buried in a local `let`.
See `deleteFixupL`'s docstring for what each case does. -/
def deleteFixupCase234L (c' : Color) (x : RBTree α) (k : α) (s : RBTree α) : RBTree α × Bool :=
  match s with
  | leaf => (node c' x k leaf, false)
  | node _ sl sk sr =>
      if !sl.isRed && !sr.isRed then
        (node .black x k (node .red sl sk sr), c' = .black)
      else
        -- Case 3 (`sl` red, `sr` black) rotates `s` into `Case 4`'s shape first; Case 4 direct
        -- (`sr` already red) leaves `s` alone.
        let s' := if sr.isRed then s else rotateRight (node .red (blacken sl) sk sr)
        match s' with
        | node _ s'l s'k s'r =>
            (rotateLeft (node .black x k (node c' s'l s'k (blacken s'r))), false)
        | leaf => (node c' x k leaf, false)

omit [LinearOrder α] in
/-- One step of `RB-DELETE-FIXUP`'s loop body when the deficient node is the **left** child: `x`
carries a black-height deficit of exactly one, tracked by the caller's `Bool` (see this section's
docstring). `c`/`k`/`w` are this node's own (untouched) color/key/**sibling**. Returns the rebuilt
subtree and whether the deficiency survives one level further up.

CLRS's four cases, cascading (`Case 1` always falls through into `Case 2`/`3`/`4` within this same
call, never needing a second pass at this level):
* **Case 1** (sibling `w` red): recolor and `LEFT-ROTATE` to convert to a black-sibling case, then
  immediately fall through to `Case 2`/`3`/`4` on the rotated structure -- always ends up resolved.
* **Case 2** (`w` black, both children black): recolor `w` red, pushing the deficiency up to this
  node's own color (resolved here if `c` was red -- the node ends up black either way, since a red
  `c` gets forced black exactly where CLRS's final unconditional `x.color = BLACK` would fire).
* **Case 3** (`w` black, `w.left` red, `w.right` black -- a "triangle"): `RIGHT-ROTATE` at `w` to
  turn it into `Case 4`'s shape.
* **Case 4** (`w` black, `w.right` red -- a "line"): recolor and `LEFT-ROTATE` at this node --
  always resolves the deficiency. -/
def deleteFixupL (c : Color) (x : RBTree α) (k : α) (w : RBTree α) : RBTree α × Bool :=
  match w with
  | node .red wl wk wr =>
      (node .black (deleteFixupCase234L .red x k wl).1 wk wr, false)
  | _ => deleteFixupCase234L c x k w

omit [LinearOrder α] in
/-- Mirror of `deleteFixupCase234L` for the right-child (sibling on the left) orientation. -/
def deleteFixupCase234R (c' : Color) (k : α) (x s : RBTree α) : RBTree α × Bool :=
  match s with
  | leaf => (node c' leaf k x, false)
  | node _ sl sk sr =>
      if !sl.isRed && !sr.isRed then
        (node .black (node .red sl sk sr) k x, c' = .black)
      else
        -- Case 3 (`sr` red, `sl` black) rotates `s` into `Case 4`'s shape first; Case 4 direct
        -- (`sl` already red) leaves `s` alone.
        let s' := if sl.isRed then s else rotateLeft (node .red sl sk (blacken sr))
        match s' with
        | node _ s'l s'k s'r =>
            (rotateRight (node .black (node c' (blacken s'l) s'k s'r) k x), false)
        | leaf => (node c' leaf k x, false)

omit [LinearOrder α] in
/-- Symmetric to `deleteFixupL`, for a deficiency on the **right** child (sibling `w` is now the
*left* child; `LEFT-ROTATE`/`RIGHT-ROTATE` and "left"/"right" child roles swap throughout). -/
def deleteFixupR (c : Color) (w : RBTree α) (k : α) (x : RBTree α) : RBTree α × Bool :=
  match w with
  | node .red wl wk wr =>
      (node .black wl wk (deleteFixupCase234R .red k x wr).1, false)
  | _ => deleteFixupCase234R c k x w

omit [LinearOrder α] in
/-- Delete the minimum key from a non-empty tree (given pre-destructured, to stay total without
needing `[Inhabited α]` for a leaf case that can't actually occur -- same trick `insertFixupL`'s
match uses). Returns the rebuilt tree, whether it is now one black node short (CLRS's "extra
black"), and the removed minimum key itself (needed by `del`'s two-children case, which moves this
key up in place of the deleted node -- CLRS's in-order-successor splice).

The base case (`l = leaf`, so `k` itself is the minimum) mirrors CLRS's `RB-TRANSPLANT`: splicing
`node c leaf k r` out and replacing it with `r`.
* `c` red: property 4 forces `r = leaf` too (a red node's children are black; a black `leaf` child
  balancing a black `leaf` sibling position leaves no room for a non-leaf other side) -- removing a
  red node never changes black-height, no deficiency.
* `c` black, `r = leaf`: nothing to replace the removed black node with -- genuine deficiency.
* `c` black, `r` a node: property 4 again forces `r` red with `leaf` children -- recolor it black
  (`blacken`) to occupy exactly the black slot `c` vacated; no deficiency. -/
def delMin (c : Color) (l : RBTree α) (k : α) (r : RBTree α) : RBTree α × Bool × α :=
  match l with
  | leaf =>
      match c, r with
      | .red, _ => (r, false, k)
      | .black, leaf => (leaf, true, k)
      | .black, node _ rl rk rr => (node .black rl rk rr, false, k)
  | node cl ll lk lr =>
      let (l', deficient, m) := delMin cl ll lk lr
      if deficient then
        let (t', d') := deleteFixupL c l' k r
        (t', d', m)
      else (node c l' k r, false, m)

/-- Ordinary BST delete of `a`, tracking the black-height deficiency on the way back up exactly the
way `ins` tracks a residual red-red violation. A missing key is a no-op, same as `BST.delete`. The
two-children case follows CLRS's `RB-DELETE`: move the in-order successor (`delMin` of the right
subtree) up in `a`'s place, and treat the resulting deficiency (if any) as coming from the right. -/
def del (a : α) : RBTree α → RBTree α × Bool
  | leaf => (leaf, false)
  | node c l k r =>
      if a < k then
        let (l', deficient) := del a l
        if deficient then deleteFixupL c l' k r else (node c l' k r, false)
      else if k < a then
        let (r', deficient) := del a r
        if deficient then deleteFixupR c l k r' else (node c l k r', false)
      else
        match l with
        | leaf =>
            match c, r with
            | .red, _ => (r, false)
            | .black, leaf => (leaf, true)
            | .black, node _ rl rk rr => (node .black rl rk rr, false)
        | node cl ll lk lr =>
            match r with
            | leaf =>
                match c with
                | .red => (l, false)
                | .black => (node .black ll lk lr, false)
            | node cr rl rk rr =>
                let (r', deficient, m) := delMin cr rl rk rr
                if deficient then deleteFixupR c l m r'
                else (node c (node cl ll lk lr) m r', false)

/-- `delete`, discarding the top-level deficiency flag: if the deficiency survives all the way to
the true root, that's not an error -- unlike a residual red-red violation (which `insert` must
still force away with a final `blacken`, since a red *root* would violate `RootBlack`), a root that
ends up with a strictly smaller black-height than before is a perfectly ordinary valid tree, with
nothing above it to compare against. This matches CLRS's own `RB-DELETE`, which has no unconditional
recoloring step at the end (unlike `RB-INSERT`'s `T.root.color = BLACK`). -/
def delete (a : α) (t : RBTree α) : RBTree α := (del a t).1

omit [LinearOrder α] in
/-- `rotateLeft` applied to an already-non-`leaf` tree is again non-`leaf` -- lets downstream
proofs case on the *shape* of a `rotateLeft` result (`leaf` vs `node`) without needing to know
anything about the specific tree being rotated (in particular, without case-bashing on `rx`). -/
theorem exists_node_rotateLeft {cx : Color} {lx : RBTree α} {kx : α} {rx : RBTree α} :
    ∃ c' l' k' r', rotateLeft (node cx lx kx rx) = node c' l' k' r' := by
  cases rx with
  | leaf => exact ⟨cx, lx, kx, leaf, rfl⟩
  | node cy ly ky ry => exact ⟨cy, node cx lx kx ly, ky, ry, rfl⟩

omit [LinearOrder α] in
/-- Symmetric to `exists_node_rotateLeft`. -/
theorem exists_node_rotateRight {cx : Color} {lx : RBTree α} {kx : α} {rx : RBTree α} :
    ∃ c' l' k' r', rotateRight (node cx lx kx rx) = node c' l' k' r' := by
  cases lx with
  | leaf => exact ⟨cx, leaf, kx, rx, rfl⟩
  | node cy ly ky ry => exact ⟨cy, ly, ky, node cx ry kx rx, rfl⟩

omit [LinearOrder α] in
theorem mem_deleteFixupCase234L (c' : Color) (x : RBTree α) (k : α) (s : RBTree α) (b : α) :
    Mem b (deleteFixupCase234L c' x k s).1 ↔ Mem b x ∨ b = k ∨ Mem b s := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · simp [deleteFixupCase234L, Mem]
  · simp only [deleteFixupCase234L]
    split_ifs with hno hsr
    · simp [Mem]
    · simp only [mem_rotateLeft, mem_node, mem_blacken]; try tauto
    · obtain ⟨c'', l'', k'', r'', heq⟩ := exists_node_rotateRight (α := α)
        (cx := Color.red) (lx := blacken sl) (kx := sk) (rx := sr)
      rw [heq]
      have hmems' : Mem b (node c'' l'' k'' r'') ↔ Mem b (node cs sl sk sr) := by
        rw [← heq, mem_rotateRight]; simp [Mem, mem_blacken]
      simp only [mem_rotateLeft, mem_node, mem_blacken] at hmems' ⊢
      tauto

omit [LinearOrder α] in
theorem mem_deleteFixupCase234R (c' : Color) (k : α) (x s : RBTree α) (b : α) :
    Mem b (deleteFixupCase234R c' k x s).1 ↔ Mem b s ∨ b = k ∨ Mem b x := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · simp [deleteFixupCase234R, Mem]
  · simp only [deleteFixupCase234R]
    split_ifs with hno hsl
    · simp [Mem]
    · simp only [mem_rotateRight, mem_node, mem_blacken]; try tauto
    · obtain ⟨c'', l'', k'', r'', heq⟩ := exists_node_rotateLeft (α := α)
        (cx := Color.red) (lx := sl) (kx := sk) (rx := blacken sr)
      rw [heq]
      have hmems' : Mem b (node c'' l'' k'' r'') ↔ Mem b (node cs sl sk sr) := by
        rw [← heq, mem_rotateLeft]; simp [Mem, mem_blacken]
      simp only [mem_rotateRight, mem_node, mem_blacken] at hmems' ⊢
      tauto

omit [LinearOrder α] in
theorem mem_deleteFixupL (c : Color) (x : RBTree α) (k : α) (w : RBTree α) (b : α) :
    Mem b (deleteFixupL c x k w).1 ↔ Mem b (node c x k w) := by
  rcases w with _ | ⟨cw, wl, wk, wr⟩
  · simp [deleteFixupL, mem_deleteFixupCase234L, Mem]
  · cases cw <;>
      (simp only [deleteFixupL, mem_node, mem_deleteFixupCase234L]; try tauto)

omit [LinearOrder α] in
theorem mem_deleteFixupR (c : Color) (w : RBTree α) (k : α) (x : RBTree α) (b : α) :
    Mem b (deleteFixupR c w k x).1 ↔ Mem b (node c w k x) := by
  rcases w with _ | ⟨cw, wl, wk, wr⟩
  · simp [deleteFixupR, mem_deleteFixupCase234R, Mem]
  · cases cw <;>
      (simp only [deleteFixupR, mem_node, mem_deleteFixupCase234R]; try tauto)

theorem sorted_deleteFixupCase234L {c' : Color} {x : RBTree α} {k : α} {s : RBTree α}
    (ht : Sorted (node c' x k s)) : Sorted (deleteFixupCase234L c' x k s).1 := by
  obtain ⟨hxk, hks, hsx, hss⟩ := ht
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · exact ⟨hxk, trivial, hsx, trivial⟩
  · obtain ⟨hks_l, hks_k, hks_r⟩ := hks
    obtain ⟨hsl_sk, hsk_sr, hsl_sorted, hsr_sorted⟩ := hss
    have hpre1 : Sorted (node .black x k (node c' sl sk (blacken sr))) :=
      ⟨hxk, ⟨hks_l, hks_k, (all_blacken sr).mpr hks_r⟩, hsx,
        ⟨hsl_sk, (all_blacken sr).mpr hsk_sr, hsl_sorted, sorted_blacken hsr_sorted⟩⟩
    have hpre2 : Sorted (node .red (blacken sl) sk sr) :=
      ⟨(all_blacken sl).mpr hsl_sk, hsk_sr, sorted_blacken hsl_sorted, hsr_sorted⟩
    have hpre2_all : All (k < ·) (node .red (blacken sl) sk sr) :=
      ⟨(all_blacken sl).mpr hks_l, hks_k, hks_r⟩
    simp only [deleteFixupCase234L]
    split_ifs with hno hsr'
    · exact ⟨hxk, ⟨hks_l, hks_k, hks_r⟩, hsx, ⟨hsl_sk, hsk_sr, hsl_sorted, hsr_sorted⟩⟩
    · exact sorted_rotateLeft hpre1
    · obtain ⟨cq, lq, kq, rq, heq⟩ := exists_node_rotateRight (α := α)
        (cx := Color.red) (lx := blacken sl) (kx := sk) (rx := sr)
      have hq_sorted : Sorted (node cq lq kq rq) := heq ▸ sorted_rotateRight hpre2
      have hq_all : All (k < ·) (node cq lq kq rq) := heq ▸ (all_rotateRight _).mpr hpre2_all
      obtain ⟨hlq_kq, hkq_rq, hlq_sorted, hrq_sorted⟩ := hq_sorted
      obtain ⟨hlq_k, hkq_k, hrq_k⟩ := hq_all
      have hfinal : Sorted (node .black x k (node c' lq kq (blacken rq))) :=
        ⟨hxk, ⟨hlq_k, hkq_k, (all_blacken rq).mpr hrq_k⟩, hsx,
          ⟨hlq_kq, (all_blacken rq).mpr hkq_rq, hlq_sorted, sorted_blacken hrq_sorted⟩⟩
      rw [heq]
      exact sorted_rotateLeft hfinal

theorem sorted_deleteFixupCase234R {c' : Color} {k : α} {x s : RBTree α}
    (ht : Sorted (node c' s k x)) : Sorted (deleteFixupCase234R c' k x s).1 := by
  obtain ⟨hsk, hkx, hss, hsx⟩ := ht
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · exact ⟨trivial, hkx, trivial, hsx⟩
  · obtain ⟨hsl_k, hk_k, hsr_k⟩ := hsk
    obtain ⟨hsl_sk, hsk_sr, hsl_sorted, hsr_sorted⟩ := hss
    have hpre1 : Sorted (node .black (node c' (blacken sl) sk sr) k x) :=
      ⟨⟨(all_blacken sl).mpr hsl_k, hk_k, hsr_k⟩, hkx,
        ⟨(all_blacken sl).mpr hsl_sk, hsk_sr, sorted_blacken hsl_sorted, hsr_sorted⟩, hsx⟩
    have hpre2 : Sorted (node .red sl sk (blacken sr)) :=
      ⟨hsl_sk, (all_blacken sr).mpr hsk_sr, hsl_sorted, sorted_blacken hsr_sorted⟩
    have hpre2_all : All (· < k) (node .red sl sk (blacken sr)) :=
      ⟨hsl_k, hk_k, (all_blacken sr).mpr hsr_k⟩
    simp only [deleteFixupCase234R]
    split_ifs with hno hsl'
    · exact ⟨⟨hsl_k, hk_k, hsr_k⟩, hkx, ⟨hsl_sk, hsk_sr, hsl_sorted, hsr_sorted⟩, hsx⟩
    · exact sorted_rotateRight hpre1
    · obtain ⟨cq, lq, kq, rq, heq⟩ := exists_node_rotateLeft (α := α)
        (cx := Color.red) (lx := sl) (kx := sk) (rx := blacken sr)
      have hq_sorted : Sorted (node cq lq kq rq) := heq ▸ sorted_rotateLeft hpre2
      have hq_all : All (· < k) (node cq lq kq rq) := heq ▸ (all_rotateLeft _).mpr hpre2_all
      obtain ⟨hlq_kq, hkq_rq, hlq_sorted, hrq_sorted⟩ := hq_sorted
      obtain ⟨hlq_k, hkq_k, hrq_k⟩ := hq_all
      have hfinal : Sorted (node .black (node c' (blacken lq) kq rq) k x) :=
        ⟨⟨(all_blacken lq).mpr hlq_k, hkq_k, hrq_k⟩, hkx,
          ⟨(all_blacken lq).mpr hlq_kq, hkq_rq, sorted_blacken hlq_sorted, hrq_sorted⟩, hsx⟩
      rw [heq]
      exact sorted_rotateRight hfinal

theorem sorted_deleteFixupL {c : Color} {x : RBTree α} {k : α} {w : RBTree α}
    (ht : Sorted (node c x k w)) : Sorted (deleteFixupL c x k w).1 := by
  rcases w with _ | ⟨cw, wl, wk, wr⟩
  · simpa [deleteFixupL, deleteFixupCase234L] using ht
  · cases cw
    · obtain ⟨hxk, hkw, hsx, hsw⟩ := ht
      obtain ⟨hkwl, hk_wk, hkwr⟩ := hkw
      obtain ⟨hwl_wk, hwk_wr, hwl_sorted, hwr_sorted⟩ := hsw
      have hinner : Sorted (node .red x k wl) := ⟨hxk, hkwl, hsx, hwl_sorted⟩
      have hsorted_res : Sorted (deleteFixupCase234L .red x k wl).1 :=
        sorted_deleteFixupCase234L hinner
      have hall_res : All (· < wk) (deleteFixupCase234L .red x k wl).1 := by
        apply all_of_forall_mem
        intro b hb
        rw [mem_deleteFixupCase234L] at hb
        rcases hb with hbx | rfl | hbwl
        · exact lt_trans (hxk.of_mem hbx) hk_wk
        · exact hk_wk
        · exact hwl_wk.of_mem hbwl
      simp only [deleteFixupL]
      exact ⟨hall_res, hwk_wr, hsorted_res, hwr_sorted⟩
    · simpa [deleteFixupL] using sorted_deleteFixupCase234L ht

theorem sorted_deleteFixupR {c : Color} {w : RBTree α} {k : α} {x : RBTree α}
    (ht : Sorted (node c w k x)) : Sorted (deleteFixupR c w k x).1 := by
  rcases w with _ | ⟨cw, wl, wk, wr⟩
  · simpa [deleteFixupR, deleteFixupCase234R] using ht
  · cases cw
    · obtain ⟨hwk, hkx, hsw, hsx⟩ := ht
      obtain ⟨hwlk, hwk_k, hwrk⟩ := hwk
      obtain ⟨hwl_wk, hwk_wr, hwl_sorted, hwr_sorted⟩ := hsw
      have hinner : Sorted (node .red wr k x) := ⟨hwrk, hkx, hwr_sorted, hsx⟩
      have hsorted_res : Sorted (deleteFixupCase234R .red k x wr).1 :=
        sorted_deleteFixupCase234R hinner
      have hall_res : All (wk < ·) (deleteFixupCase234R .red k x wr).1 := by
        apply all_of_forall_mem
        intro b hb
        rw [mem_deleteFixupCase234R] at hb
        rcases hb with hbwr | rfl | hbx
        · exact hwk_wr.of_mem hbwr
        · exact hwk_k
        · exact lt_trans hwk_k (hkx.of_mem hbx)
      simp only [deleteFixupR]
      exact ⟨hwl_wk, hall_res, hwl_sorted, hsorted_res⟩
    · simpa [deleteFixupR] using sorted_deleteFixupCase234R ht

omit [LinearOrder α] in
/-- The key `delMin` reports removing is always still a member of the original tree -- the
color-blind half of "it removes the minimum": *that* it's a real member, not yet *that* it's the
smallest. Proved separately from `mem_delMin` (which needs this fact about the specific key `m`,
not just the fixed `b` its own induction is stated for). -/
theorem delMin_min_mem (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    Mem (delMin c l k r).2.2 (node c l k r) := by
  induction l generalizing c k r with
  | leaf =>
    cases c with
    | red => exact Or.inr (Or.inl rfl)
    | black => cases r <;> exact Or.inr (Or.inl rfl)
  | node cl ll lk lr ihl =>
    rcases hdm : delMin cl ll lk lr with ⟨l', deficient, m⟩
    have hmem_ll : Mem m (node cl ll lk lr) := by
      have h := ihl (c := cl) (k := lk) (r := lr)
      rw [hdm] at h
      exact h
    simp only [delMin, hdm]
    cases deficient <;> simp_all [Mem]

/-- The other half of "`delMin` finds the minimum": the reported key is a lower bound for the
*whole* original tree, not just present in it. Needed by `sorted_del`'s two-children case, to know
the promoted successor key still bounds everything in the (rebuilt) right subtree from below. -/
theorem delMin_le {c : Color} {l : RBTree α} {k : α} {r : RBTree α} (ht : Sorted (node c l k r)) :
    All ((delMin c l k r).2.2 ≤ ·) (node c l k r) := by
  induction l generalizing c k r with
  | leaf =>
    obtain ⟨-, hkr, -, -⟩ := ht
    cases c with
    | red => exact ⟨trivial, le_refl _, hkr.imp (fun _ h => le_of_lt h)⟩
    | black =>
      cases r with
      | leaf => exact ⟨trivial, le_refl _, trivial⟩
      | node crr rl rk rr => exact ⟨trivial, le_refl _, hkr.imp (fun _ h => le_of_lt h)⟩
  | node cl ll lk lr ihl =>
    obtain ⟨hlk, hkr, hsl, hsr⟩ := ht
    have hih := ihl hsl
    rcases hdm : delMin cl ll lk lr with ⟨l', deficient, m⟩
    rw [hdm] at hih
    have hmem : Mem m (node cl ll lk lr) := by
      have h := delMin_min_mem cl ll lk lr
      rw [hdm] at h
      exact h
    have hmk : m < k := hlk.of_mem hmem
    simp only [delMin, hdm]
    cases deficient <;> exact ⟨hih, le_of_lt hmk, hkr.imp (fun _ h => le_of_lt (lt_trans hmk h))⟩

/-- **`delMin` is correct**: it removes exactly the tree's minimum (`.2.2`) and nothing else. -/
theorem mem_delMin {c : Color} {l : RBTree α} {k : α} {r : RBTree α} (ht : Sorted (node c l k r))
    (b : α) : Mem b (delMin c l k r).1 ↔ b ≠ (delMin c l k r).2.2 ∧ Mem b (node c l k r) := by
  induction l generalizing c k r with
  | leaf =>
    obtain ⟨-, hkr, -, -⟩ := ht
    cases c with
    | red =>
      simp only [delMin]
      constructor
      · intro hbr
        exact ⟨(ne_of_lt (hkr.of_mem hbr)).symm, Or.inr (Or.inr hbr)⟩
      · rintro ⟨hne, hbleaf | rfl | hbr⟩
        · cases hbleaf
        · exact absurd rfl hne
        · exact hbr
    | black =>
      cases r with
      | leaf => simp [delMin, Mem]
      | node crr rl rk rr =>
        simp only [delMin]
        constructor
        · intro hb
          have hb' : Mem b (node crr rl rk rr) := by simpa [Mem] using hb
          exact ⟨(ne_of_lt (hkr.of_mem hb')).symm, Or.inr (Or.inr hb')⟩
        · rintro ⟨hne, hbleaf | rfl | hb⟩
          · cases hbleaf
          · exact absurd rfl hne
          · simpa [Mem] using hb
  | node cl ll lk lr ihl =>
    obtain ⟨hlk, hkr, hsl, hsr⟩ := ht
    have hihl := ihl hsl
    rcases hdm : delMin cl ll lk lr with ⟨l', deficient, m⟩
    rw [hdm] at hihl
    have hmem_ll : Mem m (node cl ll lk lr) := by
      have h := delMin_min_mem cl ll lk lr
      rw [hdm] at h
      exact h
    have hmk : m < k := hlk.of_mem hmem_ll
    have hmnek : m ≠ k := ne_of_lt hmk
    have hqd : ¬ (b = m ∧ b = k) := fun ⟨hbm, hbk⟩ => hmnek (hbm ▸ hbk)
    have hqe : ¬ (b = m ∧ Mem b r) := fun ⟨hbm, hbr⟩ => lt_asymm hmk (hbm ▸ hkr.of_mem hbr)
    simp only [delMin, hdm]
    cases deficient with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      simp only [mem_node] at hihl ⊢
      tauto
    | true =>
      simp only [ite_true]
      rw [mem_deleteFixupL]
      simp only [mem_node] at hihl ⊢
      tauto

theorem sorted_delMin {c : Color} {l : RBTree α} {k : α} {r : RBTree α}
    (ht : Sorted (node c l k r)) : Sorted (delMin c l k r).1 := by
  induction l generalizing c k r with
  | leaf =>
    obtain ⟨-, hkr, -, hsr⟩ := ht
    cases c with
    | red => exact hsr
    | black =>
      cases r with
      | leaf => trivial
      | node crr rl rk rr => exact hsr
  | node cl ll lk lr ihl =>
    obtain ⟨hlk, hkr, hsl, hsr⟩ := ht
    rcases hdm : delMin cl ll lk lr with ⟨l', deficient, m⟩
    have hsl' : Sorted l' := by have h := ihl hsl; rw [hdm] at h; exact h
    have hmem := mem_delMin hsl
    have hb'_helper : ∀ b, Mem b l' → Mem b (node cl ll lk lr) := by
      intro b hb
      have h := (hmem b).mp
      rw [hdm] at h
      exact (h hb).2
    have hl'_all : All (· < k) l' := all_of_forall_mem (fun b hb => hlk.of_mem (hb'_helper b hb))
    have hpre : Sorted (node c l' k r) := ⟨hl'_all, hkr, hsl', hsr⟩
    simp only [delMin, hdm]
    cases deficient with
    | false => simpa using hpre
    | true => simp only [ite_true]; exact sorted_deleteFixupL hpre

/-- **`del` is correct**: it removes exactly `a` and nothing else, same shape as `mem_insert`/
`BST.mem_delete`. -/
theorem mem_del {t : RBTree α} (ht : Sorted t) (a b : α) :
    Mem b (del a t).1 ↔ b ≠ a ∧ Mem b t := by
  induction t generalizing a with
  | leaf => simp [del, Mem]
  | node c l k r ihl ihr =>
    obtain ⟨hlk, hkr, hsl, hsr⟩ := ht
    unfold del
    split
    · rename_i hak
      have hihl := ihl hsl a
      rcases hdl : del a l with ⟨l', deficient⟩
      simp only [hdl] at hihl ⊢
      have key : Mem b (if deficient then deleteFixupL c l' k r else (node c l' k r, false)).1 ↔
          Mem b (node c l' k r) := by
        cases deficient with
        | false => simp
        | true => simp only [ite_true]; exact mem_deleteFixupL c l' k r b
      rw [key, mem_node, mem_node]
      constructor
      · rintro (h | rfl | h)
        · obtain ⟨hne, h'⟩ := hihl.mp h
          exact ⟨hne, Or.inl h'⟩
        · exact ⟨(ne_of_lt hak).symm, Or.inr (Or.inl rfl)⟩
        · exact ⟨(ne_of_lt (lt_trans hak (hkr.of_mem h))).symm, Or.inr (Or.inr h)⟩
      · rintro ⟨hne, hbl | rfl | hbr⟩
        · exact Or.inl (hihl.mpr ⟨hne, hbl⟩)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hbr)
    · split
      · rename_i hak hka
        have hihr := ihr hsr a
        rcases hdr : del a r with ⟨r', deficient⟩
        simp only [hdr] at hihr ⊢
        have key : Mem b (if deficient then deleteFixupR c l k r' else (node c l k r', false)).1 ↔
            Mem b (node c l k r') := by
          cases deficient with
          | false => simp
          | true => simp only [ite_true]; exact mem_deleteFixupR c l k r' b
        rw [key, mem_node, mem_node]
        constructor
        · rintro (h | rfl | h)
          · exact ⟨ne_of_lt (lt_trans (hlk.of_mem h) hka), Or.inl h⟩
          · exact ⟨ne_of_lt hka, Or.inr (Or.inl rfl)⟩
          · obtain ⟨hne, h'⟩ := hihr.mp h
            exact ⟨hne, Or.inr (Or.inr h')⟩
        · rintro ⟨hne, hbl | rfl | hbr⟩
          · exact Or.inl hbl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (hihr.mpr ⟨hne, hbr⟩))
      · rename_i hak hka
        have hak' : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
        rw [← hak']
        rcases l with _ | ⟨cl, ll, lk, lr⟩
        · -- l = leaf: same shape as `delMin`'s `l = leaf` case (`mem_delMin`'s proof), since
          -- `del`'s `a = k` branch computes identically once `c`/`r` are cased.
          cases c with
          | red =>
            simp only
            constructor
            · intro hbr
              exact ⟨(ne_of_lt (hkr.of_mem hbr)).symm, Or.inr (Or.inr hbr)⟩
            · rintro ⟨hne, hbleaf | rfl | hbr⟩
              · cases hbleaf
              · exact absurd rfl hne
              · exact hbr
          | black =>
            cases r with
            | leaf => simp [Mem]
            | node crr rl rk rr =>
              simp only
              constructor
              · intro hb
                have hb' : Mem b (node crr rl rk rr) := by simpa [Mem] using hb
                exact ⟨(ne_of_lt (hkr.of_mem hb')).symm, Or.inr (Or.inr hb')⟩
              · rintro ⟨hne, hbleaf | rfl | hb⟩
                · cases hbleaf
                · exact absurd rfl hne
                · simpa [Mem] using hb
        · rcases r with _ | ⟨cr, rl, rk, rr⟩
          · -- r = leaf: the mirror image, worked out directly (no separate `delMax` helper).
            obtain ⟨-, -, -, -⟩ := hsl
            cases c with
            | red =>
              simp only
              constructor
              · intro hbl
                exact ⟨ne_of_lt (hlk.of_mem hbl), Or.inl hbl⟩
              · rintro ⟨hne, hbl | rfl | hbr⟩
                · exact hbl
                · exact absurd rfl hne
                · cases hbr
            | black =>
              simp only
              constructor
              · intro hb
                have hb' : Mem b (node cl ll lk lr) := by simpa [Mem] using hb
                exact ⟨ne_of_lt (hlk.of_mem hb'), Or.inl hb'⟩
              · rintro ⟨hne, hbl | rfl | hbr⟩
                · simpa [Mem] using hbl
                · exact absurd rfl hne
                · cases hbr
          · -- l, r both non-leaf: move the successor (`delMin` on `r`) up in `k`'s place.
            have hmin := mem_delMin (c := cr) (l := rl) (k := rk) (r := rr) hsr b
            rcases hdm : delMin cr rl rk rr with ⟨r'', deficient, m⟩
            simp only [hdm] at hmin
            have hmem_r : Mem m (node cr rl rk rr) := by
              have h := delMin_min_mem cr rl rk rr
              rw [hdm] at h
              exact h
            have hkm : k < m := hkr.of_mem hmem_r
            simp only [hdm]
            have key : Mem b (if deficient then deleteFixupR c (node cl ll lk lr) m r''
                else (node c (node cl ll lk lr) m r'', false)).1 ↔
                Mem b (node c (node cl ll lk lr) m r'') := by
              cases deficient with
              | false => simp
              | true => simp only [ite_true]; exact mem_deleteFixupR c (node cl ll lk lr) m r'' b
            rw [key]
            have hbk_of_left : Mem b (node cl ll lk lr) → b ≠ k := fun h => ne_of_lt (hlk.of_mem h)
            have hbk_of_right : Mem b (node cr rl rk rr) → b ≠ k :=
              fun h => (ne_of_lt (hkr.of_mem h)).symm
            rw [mem_node, mem_node]
            constructor
            · rintro (hbl | rfl | hbr)
              · exact ⟨hbk_of_left hbl, Or.inl hbl⟩
              · exact ⟨(ne_of_lt hkm).symm, Or.inr (Or.inr hmem_r)⟩
              · obtain ⟨hne, h'⟩ := hmin.mp hbr
                exact ⟨hbk_of_right h', Or.inr (Or.inr h')⟩
            · rintro ⟨hne, hbl | rfl | hbr⟩
              · exact Or.inl hbl
              · exact absurd rfl hne
              · by_cases hbm : b = m
                · exact Or.inr (Or.inl hbm)
                · exact Or.inr (Or.inr (hmin.mpr ⟨hbm, hbr⟩))

/-- **`del` preserves the BST invariant**, same shape as `sorted_insert`/`BST.sorted_delete`. -/
theorem sorted_del {t : RBTree α} (ht : Sorted t) (a : α) : Sorted (del a t).1 := by
  induction t generalizing a with
  | leaf => simp [del, Sorted]
  | node c l k r ihl ihr =>
    obtain ⟨hlk, hkr, hsl, hsr⟩ := ht
    unfold del
    split
    · rename_i hak
      have hihl := ihl hsl a
      rcases hdl : del a l with ⟨l', deficient⟩
      rw [hdl] at hihl
      have hl'_all : All (· < k) l' := by
        apply all_of_forall_mem
        intro b hb
        have hb' : Mem b l := by
          have h := (mem_del hsl a b).mp
          rw [hdl] at h
          exact (h hb).2
        exact hlk.of_mem hb'
      have hpre : Sorted (node c l' k r) := ⟨hl'_all, hkr, hihl, hsr⟩
      simp only
      cases deficient with
      | false => simpa using hpre
      | true => simp only [ite_true]; exact sorted_deleteFixupL hpre
    · split
      · rename_i hak hka
        have hihr := ihr hsr a
        rcases hdr : del a r with ⟨r', deficient⟩
        rw [hdr] at hihr
        have hr'_all : All (k < ·) r' := by
          apply all_of_forall_mem
          intro b hb
          have hb' : Mem b r := by
            have h := (mem_del hsr a b).mp
            rw [hdr] at h
            exact (h hb).2
          exact hkr.of_mem hb'
        have hpre : Sorted (node c l k r') := ⟨hlk, hr'_all, hsl, hihr⟩
        simp only
        cases deficient with
        | false => simpa using hpre
        | true => simp only [ite_true]; exact sorted_deleteFixupR hpre
      · rename_i hak hka
        rcases l with _ | ⟨cl, ll, lk, lr⟩
        · -- l = leaf: same computation as `delMin`'s `l = leaf` branch.
          cases c with
          | red => simpa using hsr
          | black =>
            cases r with
            | leaf => trivial
            | node crr rl rk rr => simp only; exact hsr
        · rcases r with _ | ⟨cr, rl, rk, rr⟩
          · -- r = leaf: the mirror image.
            cases c with
            | red => simpa using hsl
            | black => simp only; exact hsl
          · -- l, r both non-leaf: promote the successor (`delMin` on `r`).
            have hsm := sorted_delMin (c := cr) (l := rl) (k := rk) (r := rr) hsr
            have hle := delMin_le (c := cr) (l := rl) (k := rk) (r := rr) hsr
            rcases hdm : delMin cr rl rk rr with ⟨r'', deficient, m⟩
            rw [hdm] at hsm hle
            have hmem_r : Mem m (node cr rl rk rr) := by
              have h := delMin_min_mem cr rl rk rr
              rw [hdm] at h
              exact h
            have hkm : k < m := hkr.of_mem hmem_r
            have hl_all : All (· < m) (node cl ll lk lr) :=
              hlk.imp (fun _ h => lt_trans h hkm)
            have hr''_all : All (m < ·) r'' := by
              apply all_of_forall_mem
              intro b hb
              have hb' : b ≠ m ∧ Mem b (node cr rl rk rr) := by
                have h := (mem_delMin hsr b).mp
                rw [hdm] at h
                exact h hb
              exact lt_of_le_of_ne (hle.of_mem hb'.2) (Ne.symm hb'.1)
            have hpre : Sorted (node c (node cl ll lk lr) m r'') :=
              ⟨hl_all, hr''_all, hsl, hsm⟩
            simp only [hdm]
            cases deficient with
            | false => simpa using hpre
            | true => simp only [ite_true]; exact sorted_deleteFixupR hpre

/-- **`delete` is correct**: it removes exactly `a` and nothing else. -/
theorem mem_delete {t : RBTree α} (ht : Sorted t) (a b : α) :
    Mem b (delete a t) ↔ b ≠ a ∧ Mem b t :=
  mem_del ht a b

/-- **`delete` preserves the BST invariant**. -/
theorem sorted_delete {t : RBTree α} (ht : Sorted t) (a : α) : Sorted (delete a t) :=
  sorted_del ht a

/-! ### `delete`'s color-invariant preservation

Mirrors the `insertFixupL_spec`/`insertFixupR_spec`/`ins_spec`/`valid_insert` chain above, but for
CLRS's "extra blackness" device: instead of a residual red-red violation threaded via a
color-conditional disjunct, here a black-height *deficit* of exactly one is threaded via the `Bool`
`deleteFixupL`/`deleteFixupR`/`delMin`/`del` already return, and each spec states how that `Bool`
trades against `bheight`: a spliced-out or absorbed deficiency lowers `bheight` by one relative to
what the input contributed, tracked by adding `1` back in exactly when the returned flag is
`false`. -/

omit [LinearOrder α] in
/-- `RB-DELETE-FIXUP`'s `Case 2`/`3`/`4`, run against a sibling `s` already known black-rooted (or
`leaf`, vacuously black) with a genuine one-black-node deficit `x` on the other side (`hbh`). Since
`s` is black-rooted, `x` always ends up fully absorbed under a black parent -- the result is always
fully `NoRedRed`, never merely `NoRedRed2`, unlike the insert side's fixups (which can leave a
residual violation for the caller to handle). The deficiency only survives (`.2 = true`) in
`Case 2` when `c'` was already black (nothing left to absorb it into); a red `c'` always fully
resolves it, since `Case 2` recolors this node to black regardless and a red `c'` had exactly the
one spare unit of blackness needed. -/
theorem deleteFixupCase234L_spec {c' : Color} {x : RBTree α} {k : α} {s : RBTree α}
    (hs_black : s.IsBlack) (hs_bal : Balanced s) (hs_nrr : NoRedRed s)
    (hx_bal : Balanced x) (hx_nrr : NoRedRed x) (hbh : bheight x + 1 = bheight s) :
    bheight (deleteFixupCase234L c' x k s).1 +
        (if (deleteFixupCase234L c' x k s).2 then 1 else 0) =
      bheight s + (if c' = .black then 1 else 0) ∧
    Balanced (deleteFixupCase234L c' x k s).1 ∧
    NoRedRed (deleteFixupCase234L c' x k s).1 ∧
    (c' = .black → (deleteFixupCase234L c' x k s).1.IsBlack) ∧
    (c' = .red → (deleteFixupCase234L c' x k s).2 = false) := by
  have hxpos := bheight_pos x
  rcases s with _ | ⟨cs, _ | ⟨csl, sll, slk, slr⟩, sk, _ | ⟨csr, srl, srk, srr⟩⟩ <;>
    cases c' <;> (try cases csl) <;> (try cases csr) <;>
    simp_all [deleteFixupCase234L, rotateLeft, rotateRight, blacken, isRed, NoRedRed, Balanced,
      bheight, IsBlack] <;>
    omega

omit [LinearOrder α] in
/-- Mirror of `deleteFixupCase234L_spec` for `deleteFixupCase234R`. -/
theorem deleteFixupCase234R_spec {c' : Color} {k : α} {x s : RBTree α}
    (hs_black : s.IsBlack) (hs_bal : Balanced s) (hs_nrr : NoRedRed s)
    (hx_bal : Balanced x) (hx_nrr : NoRedRed x) (hbh : bheight x + 1 = bheight s) :
    bheight (deleteFixupCase234R c' k x s).1 +
        (if (deleteFixupCase234R c' k x s).2 then 1 else 0) =
      bheight s + (if c' = .black then 1 else 0) ∧
    Balanced (deleteFixupCase234R c' k x s).1 ∧
    NoRedRed (deleteFixupCase234R c' k x s).1 ∧
    (c' = .black → (deleteFixupCase234R c' k x s).1.IsBlack) ∧
    (c' = .red → (deleteFixupCase234R c' k x s).2 = false) := by
  have hxpos := bheight_pos x
  rcases s with _ | ⟨cs, _ | ⟨csl, sll, slk, slr⟩, sk, _ | ⟨csr, srl, srk, srr⟩⟩ <;>
    cases c' <;> (try cases csl) <;> (try cases csr) <;>
    simp_all [deleteFixupCase234R, rotateLeft, rotateRight, blacken, isRed, NoRedRed, Balanced,
      bheight, IsBlack] <;>
    omega

omit [LinearOrder α] in
/-- One `RB-DELETE-FIXUP` step on a left-child deficit, including Case 1's rotate-and-fall-through.
The returned black-height plus surviving deficiency equals what a balanced `node c x k w` would
have contributed, using `w`'s black-height as the pre-deletion sibling height. -/
theorem deleteFixupL_spec {c : Color} {x : RBTree α} {k : α} {w : RBTree α}
    (hx_bal : Balanced x) (hx_nrr : NoRedRed x)
    (hw_bal : Balanced w) (hw_nrr : NoRedRed w)
    (hw_black_of_red : c = .red → w.IsBlack)
    (hbh : bheight x + 1 = bheight w) :
    bheight (deleteFixupL c x k w).1 +
        (if (deleteFixupL c x k w).2 then 1 else 0) =
      bheight w + (if c = .black then 1 else 0) ∧
    Balanced (deleteFixupL c x k w).1 ∧
    NoRedRed (deleteFixupL c x k w).1 ∧
    (c = .black → (deleteFixupL c x k w).1.IsBlack) ∧
    (c = .red → (deleteFixupL c x k w).2 = false) := by
  have hxpos : 1 ≤ bheight x := bheight_pos (t := x)
  rcases w with _ | ⟨cw, wl, wk, wr⟩
  · simp [bheight] at hbh
    omega
  · cases cw with
    | black =>
      have h234 := deleteFixupCase234L_spec (c' := c) (x := x) (k := k)
        (s := node .black wl wk wr)
        (by simp [IsBlack]) hw_bal hw_nrr hx_bal hx_nrr hbh
      simp only [deleteFixupL]
      exact h234
    | red =>
      obtain ⟨hnr, hwl_nrr, hwr_nrr⟩ := hw_nrr
      obtain ⟨hwl_black, hwr_black⟩ := hnr rfl
      obtain ⟨hbh_w, hwl_bal, hwr_bal⟩ := hw_bal
      have hc : c = .black := by
        cases c with
        | black => rfl
        | red => nomatch hw_black_of_red rfl
      subst hc
      have hbh' : bheight x + 1 = bheight wl := by
        simp [bheight] at hbh ⊢; omega
      have h234 := deleteFixupCase234L_spec (c' := .red) (x := x) (k := k) (s := wl)
        hwl_black hwl_bal hwl_nrr hx_bal hx_nrr hbh'
      obtain ⟨hbh234, hbal234, hnrr234, -, hdef234⟩ := h234
      have hfalse : (deleteFixupCase234L .red x k wl).2 = false := hdef234 rfl
      simp only [deleteFixupL]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [bheight, hfalse] at hbh234 ⊢
        omega
      · refine ⟨?_, hbal234, hwr_bal⟩
        simp [hfalse] at hbh234 hbh_w ⊢
        omega
      · exact ⟨fun h => Color.noConfusion h, hnrr234, hwr_nrr⟩
      · intro _; rfl
      · intro h; exact nomatch h

omit [LinearOrder α] in
/-- Symmetric to `deleteFixupL_spec`. -/
theorem deleteFixupR_spec {c : Color} {w : RBTree α} {k : α} {x : RBTree α}
    (hx_bal : Balanced x) (hx_nrr : NoRedRed x)
    (hw_bal : Balanced w) (hw_nrr : NoRedRed w)
    (hw_black_of_red : c = .red → w.IsBlack)
    (hbh : bheight x + 1 = bheight w) :
    bheight (deleteFixupR c w k x).1 +
        (if (deleteFixupR c w k x).2 then 1 else 0) =
      bheight w + (if c = .black then 1 else 0) ∧
    Balanced (deleteFixupR c w k x).1 ∧
    NoRedRed (deleteFixupR c w k x).1 ∧
    (c = .black → (deleteFixupR c w k x).1.IsBlack) ∧
    (c = .red → (deleteFixupR c w k x).2 = false) := by
  have hxpos : 1 ≤ bheight x := bheight_pos (t := x)
  rcases w with _ | ⟨cw, wl, wk, wr⟩
  · simp [bheight] at hbh
    omega
  · cases cw with
    | black =>
      have h234 := deleteFixupCase234R_spec (c' := c) (k := k) (x := x)
        (s := node .black wl wk wr)
        (by simp [IsBlack]) hw_bal hw_nrr hx_bal hx_nrr hbh
      simp only [deleteFixupR]
      exact h234
    | red =>
      obtain ⟨hnr, hwl_nrr, hwr_nrr⟩ := hw_nrr
      obtain ⟨hwl_black, hwr_black⟩ := hnr rfl
      obtain ⟨hbh_w, hwl_bal, hwr_bal⟩ := hw_bal
      have hc : c = .black := by
        cases c with
        | black => rfl
        | red => nomatch hw_black_of_red rfl
      subst hc
      have hbh' : bheight x + 1 = bheight wr := by
        simp [bheight] at hbh hbh_w ⊢; omega
      have h234 := deleteFixupCase234R_spec (c' := .red) (k := k) (x := x) (s := wr)
        hwr_black hwr_bal hwr_nrr hx_bal hx_nrr hbh'
      obtain ⟨hbh234, hbal234, hnrr234, -, hdef234⟩ := h234
      have hfalse : (deleteFixupCase234R .red k x wr).2 = false := hdef234 rfl
      simp only [deleteFixupR]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [bheight, hfalse] at hbh234 ⊢
        try omega
      · refine ⟨?_, hwl_bal, hbal234⟩
        simp [hfalse] at hbh234 hbh_w ⊢
        try omega
      · exact ⟨fun h => Color.noConfusion h, hwl_nrr, hnrr234⟩
      · intro _; rfl
      · intro h; exact nomatch h

omit [LinearOrder α] in
/-- `delMin` preserves balance and red-red safety, and accounts for a one-black-node deficit when
a black node is spliced out. A red input never returns a surviving deficiency. -/
theorem delMin_spec {c : Color} {l : RBTree α} {k : α} {r : RBTree α}
    (hbal : Balanced (node c l k r)) (hnrr : NoRedRed (node c l k r)) :
    Balanced (delMin c l k r).1 ∧ NoRedRed (delMin c l k r).1 ∧
    bheight (delMin c l k r).1 + (if (delMin c l k r).2.1 then 1 else 0) =
      bheight (node c l k r) ∧
    (c = .black → (delMin c l k r).1.IsBlack) := by
  induction l generalizing c k r with
  | leaf =>
    obtain ⟨hbh, -, hr_bal⟩ := hbal
    obtain ⟨hnr, -, hr_nrr⟩ := hnrr
    cases c with
    | red =>
      have hr_black : r.IsBlack := (hnr rfl).2
      have hr_leaf : r = leaf := by
        cases r with
        | leaf => rfl
        | node cr rl _ _ =>
          have hcr : cr = .black := hr_black
          subst hcr
          have hpos := bheight_pos rl
          simp [bheight] at hbh
          omega
      subst hr_leaf
      simp only [delMin]
      exact ⟨hr_bal, hr_nrr, by simp [bheight], fun h => nomatch h⟩
    | black =>
      cases r with
      | leaf => simp [delMin, Balanced, NoRedRed, bheight, IsBlack]
      | node cr rl rk rr =>
        have hbhr : bheight (node cr rl rk rr) = 1 := hbh.symm
        simp only [delMin]
        refine ⟨hr_bal, ?_, ?_, fun _ => rfl⟩
        · cases cr with
          | red =>
            obtain ⟨-, hrl_nrr, hrr_nrr⟩ := hr_nrr
            refine And.intro ?_ (And.intro hrl_nrr hrr_nrr)
            intro h; exact nomatch h
          | black => exact hr_nrr
        · cases cr with
          | red =>
            simp [bheight] at hbhr ⊢
            omega
          | black =>
            have hpos : 1 ≤ bheight rl := bheight_pos (t := rl)
            simp [bheight] at hbhr
            omega
  | node cl ll lk lr ihl =>
    obtain ⟨hbh, hl_bal, hr_bal⟩ := hbal
    obtain ⟨hnr, hl_nrr, hr_nrr⟩ := hnrr
    rcases hdm : delMin cl ll lk lr with ⟨l', deficient, m⟩
    have hih := ihl hl_bal hl_nrr
    simp only [hdm] at hih
    obtain ⟨hl'_bal, hl'_nrr, hbh_l', hblack'⟩ := hih
    simp only [delMin, hdm]
    cases deficient with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hl'eq : bheight l' = bheight (node cl ll lk lr) := by simpa using hbh_l'
      have hnr' : c = .red → l'.IsBlack ∧ r.IsBlack := fun hc =>
        ⟨hblack' (hnr hc).1, (hnr hc).2⟩
      refine ⟨⟨hl'eq.trans hbh, hl'_bal, hr_bal⟩, ⟨hnr', hl'_nrr, hr_nrr⟩, ?_, ?_⟩
      · simp [bheight, hl'eq]
      · intro hc; subst hc; trivial
    | true =>
      simp only [ite_true]
      have hl'_def : bheight l' + 1 = bheight (node cl ll lk lr) := by
        simp [bheight] at hbh_l' ⊢; omega
      have hw_black : c = .red → r.IsBlack := fun hc => (hnr hc).2
      have hbh_xr : bheight l' + 1 = bheight r := by
        simp [bheight] at hbh hl'_def ⊢; omega
      obtain ⟨hbh_f, hbal_f, hnrr_f, hblack_f, -⟩ :=
        deleteFixupL_spec hl'_bal hl'_nrr hr_bal hr_nrr hw_black hbh_xr
      exact ⟨hbal_f, hnrr_f, by simp [bheight] at hbh hbh_f ⊢; omega, hblack_f⟩

/-- Strengthened induction hypothesis for `del`: balance and red-red safety, with a tracked
black-height deficit of at most one. A black-rooted input yields a black-rooted result. -/
theorem del_spec {t : RBTree α} (a : α) (hbal : Balanced t) (hnrr : NoRedRed t) :
    Balanced (del a t).1 ∧ NoRedRed (del a t).1 ∧
    bheight (del a t).1 + (if (del a t).2 then 1 else 0) = bheight t ∧
    (t.IsBlack → (del a t).1.IsBlack) := by
  induction t generalizing a with
  | leaf => simp [del, Balanced, NoRedRed, bheight, IsBlack]
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hl_bal, hr_bal⟩ := hbal
    obtain ⟨hnr, hl_nrr, hr_nrr⟩ := hnrr
    unfold del
    split
    · rename_i hak
      rcases hdl : del a l with ⟨l', deficient⟩
      have hih := ihl a hl_bal hl_nrr
      simp only [hdl] at hih
      obtain ⟨hl'_bal, hl'_nrr, hbh_l', hl'_black⟩ := hih
      cases deficient with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have hl'eq : bheight l' = bheight l := by simpa using hbh_l'
        have hnr' : c = .red → l'.IsBlack ∧ r.IsBlack := fun hc =>
          ⟨hl'_black (hnr hc).1, (hnr hc).2⟩
        refine ⟨⟨hl'eq.trans hbh, hl'_bal, hr_bal⟩, ⟨hnr', hl'_nrr, hr_nrr⟩, ?_, ?_⟩
        · simp [bheight, hl'eq]
        · intro hc
          cases c with
          | black => trivial
          | red => nomatch hc
      | true =>
        simp only [ite_true]
        have hw_black : c = .red → r.IsBlack := fun hc => (hnr hc).2
        have hbh_xr : bheight l' + 1 = bheight r := by
          simp at hbh hbh_l' ⊢; omega
        obtain ⟨hbh_f, hbal_f, hnrr_f, hblack_f, -⟩ :=
          deleteFixupL_spec (c := c) (x := l') (k := k) (w := r)
            hl'_bal hl'_nrr hr_bal hr_nrr hw_black hbh_xr
        exact ⟨hbal_f, hnrr_f, by simp [bheight] at hbh hbh_f ⊢; omega, fun hc =>
          match c with
          | .black => hblack_f rfl
          | .red => nomatch hc⟩
    · split
      · rename_i hak hka
        rcases hdr : del a r with ⟨r', deficient⟩
        have hih := ihr a hr_bal hr_nrr
        simp only [hdr] at hih
        obtain ⟨hr'_bal, hr'_nrr, hbh_r', hr'_black⟩ := hih
        cases deficient with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have hr'eq : bheight r' = bheight r := by simpa using hbh_r'
          have hnr' : c = .red → l.IsBlack ∧ r'.IsBlack := fun hc =>
            ⟨(hnr hc).1, hr'_black (hnr hc).2⟩
          refine ⟨⟨hbh.trans hr'eq.symm, hl_bal, hr'_bal⟩, ⟨hnr', hl_nrr, hr'_nrr⟩, ?_, ?_⟩
          · simp [bheight]
          · intro hc
            cases c with
            | black => trivial
            | red => nomatch hc
        | true =>
          simp only [ite_true]
          have hw_black : c = .red → l.IsBlack := fun hc => (hnr hc).1
          have hbh_xr : bheight r' + 1 = bheight l := by
            simp at hbh hbh_r' ⊢; omega
          obtain ⟨hbh_f, hbal_f, hnrr_f, hblack_f, -⟩ :=
            deleteFixupR_spec (c := c) (w := l) (k := k) (x := r')
              hr'_bal hr'_nrr hl_bal hl_nrr hw_black hbh_xr
          exact ⟨hbal_f, hnrr_f, by simp [bheight] at hbh hbh_f ⊢; omega, fun hc =>
            match c with
            | .black => hblack_f rfl
            | .red => nomatch hc⟩
      · rename_i hak hka
        cases hl : l with
        | leaf =>
          simp [hl] at hbh hl_bal hl_nrr hnr
          cases c with
          | red =>
            simp only
            refine ⟨hr_bal, hr_nrr, by
              simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, bheight, reduceCtorEq]
              exact hbh.symm,
              fun h => nomatch h⟩
          | black =>
            cases r with
            | leaf => simp [Balanced, NoRedRed, bheight, IsBlack]
            | node cr rl rk rr =>
              simp only
              refine ⟨hr_bal, ?_, ?_, fun _ => rfl⟩
              · cases cr with
                | red =>
                  obtain ⟨-, hrl_nrr, hrr_nrr⟩ := hr_nrr
                  refine And.intro ?_ (And.intro hrl_nrr hrr_nrr)
                  intro h; exact nomatch h
                | black => exact hr_nrr
              · have hbhr : bheight (node cr rl rk rr) = 1 := hbh.symm
                cases cr with
                | red => simp [bheight] at hbhr ⊢; omega
                | black =>
                  have hpos : 1 ≤ bheight rl := bheight_pos (t := rl)
                  simp [bheight] at hbhr
                  omega
        | node cl ll lk lr =>
          simp only [hl, IsBlack_node] at hbh hl_bal hl_nrr hnr
          cases hr : r with
          | leaf =>
            simp only [hr, IsBlack_leaf, and_true] at hbh hr_bal hr_nrr hnr
            cases c with
            | red =>
              simp only
              refine ⟨hl_bal, hl_nrr, by simp [bheight], fun h => nomatch h⟩
            | black =>
              simp only
              refine ⟨hl_bal, ?_, ?_, fun _ => rfl⟩
              · obtain ⟨-, hll_nrr, hlr_nrr⟩ := hl_nrr
                refine And.intro ?_ (And.intro hll_nrr hlr_nrr)
                intro h; exact nomatch h
              · have hpos := bheight_pos ll
                cases cl <;> simp [bheight] at hbh ⊢
                omega
          | node cr rl rk rr =>
            simp only [hr, IsBlack_node] at hbh hr_bal hr_nrr hnr
            rcases hdm : delMin cr rl rk rr with ⟨r'', deficient, m⟩
            have hmin := delMin_spec (c := cr) (l := rl) (k := rk) (r := rr) hr_bal hr_nrr
            simp only [hdm] at hmin
            obtain ⟨hr''_bal, hr''_nrr, hbh_r'', hblack_min⟩ := hmin
            cases deficient with
            | false =>
              simp only [hdm, Bool.false_eq_true, ite_false]
              have hr''eq : bheight r'' = bheight (node cr rl rk rr) := by simpa using hbh_r''
              have hnr' : c = .red → (node cl ll lk lr).IsBlack ∧ r''.IsBlack := fun hc =>
                ⟨(hnr hc).1, hblack_min (by simpa [IsBlack] using (hnr hc).2)⟩
              refine ⟨⟨hbh.trans hr''eq.symm, hl_bal, hr''_bal⟩, ⟨hnr', hl_nrr, hr''_nrr⟩, ?_, ?_⟩
              · simp [bheight]
              · intro hc
                cases c with
                | black => trivial
                | red => nomatch hc
            | true =>
              simp only [hdm, ite_true]
              have hw_black : c = .red → (node cl ll lk lr).IsBlack := fun hc => (hnr hc).1
              have hbh_xr : bheight r'' + 1 = bheight (node cl ll lk lr) := by
                simp [bheight] at hbh hbh_r'' ⊢; omega
              obtain ⟨hbh_f, hbal_f, hnrr_f, hblack_f, -⟩ :=
                deleteFixupR_spec (c := c) (w := node cl ll lk lr) (k := m) (x := r'')
                  hr''_bal hr''_nrr hl_bal hl_nrr hw_black hbh_xr
              exact ⟨hbal_f, hnrr_f, by simp [bheight] at hbh hbh_f ⊢; omega, fun hc =>
                match c with
                | .black => hblack_f rfl
                | .red => nomatch hc⟩

/-- **`delete` produces a legal standard red-black tree from a legal one.** Combined with
`mem_delete`/`sorted_delete`, deletion is fully verified: it removes exactly the requested key
and restores CLRS's color properties. -/
theorem valid_delete {t : RBTree α} (ht : Valid t) (a : α) : Valid (delete a t) := by
  obtain ⟨hs, hrb, hnrr, hbh⟩ := ht
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  have hblack : t.IsBlack := by
    cases t with
    | leaf => trivial
    | node _ _ _ _ => exact hrb
  obtain ⟨hbal', hnrr', -, hblack'⟩ := del_spec a hbal hnrr
  refine ⟨sorted_delete hs a, ?_, hnrr', blackHeightOk_iff_balanced.mpr hbal'⟩
  have h := hblack' hblack
  cases (del a t).1 with
  | leaf => trivial
  | node _ _ _ _ => exact h

/-- **`delete` discharges `DeleteSpec`** on a legal tree, assembled from `mem_delete` and
`valid_delete`. The `Valid` hypothesis is what makes the key-set half available: on an unsorted tree
the descent can walk past the side `a` is on. -/
theorem deleteSpec {{t : RBTree α}} (hv : Valid t) (a : α) : DeleteSpec a t (delete a t) :=
  ⟨mem_delete hv.1 a, fun h => valid_delete h a⟩

end RBTree

end AlgoDesign.Searching
