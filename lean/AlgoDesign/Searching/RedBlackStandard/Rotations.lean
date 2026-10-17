/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Cost

/-!
# Red-black tree: rotations

The constant rotation bounds the standard tree has and the LLRB lacks: an insert rotates at most
twice (`insert_rotations_le`), a delete at most three times (`delete_rotations_le`). Each bound is
on the time of a counting run (`insertRot`, `deleteRot`) that ticks once per rotation and is proved
to return the operation's own tree (`ret_insertRot`, `ret_deleteRot`).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace RBTree

variable {α : Type}
variable [LinearOrder α]

/-! ### Rotation count

CLRS's Theorem 13.4-adjacent claim, stated to the reader in the Search chapter ("What the extra
freedom costs"): a single `insert` never needs more than two rotations.

The count is taken on the operation itself. `insertRot` is `insert` run in `TimeM`, charging one
tick at each `rotateLeft`/`rotateRight` call and nothing else, and `ret_insertRot` proves its
result is `insert`'s tree; `insert_rotations_le` bounds its time. So if `insert` changed, the
`ret` theorem would break, and the count could not silently describe some other procedure.

The bound itself is proved on a closed form of that count: `insertFixupLRotations`/
`insertFixupRRotations` read the rotations off `insertFixupL`/`insertFixupR`'s four branches
(`0` for "no violation" and Case 1, `2` for Case 2, `1` for Case 3) and `insRotations` follows
`ins`'s recursion; `time_insertRot` proves the counting run's time equals it, so the closed form
cannot drift from the run either. `insRotations_le` is the induction. -/

/-- How many `rotateLeft`/`rotateRight` calls `insertFixupL c l k r` makes — read directly off its
four branches (`k` doesn't affect the count, so it's dropped from the signature). -/
def insertFixupLRotations (c : Color) (l r : RBTree α) : ℕ :=
  match c, l with
  | .black, node .red ll _lk lr =>
      if !ll.isRed && !lr.isRed then 0
      else if r.isRed then 0
      else if lr.isRed then 2
      else 1
  | _, _ => 0

/-- Symmetric to `insertFixupLRotations`. -/
def insertFixupRRotations (c : Color) (l r : RBTree α) : ℕ :=
  match c, r with
  | .black, node .red rl _rk rr =>
      if !rl.isRed && !rr.isRed then 0
      else if l.isRed then 0
      else if rl.isRed then 2
      else 1
  | _, _ => 0

omit [LinearOrder α] in
/-- **A single fixup call rotates at most twice** — true in isolation, no invariant needed: it's
read directly off `insertFixupL`'s four branches. -/
theorem insertFixupLRotations_le (c : Color) (l r : RBTree α) :
    insertFixupLRotations c l r ≤ 2 := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;>
    simp only [insertFixupLRotations] <;> (try split_ifs) <;> omega

omit [LinearOrder α] in
theorem insertFixupRRotations_le (c : Color) (l r : RBTree α) :
    insertFixupRRotations c l r ≤ 2 := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;>
    simp only [insertFixupRRotations] <;> (try split_ifs) <;> omega

omit [LinearOrder α] in
/-- **A `NoRedRed` left child needs no fixing**, for *any* `c`/`r`: if `l` isn't red-rooted, the
match fails outright; if it is, `NoRedRed` forces its own children black, landing in the "no
violation" branch. This is the fact that makes a second rotation impossible once the first one has
resolved the tree's one violation. -/
theorem insertFixupLRotations_eq_zero_of_noRedRed {l : RBTree α} (hl : NoRedRed l) (c : Color)
    (r : RBTree α) : insertFixupLRotations c l r = 0 := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;> (try cases ll) <;>
    (try cases lr) <;> simp_all [insertFixupLRotations, isRed, NoRedRed, IsBlack]

omit [LinearOrder α] in
theorem insertFixupRRotations_eq_zero_of_noRedRed {r : RBTree α} (hr : NoRedRed r) (c : Color)
    (l : RBTree α) : insertFixupRRotations c l r = 0 := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;> (try cases rl) <;>
    (try cases rr) <;> simp_all [insertFixupRRotations, isRed, NoRedRed, IsBlack]

omit [LinearOrder α] in
/-- Companion to the `_eq_zero_of_noRedRed` lemmas: whenever `l` is already `NoRedRed`,
`insertFixupL` doesn't just rotate zero times, it returns its input completely unchanged (every
zero-rotation branch — the match failing outright, or the "no violation" arm — is literally a
no-op). -/
theorem insertFixupL_eq_of_noRedRed {l : RBTree α} (hl : NoRedRed l) (c : Color) (k : α)
    (r : RBTree α) : insertFixupL c l k r = node c l k r := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;> (try cases ll) <;>
    (try cases lr) <;> simp_all [insertFixupL, isRed, NoRedRed, IsBlack]

omit [LinearOrder α] in
theorem insertFixupR_eq_of_noRedRed {r : RBTree α} (hr : NoRedRed r) (c : Color) (k : α)
    (l : RBTree α) : insertFixupR c l k r = node c l k r := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;> (try cases rl) <;>
    (try cases rr) <;> simp_all [insertFixupR, isRed, NoRedRed, IsBlack]

omit [LinearOrder α] in
/-- **A rotation, whenever it fires, fully resolves the tree** — not just to `NoRedRed`, but all
the way to black-rooted. This is what lets the resolution survive being wrapped by an ancestor of
*either* color as the recursion climbs back up: a black-rooted `NoRedRed` child can never itself be
the violator, whatever its new parent's color turns out to be. Reuses `insertFixupL_spec`'s own
hypotheses and conclusion (for the `NoRedRed` half) and adds the black-rootedness half directly,
since Case 2/3's construction always ends in an outermost `blacken`. -/
theorem insertFixupLRotations_ne_zero {c : Color} {l' r : RBTree α} {k : α}
    (hr_nrr : NoRedRed r) (hr_bal : Balanced r) (hl'_bal : Balanced l')
    (hl'_nrr_or : NoRedRed l' ∨ (c ≠ .red ∧ NoRedRed2 l' ∧ AtMostOneRedChild l'))
    (hcr : c = .red → r.IsBlack) (hbh : bheight l' = bheight r)
    (hne : insertFixupLRotations c l' r ≠ 0) :
    NoRedRed (insertFixupL c l' k r) ∧ (insertFixupL c l' k r).IsBlack := by
  have hc : c ≠ .red := by
    rintro rfl
    apply hne
    cases l' <;> rfl
  obtain ⟨-, -, e3, -⟩ := insertFixupL_spec hr_nrr hr_bal hl'_bal hl'_nrr_or hcr hbh
  refine ⟨e3 hc, ?_⟩
  cases c with
  | red => exact absurd rfl hc
  | black =>
    rcases l' with _ | ⟨cl, ll, lk, lr⟩
    · exact absurd rfl hne
    · cases cl with
      | black => exact absurd rfl hne
      | red =>
        simp only [insertFixupLRotations] at hne
        simp only [insertFixupL]
        rcases ll with _ | ⟨cll, lll, llk, llr⟩ <;> rcases lr with _ | ⟨clr, lrl, lrk, lrr⟩ <;>
          rcases r with _ | ⟨cr, rl, rk, rr⟩ <;>
          split_ifs at hne ⊢ <;> simp_all [rotateLeft, rotateRight, blacken, IsBlack]

omit [LinearOrder α] in
theorem insertFixupRRotations_ne_zero {c : Color} {l r' : RBTree α} {k : α}
    (hl_nrr : NoRedRed l) (hl_bal : Balanced l) (hr'_bal : Balanced r')
    (hr'_nrr_or : NoRedRed r' ∨ (c ≠ .red ∧ NoRedRed2 r' ∧ AtMostOneRedChild r'))
    (hcl : c = .red → l.IsBlack) (hbh : bheight l = bheight r')
    (hne : insertFixupRRotations c l r' ≠ 0) :
    NoRedRed (insertFixupR c l k r') ∧ (insertFixupR c l k r').IsBlack := by
  have hc : c ≠ .red := by
    rintro rfl
    apply hne
    cases r' <;> rfl
  obtain ⟨-, -, e3, -⟩ := insertFixupR_spec hl_nrr hl_bal hr'_bal hr'_nrr_or hcl hbh
  refine ⟨e3 hc, ?_⟩
  cases c with
  | red => exact absurd rfl hc
  | black =>
    rcases r' with _ | ⟨cr, rl, rk, rr⟩
    · exact absurd rfl hne
    · cases cr with
      | black => exact absurd rfl hne
      | red =>
        simp only [insertFixupRRotations] at hne
        simp only [insertFixupR]
        rcases rl with _ | ⟨crl, rll, rlk, rlr⟩ <;> rcases rr with _ | ⟨crr, rrl, rrk, rrr⟩ <;>
          rcases l with _ | ⟨cl, ll, lk, lr⟩ <;>
          split_ifs at hne ⊢ <;> simp_all [rotateLeft, rotateRight, blacken, IsBlack]

/-- Mirrors `ins`'s own recursion, counting `rotateLeft`/`rotateRight` calls instead of building a
tree. -/
def insRotations (a : α) : RBTree α → ℕ
  | leaf => 0
  | node c l k r =>
      if a < k then insRotations a l + insertFixupLRotations c (ins a l) r
      else if k < a then insRotations a r + insertFixupRRotations c l (ins a r)
      else 0

/-- **`insert` never rotates more than twice.** The rotation-count analogue of `ins_spec`, proved
by the same induction and reusing `ins_spec` itself (rather than re-deriving `hdisj`). The second
and third conjuncts are the induction's own load-bearing strengthening, the reason a second
rotation can never fire once the first one has: whenever a rotation has happened anywhere in the
recursion so far, the result is fully `NoRedRed` (second conjunct), and — whenever additionally the
*original* node was black-rooted — the result is black-rooted too (third conjunct), which is
exactly what keeps *that* fact propagating correctly past an ancestor of either color. -/
theorem insRotations_le {t : RBTree α} (a : α) (ht_bal : Balanced t) (ht_nrr : NoRedRed t) :
    insRotations a t ≤ 2 ∧ (insRotations a t ≠ 0 → NoRedRed (ins a t)) ∧
    (t.IsBlack → insRotations a t ≠ 0 → (ins a t).IsBlack) := by
  induction t with
  | leaf => simp [insRotations]
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hbl, hbr⟩ := ht_bal
    obtain ⟨hnr, hl_nrr, hr_nrr⟩ := ht_nrr
    obtain ⟨hle_l, hne_l, hib_l⟩ := ihl hbl hl_nrr
    obtain ⟨hle_r, hne_r, hib_r⟩ := ihr hbr hr_nrr
    unfold insRotations
    split
    · -- a < k
      rename_i hak
      have hins : ins a (node c l k r) = insertFixupL c (ins a l) k r := by
        change (if a < k then insertFixupL c (ins a l) k r else
            if k < a then insertFixupR c l k (ins a r) else node c l k r) =
          insertFixupL c (ins a l) k r
        rw [ite_eq_left hak]
      obtain ⟨e1l, e2l, e3l, e4l⟩ := ins_spec a hbl hl_nrr
      have hdisj : NoRedRed (ins a l) ∨
          (c ≠ .red ∧ NoRedRed2 (ins a l) ∧ AtMostOneRedChild (ins a l)) := by
        by_cases hlb : l.IsBlack
        · exact Or.inl (e3l hlb)
        · obtain ⟨p1, p2⟩ := e4l hlb
          exact Or.inr ⟨fun hc => absurd (hnr hc).1 hlb, p1, p2⟩
      have hcr : c = .red → r.IsBlack := fun hc => (hnr hc).2
      by_cases hzl : insRotations a l = 0
      · refine ⟨?_, ?_, ?_⟩
        · rw [hzl, Nat.zero_add]; exact insertFixupLRotations_le c (ins a l) r
        · intro hne
          rw [hzl, Nat.zero_add] at hne
          rw [hins]
          exact (insertFixupLRotations_ne_zero hr_nrr hbr e2l hdisj hcr (by omega) hne).1
        · intro _ hne
          rw [hzl, Nat.zero_add] at hne
          rw [hins]
          exact (insertFixupLRotations_ne_zero hr_nrr hbr e2l hdisj hcr (by omega) hne).2
      · have hnrr_l := hne_l hzl
        rw [insertFixupLRotations_eq_zero_of_noRedRed hnrr_l, Nat.add_zero]
        rw [hins, insertFixupL_eq_of_noRedRed hnrr_l]
        refine ⟨hle_l, fun _ => ⟨fun hc => ⟨hib_l (hnr hc).1 hzl, hcr hc⟩, hnrr_l, hr_nrr⟩,
          fun hib _ => ?_⟩
        simpa [IsBlack] using hib
    · split
      · -- k < a
        rename_i hnak hka
        have hins : ins a (node c l k r) = insertFixupR c l k (ins a r) := by
          change (if a < k then insertFixupL c (ins a l) k r else
              if k < a then insertFixupR c l k (ins a r) else node c l k r) =
            insertFixupR c l k (ins a r)
          rw [ite_eq_right hnak, ite_eq_left hka]
        obtain ⟨e1r, e2r, e3r, e4r⟩ := ins_spec a hbr hr_nrr
        have hdisj : NoRedRed (ins a r) ∨
            (c ≠ .red ∧ NoRedRed2 (ins a r) ∧ AtMostOneRedChild (ins a r)) := by
          by_cases hrb' : r.IsBlack
          · exact Or.inl (e3r hrb')
          · obtain ⟨p1, p2⟩ := e4r hrb'
            exact Or.inr ⟨fun hc => absurd (hnr hc).2 hrb', p1, p2⟩
        have hcl : c = .red → l.IsBlack := fun hc => (hnr hc).1
        by_cases hzr : insRotations a r = 0
        · refine ⟨?_, ?_, ?_⟩
          · rw [hzr, Nat.zero_add]; exact insertFixupRRotations_le c l (ins a r)
          · intro hne
            rw [hzr, Nat.zero_add] at hne
            rw [hins]
            exact (insertFixupRRotations_ne_zero hl_nrr hbl e2r hdisj hcl (by omega) hne).1
          · intro _ hne
            rw [hzr, Nat.zero_add] at hne
            rw [hins]
            exact (insertFixupRRotations_ne_zero hl_nrr hbl e2r hdisj hcl (by omega) hne).2
        · have hnrr_r := hne_r hzr
          rw [insertFixupRRotations_eq_zero_of_noRedRed hnrr_r, Nat.add_zero]
          rw [hins, insertFixupR_eq_of_noRedRed hnrr_r]
          refine ⟨hle_r, fun _ => ⟨fun hc => ⟨hcl hc, hib_r (hnr hc).2 hzr⟩, hl_nrr, hnrr_r⟩,
            fun hib _ => ?_⟩
          simpa [IsBlack] using hib
      · -- a = k
        refine ⟨by omega, fun h => absurd rfl h, fun _ h => absurd rfl h⟩

/-- Apply the rotation `f` to `t`, charging one tick. The counting runs `insertRot` and
`deleteRot` charge for this and for nothing else. -/
def rot (f : RBTree α → RBTree α) (t : RBTree α) : TimeM ℕ (RBTree α) := ⟨f t, 1⟩

omit [LinearOrder α] in
@[simp] theorem ret_rot (f : RBTree α → RBTree α) (t : RBTree α) : (rot f t).ret = f t := rfl

omit [LinearOrder α] in
@[simp] theorem time_rot (f : RBTree α → RBTree α) (t : RBTree α) : (rot f t).time = 1 := rfl

omit [LinearOrder α] in
/-- `insertFixupL`, with each of its rotations charged through `rot`. -/
def insertFixupLRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) : TimeM ℕ (RBTree α) :=
  match c, l with
  | .black, node .red ll _lk lr =>
      if !ll.isRed && !lr.isRed then pure (node c l k r)
      else if r.isRed then pure (node .red (blacken l) k (blacken r))
      else if lr.isRed then do
        let l' ← rot rotateLeft l
        rot rotateRight (node .red (blacken l') k r)
      else rot rotateRight (node .red (blacken l) k r)
  | _, _ => pure (node c l k r)

omit [LinearOrder α] in
/-- `insertFixupR`, with each of its rotations charged through `rot`. -/
def insertFixupRRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) : TimeM ℕ (RBTree α) :=
  match c, r with
  | .black, node .red rl _rk rr =>
      if !rl.isRed && !rr.isRed then pure (node c l k r)
      else if l.isRed then pure (node .red (blacken l) k (blacken r))
      else if rl.isRed then do
        let r' ← rot rotateRight r
        rot rotateLeft (node .red l k (blacken r'))
      else rot rotateLeft (node .red l k (blacken r))
  | _, _ => pure (node c l k r)

omit [LinearOrder α] in
theorem ret_insertFixupLRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    (insertFixupLRot c l k r).ret = insertFixupL c l k r := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;>
    simp only [insertFixupLRot, insertFixupL] <;> (try split_ifs) <;> rfl

omit [LinearOrder α] in
theorem ret_insertFixupRRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    (insertFixupRRot c l k r).ret = insertFixupR c l k r := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;>
    simp only [insertFixupRRot, insertFixupR] <;> (try split_ifs) <;> rfl

omit [LinearOrder α] in
theorem time_insertFixupLRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    (insertFixupLRot c l k r).time = insertFixupLRotations c l r := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;> cases c <;> (try cases cl) <;>
    simp only [insertFixupLRot, insertFixupLRotations] <;> (try split_ifs) <;> rfl

omit [LinearOrder α] in
theorem time_insertFixupRRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    (insertFixupRRot c l k r).time = insertFixupRRotations c l r := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> cases c <;> (try cases cr) <;>
    simp only [insertFixupRRot, insertFixupRRotations] <;> (try split_ifs) <;> rfl

/-- `ins`, charging only the rotations of each fixup on the way back up. -/
def insRot (a : α) : RBTree α → TimeM ℕ (RBTree α)
  | leaf => pure (node .red leaf a leaf)
  | node c l k r =>
      if a < k then do
        let l' ← insRot a l
        insertFixupLRot c l' k r
      else if k < a then do
        let r' ← insRot a r
        insertFixupRRot c l k r'
      else pure (node c l k r)

/-- `insert`, charging only rotations. The final `blacken` is a recoloring and costs nothing. -/
def insertRot (a : α) (t : RBTree α) : TimeM ℕ (RBTree α) := blacken <$> insRot a t

theorem ret_insRot (a : α) (t : RBTree α) : (insRot a t).ret = ins a t := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr =>
    simp only [insRot, ins]
    split_ifs <;> simp [ihl, ihr, ret_insertFixupLRot, ret_insertFixupRRot]

/-- **The count is of `insert`'s own rotations**: the counting run returns exactly `insert`'s
tree. -/
theorem ret_insertRot (a : α) (t : RBTree α) : (insertRot a t).ret = insert a t := by
  simp [insertRot, insert, ret_insRot]

theorem time_insRot (a : α) (t : RBTree α) : (insRot a t).time = insRotations a t := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr =>
    simp only [insRot, insRotations]
    split_ifs <;>
      simp [ihl, ihr, ret_insRot, time_insertFixupLRot, time_insertFixupRRot]

/-- The closed form `insRotations` is the counting run's time. -/
theorem time_insertRot (a : α) (t : RBTree α) : (insertRot a t).time = insRotations a t := by
  simp [insertRot, time_insRot]

/-- **`insert` never rotates more than twice, on a legal tree** — the payoff cited in
the Search chapter. The bound is on the time of `insertRot`, whose result is `insert`'s tree
(`ret_insertRot`); `insert`'s own final `blacken` never rotates, so this bounds `insert` as a
whole, not just `ins`. -/
theorem insert_rotations_le {t : RBTree α} (ht : Valid t) (a : α) :
    (insertRot a t).time ≤ 2 := by
  rw [time_insertRot]
  exact (insRotations_le a (blackHeightOk_iff_balanced.mp ht.2.2.2) ht.2.2.1).1

/-! ### Rotation count for `delete`

CLRS's Theorem 13.4-adjacent claim for `delete`: never more than three rotations. Unlike `insert`
(see that section), counting literal `rotateLeft`/`rotateRight` calls would *undercount*:
`deleteFixupL`'s Case 1 performs its `LEFT-ROTATE` by directly reconstructing the rotated shape
(`node .black (...) wk wr`) rather than calling `rotateLeft`, a trap flagged before any of this
was written.

As for `insert`, the count is taken on the operation itself. `deleteRot` is `delete` run in
`TimeM`, charging one tick per rotation through `rot`, and `ret_deleteRot` proves its result is
`delete`'s tree. Its Case 1 (`deleteFixupLRot`) makes the rotation literal: it recolors, calls
`rotateLeft` at this node, and runs Cases 2–4 below the new root, and `ret_deleteFixupLRot`
proves that equal to `deleteFixupL`'s fused reconstruction. `delete_rotations_le` bounds the
run's time.

The bound is proved on a closed form, `delRotations` (with `deleteFixupCase234LRotations`,
`deleteFixupLRotations`, `delMinRotations` and their `R` mirrors, Case 1 counted as `+ 1`), and
`time_deleteRot` proves the run's time equals it.

The argument this section formalizes needs none of `Balanced`/`NoRedRed`-style invariant tracking
that `insert`'s did — it is a purely syntactic fact about the code: `deleteFixupL`/`deleteFixupR`
(and, one level up, `delMin`/`del`) only ever rotate in the branches that unconditionally return
`false` (deficiency resolved) as their `Bool` half, and are only ever *called again* one level up
when that `Bool` came back `true`. So a nonzero rotation count at one level makes a rotation at any
level above it impossible by construction, without needing to know anything about the tree's
shape. -/

/-- How many rotations `deleteFixupCase234L c' x k s` makes, for *any* `c'`/`x`/`k` (none of which
the count depends on): `0` for Case 2 (recolor only) or the `s = leaf` fallback, `1` for Case 4
taken directly, `2` for Case 3's pre-rotate falling through to Case 4 (`s`'s own shape being a
node is enough to know the final `rotateLeft`/`rotateRight` call always fires in that branch — see
`deleteFixupCase234L`'s own definition). -/
def deleteFixupCase234LRotations (s : RBTree α) : ℕ :=
  match s with
  | leaf => 0
  | node _ sl _ sr => if !sl.isRed && !sr.isRed then 0 else if sr.isRed then 1 else 2

/-- Symmetric to `deleteFixupCase234LRotations`. -/
def deleteFixupCase234RRotations (s : RBTree α) : ℕ :=
  match s with
  | leaf => 0
  | node _ sl _ sr => if !sl.isRed && !sr.isRed then 0 else if sl.isRed then 1 else 2

omit [LinearOrder α] in
theorem deleteFixupCase234LRotations_le (s : RBTree α) : deleteFixupCase234LRotations s ≤ 2 := by
  cases s with
  | leaf => simp [deleteFixupCase234LRotations]
  | node _ _ _ _ => simp only [deleteFixupCase234LRotations]; split_ifs <;> omega

omit [LinearOrder α] in
theorem deleteFixupCase234RRotations_le (s : RBTree α) : deleteFixupCase234RRotations s ≤ 2 := by
  cases s with
  | leaf => simp [deleteFixupCase234RRotations]
  | node _ _ _ _ => simp only [deleteFixupCase234RRotations]; split_ifs <;> omega

omit [LinearOrder α] in
/-- **Case 2 is the only zero-rotation branch, and it's the only branch that can leave the
deficiency alive** (its own `Bool` half is `c' = .black`, which can go either way; every other
branch's `Bool` half is the literal `false`). So whenever this call actually rotated, the
deficiency is gone — read directly off `deleteFixupCase234L`'s own definition, no invariant about
the tree needed. -/
theorem deleteFixupCase234L_ne_zero_resolves {c' : Color} {x : RBTree α} {k : α} {s : RBTree α}
    (hne : deleteFixupCase234LRotations s ≠ 0) : (deleteFixupCase234L c' x k s).2 = false := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · exact absurd rfl hne
  · rcases sl with _ | ⟨csl, sll, slk, slr⟩ <;> rcases sr with _ | ⟨csr, srl, srk, srr⟩ <;>
      (try cases csl) <;> (try cases csr) <;>
      simp_all [deleteFixupCase234LRotations, deleteFixupCase234L, isRed, rotateRight, blacken]

omit [LinearOrder α] in
theorem deleteFixupCase234R_ne_zero_resolves {c' : Color} {k : α} {x s : RBTree α}
    (hne : deleteFixupCase234RRotations s ≠ 0) : (deleteFixupCase234R c' k x s).2 = false := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · exact absurd rfl hne
  · rcases sl with _ | ⟨csl, sll, slk, slr⟩ <;> rcases sr with _ | ⟨csr, srl, srk, srr⟩ <;>
      (try cases csl) <;> (try cases csr) <;>
      simp_all [deleteFixupCase234RRotations, deleteFixupCase234R, isRed, rotateLeft, blacken]

/-- Mirrors `deleteFixupL`'s own case split: Case 1 (`w` red) adds its fused rotation (`+ 1`) on
top of the recursive `deleteFixupCase234L` call on `wl` (not `w` — Case 1 hands the sibling's own
left child down, per `deleteFixupL`'s definition); every other case calls
`deleteFixupCase234LRotations` on `w` itself. -/
def deleteFixupLRotations (w : RBTree α) : ℕ :=
  match w with
  | node .red wl _ _ => 1 + deleteFixupCase234LRotations wl
  | _ => deleteFixupCase234LRotations w

/-- Symmetric to `deleteFixupLRotations`. -/
def deleteFixupRRotations (w : RBTree α) : ℕ :=
  match w with
  | node .red _ _ wr => 1 + deleteFixupCase234RRotations wr
  | _ => deleteFixupCase234RRotations w

omit [LinearOrder α] in
/-- **A single `deleteFixupL` call rotates at most three times** — `1` (Case 1's fused rotation,
when it fires) plus `deleteFixupCase234LRotations`'s own `≤ 2`. True in isolation, no invariant
needed, matching `insertFixupLRotations_le`'s role for `insert`. -/
theorem deleteFixupLRotations_le (w : RBTree α) : deleteFixupLRotations w ≤ 3 := by
  cases w with
  | leaf => simp [deleteFixupLRotations, deleteFixupCase234LRotations]
  | node c wl wk wr =>
    cases c with
    | red =>
      have := deleteFixupCase234LRotations_le wl
      simp only [deleteFixupLRotations]
      omega
    | black =>
      have := deleteFixupCase234LRotations_le (node Color.black wl wk wr)
      simp only [deleteFixupLRotations]
      omega

omit [LinearOrder α] in
theorem deleteFixupRRotations_le (w : RBTree α) : deleteFixupRRotations w ≤ 3 := by
  cases w with
  | leaf => simp [deleteFixupRRotations, deleteFixupCase234RRotations]
  | node c wl wk wr =>
    cases c with
    | red =>
      have := deleteFixupCase234RRotations_le wr
      simp only [deleteFixupRRotations]
      omega
    | black =>
      have := deleteFixupCase234RRotations_le (node Color.black wl wk wr)
      simp only [deleteFixupRRotations]
      omega

omit [LinearOrder α] in
/-- **Whenever `deleteFixupL` actually rotates, the deficiency is resolved** — Case 1 always
returns `false` regardless of what its inner `deleteFixupCase234L` call does (it hardcodes `c' :=
.red`, so that call's own `c' = .black` branch, the only one that could still return `true`, can
never fire); every other case defers straight to `deleteFixupCase234L_ne_zero_resolves`. This is
the fact that plays `insertFixupLRotations_eq_zero_of_noRedRed`'s role for `delete`: it is what
keeps a second rotation from ever firing one level up, and unlike `insert`'s version, it needs no
hypothesis about the tree at all. -/
theorem deleteFixupL_ne_zero_resolves {c : Color} {x : RBTree α} {k : α} {w : RBTree α}
    (hne : deleteFixupLRotations w ≠ 0) : (deleteFixupL c x k w).2 = false := by
  cases w with
  | leaf => exact absurd rfl hne
  | node cw wl wk wr =>
    cases cw with
    | red => rfl
    | black => exact deleteFixupCase234L_ne_zero_resolves hne

omit [LinearOrder α] in
theorem deleteFixupR_ne_zero_resolves {c : Color} {w : RBTree α} {k : α} {x : RBTree α}
    (hne : deleteFixupRRotations w ≠ 0) : (deleteFixupR c w k x).2 = false := by
  cases w with
  | leaf => exact absurd rfl hne
  | node cw wl wk wr =>
    cases cw with
    | red => rfl
    | black => exact deleteFixupCase234R_ne_zero_resolves hne

/-- Mirrors `delMin`'s own recursion: `0` at a leaf-left base case (no fixup call at all — see
`delMin`'s own base case, which only ever transplants or recolors, never rotates), otherwise the
recursive count plus (only when the recursive call came back deficient) whatever
`deleteFixupLRotations` adds. -/
def delMinRotations (_c : Color) (l : RBTree α) (_k : α) (r : RBTree α) : ℕ :=
  match l with
  | leaf => 0
  | node cl ll lk lr =>
      let (_, deficient, _) := delMin cl ll lk lr
      delMinRotations cl ll lk lr + if deficient then deleteFixupLRotations r else 0

omit [LinearOrder α] in
/-- **`delMin` never rotates more than three times, and whenever it actually rotates, the
deficiency is resolved.** Proved together, by induction, using exactly the same "at most one
level in the whole chain can rotate" argument as `deleteFixupL_ne_zero_resolves` supplies: if the
recursive call already rotated, it already resolved the deficiency (so *this* level's own
`deleteFixupL` call never even fires, and the deficiency it would have needed stays resolved); if
it didn't, this level contributes at most `deleteFixupLRotations_le`'s own bound on its own, and
resolves things itself exactly when it rotates. -/
theorem delMinRotations_spec (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    delMinRotations c l k r ≤ 3 ∧
    (delMinRotations c l k r ≠ 0 → (delMin c l k r).2.1 = false) := by
  induction l generalizing c k r with
  | leaf => simp [delMinRotations, delMin]
  | node cl ll lk lr ih =>
    obtain ⟨hle, hres⟩ := ih (c := cl) (k := lk) (r := lr)
    rcases hd : delMin cl ll lk lr with ⟨l', deficient, m⟩
    have hrot : delMinRotations c (node cl ll lk lr) k r =
        delMinRotations cl ll lk lr + if deficient then deleteFixupLRotations r else 0 := by
      simp only [delMinRotations, hd]
    have hdef' : (delMin c (node cl ll lk lr) k r).2.1 =
        if deficient then (deleteFixupL c l' k r).2 else false := by
      simp only [delMin, hd]
      cases deficient <;> simp
    simp only [hd] at hres
    rw [hrot]
    by_cases hz : delMinRotations cl ll lk lr = 0
    · rw [hz, Nat.zero_add]
      by_cases hdc : deficient
      · rw [ite_eq_left hdc]
        refine ⟨deleteFixupLRotations_le r, fun hne => ?_⟩
        rw [hdef', ite_eq_left hdc]
        exact deleteFixupL_ne_zero_resolves hne
      · rw [ite_eq_right hdc]
        simp
    · have hdf := hres hz
      rw [ite_eq_right (by simp [hdf])]
      refine ⟨by omega, fun _ => ?_⟩
      rw [hdef', ite_eq_right (by simp [hdf])]

/-- Mirrors `del`'s own case split. The two-children case delegates to `delMinRotations` on `r`'s
structure (`del` calls `delMin` there, not a recursive `del`), matching `del`'s own use of `m`
(the removed minimum) only as the new separating key, never touched by rotation bookkeeping. -/
def delRotations (a : α) : RBTree α → ℕ
  | leaf => 0
  | node _c l k r =>
      if a < k then delRotations a l + if (del a l).2 then deleteFixupLRotations r else 0
      else if k < a then delRotations a r + if (del a r).2 then deleteFixupRRotations l else 0
      else
        match l with
        | leaf => 0
        | node _ _ _ _ =>
            match r with
            | leaf => 0
            | node cr rl rk rr =>
                delMinRotations cr rl rk rr +
                  if (delMin cr rl rk rr).2.1 then deleteFixupRRotations l else 0

/-- **`delete` never rotates more than three times.** The rotation-count analogue of `del_spec`,
proved the same way `delMinRotations_spec` was: no `Balanced`/`NoRedRed` tracking needed, only the
syntactic "rotate ⟹ resolved" facts (`deleteFixupL_ne_zero_resolves`/`deleteFixupR_ne_zero_resolves`
directly; `delMinRotations_spec`'s own resolves-half for the two-children case) applied at
whichever single level in the recursion actually does the rotating. -/
theorem delRotations_spec (a : α) (t : RBTree α) :
    delRotations a t ≤ 3 ∧ (delRotations a t ≠ 0 → (del a t).2 = false) := by
  induction t with
  | leaf => simp [delRotations, del]
  | node c l k r ihl ihr =>
    unfold delRotations
    simp only [del]
    split
    · rename_i hak
      rcases hdl : del a l with ⟨l', deficient⟩
      obtain ⟨hle_l, hres_l⟩ := ihl
      simp only [hdl] at hres_l
      by_cases hz : delRotations a l = 0
      · rw [hz, Nat.zero_add]
        cases deficient with
        | true =>
          refine ⟨deleteFixupLRotations_le r, fun hne => deleteFixupL_ne_zero_resolves hne⟩
        | false => simp
      · have hdf := hres_l hz
        rw [ite_eq_right (by simp [hdf]), Nat.add_zero]
        exact ⟨hle_l, fun _ => by simp [hdf]⟩
    · split
      · rename_i hnak hka
        rcases hdr : del a r with ⟨r', deficient⟩
        obtain ⟨hle_r, hres_r⟩ := ihr
        simp only [hdr] at hres_r
        by_cases hz : delRotations a r = 0
        · rw [hz, Nat.zero_add]
          cases deficient with
          | true =>
            refine ⟨deleteFixupRRotations_le l, fun hne => deleteFixupR_ne_zero_resolves hne⟩
          | false => simp
        · have hdf := hres_r hz
          rw [ite_eq_right (by simp [hdf]), Nat.add_zero]
          exact ⟨hle_r, fun _ => by simp [hdf]⟩
      · rename_i hnak hnka
        cases hl : l with
        | leaf => simp
        | node cl ll lk lr =>
          cases hr : r with
          | leaf => simp
          | node cr rl rk rr =>
            simp only
            rcases hdm : delMin cr rl rk rr with ⟨r'', deficient, m⟩
            simp only
            obtain ⟨hle_dm, hres_dm⟩ := delMinRotations_spec cr rl rk rr
            simp only [hdm] at hres_dm
            by_cases hz : delMinRotations cr rl rk rr = 0
            · rw [hz, Nat.zero_add]
              cases deficient with
              | true =>
                refine ⟨deleteFixupRRotations_le (node cl ll lk lr),
                  fun hne => deleteFixupR_ne_zero_resolves hne⟩
              | false => simp
            · have hdf := hres_dm hz
              rw [ite_eq_right (by simp [hdf]), Nat.add_zero]
              exact ⟨hle_dm, fun _ => by simp [hdf]⟩

omit [LinearOrder α] in
/-- `deleteFixupCase234L`, with Case 3's and Case 4's rotations charged through `rot`. -/
def deleteFixupCase234LRot (c' : Color) (x : RBTree α) (k : α) (s : RBTree α) :
    TimeM ℕ (RBTree α × Bool) :=
  match s with
  | leaf => pure (node c' x k leaf, false)
  | node _ sl sk sr =>
      if !sl.isRed && !sr.isRed then
        pure (node .black x k (node .red sl sk sr), c' = .black)
      else do
        let s' ← if sr.isRed then pure s else rot rotateRight (node .red (blacken sl) sk sr)
        match s' with
        | node _ s'l s'k s'r => do
            let t ← rot rotateLeft (node .black x k (node c' s'l s'k (blacken s'r)))
            pure (t, false)
        | leaf => pure (node c' x k leaf, false)

omit [LinearOrder α] in
/-- Mirror of `deleteFixupCase234LRot`. -/
def deleteFixupCase234RRot (c' : Color) (k : α) (x s : RBTree α) : TimeM ℕ (RBTree α × Bool) :=
  match s with
  | leaf => pure (node c' leaf k x, false)
  | node _ sl sk sr =>
      if !sl.isRed && !sr.isRed then
        pure (node .black (node .red sl sk sr) k x, c' = .black)
      else do
        let s' ← if sl.isRed then pure s else rot rotateLeft (node .red sl sk (blacken sr))
        match s' with
        | node _ s'l s'k s'r => do
            let t ← rot rotateRight (node .black (node c' (blacken s'l) s'k s'r) k x)
            pure (t, false)
        | leaf => pure (node c' leaf k x, false)

omit [LinearOrder α] in
/-- `deleteFixupL` with its rotations charged. Case 1 is written the way CLRS writes it: recolor
(`w` black, this node red), `LEFT-ROTATE` at this node, then run Cases 2–4 on the new left child,
whose sibling is `w`'s old left child. The last arm is unreachable: `rotateLeft` of a node with a
right child always has this shape. `ret_deleteFixupLRot` proves the result is `deleteFixupL`'s. -/
def deleteFixupLRot (c : Color) (x : RBTree α) (k : α) (w : RBTree α) :
    TimeM ℕ (RBTree α × Bool) :=
  match w with
  | node .red wl wk wr => do
      let t ← rot rotateLeft (node .red x k (node .black wl wk wr))
      match t with
      | node ct (node _ x' k' s) kt rt => do
          let r ← deleteFixupCase234LRot .red x' k' s
          pure (node ct r.1 kt rt, false)
      | t => pure (t, false)
  | _ => deleteFixupCase234LRot c x k w

omit [LinearOrder α] in
/-- Mirror of `deleteFixupLRot`: Case 1 is `RIGHT-ROTATE` at this node. -/
def deleteFixupRRot (c : Color) (w : RBTree α) (k : α) (x : RBTree α) :
    TimeM ℕ (RBTree α × Bool) :=
  match w with
  | node .red wl wk wr => do
      let t ← rot rotateRight (node .red (node .black wl wk wr) k x)
      match t with
      | node ct lt kt (node _ s k' x') => do
          let r ← deleteFixupCase234RRot .red k' x' s
          pure (node ct lt kt r.1, false)
      | t => pure (t, false)
  | _ => deleteFixupCase234RRot c k x w

omit [LinearOrder α] in
theorem ret_deleteFixupCase234LRot (c' : Color) (x : RBTree α) (k : α) (s : RBTree α) :
    (deleteFixupCase234LRot c' x k s).ret = deleteFixupCase234L c' x k s := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · rfl
  · rcases sl with _ | ⟨csl, sll, slk, slr⟩ <;> rcases sr with _ | ⟨csr, srl, srk, srr⟩ <;>
      (try cases csl) <;> (try cases csr) <;> rfl

omit [LinearOrder α] in
theorem ret_deleteFixupCase234RRot (c' : Color) (k : α) (x s : RBTree α) :
    (deleteFixupCase234RRot c' k x s).ret = deleteFixupCase234R c' k x s := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · rfl
  · rcases sl with _ | ⟨csl, sll, slk, slr⟩ <;> rcases sr with _ | ⟨csr, srl, srk, srr⟩ <;>
      (try cases csl) <;> (try cases csr) <;> rfl

omit [LinearOrder α] in
theorem time_deleteFixupCase234LRot (c' : Color) (x : RBTree α) (k : α) (s : RBTree α) :
    (deleteFixupCase234LRot c' x k s).time = deleteFixupCase234LRotations s := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · rfl
  · rcases sl with _ | ⟨csl, sll, slk, slr⟩ <;> rcases sr with _ | ⟨csr, srl, srk, srr⟩ <;>
      (try cases csl) <;> (try cases csr) <;> rfl

omit [LinearOrder α] in
theorem time_deleteFixupCase234RRot (c' : Color) (k : α) (x s : RBTree α) :
    (deleteFixupCase234RRot c' k x s).time = deleteFixupCase234RRotations s := by
  rcases s with _ | ⟨cs, sl, sk, sr⟩
  · rfl
  · rcases sl with _ | ⟨csl, sll, slk, slr⟩ <;> rcases sr with _ | ⟨csr, srl, srk, srr⟩ <;>
      (try cases csl) <;> (try cases csr) <;> rfl

omit [LinearOrder α] in
theorem ret_deleteFixupLRot (c : Color) (x : RBTree α) (k : α) (w : RBTree α) :
    (deleteFixupLRot c x k w).ret = deleteFixupL c x k w := by
  rcases w with _ | ⟨_ | _, wl, wk, wr⟩
  · exact ret_deleteFixupCase234LRot c x k leaf
  · simp [deleteFixupLRot, deleteFixupL, rotateLeft, ret_deleteFixupCase234LRot]
  · exact ret_deleteFixupCase234LRot c x k _

omit [LinearOrder α] in
theorem ret_deleteFixupRRot (c : Color) (w : RBTree α) (k : α) (x : RBTree α) :
    (deleteFixupRRot c w k x).ret = deleteFixupR c w k x := by
  rcases w with _ | ⟨_ | _, wl, wk, wr⟩
  · exact ret_deleteFixupCase234RRot c k x leaf
  · simp [deleteFixupRRot, deleteFixupR, rotateRight, ret_deleteFixupCase234RRot]
  · exact ret_deleteFixupCase234RRot c k x _

omit [LinearOrder α] in
theorem time_deleteFixupLRot (c : Color) (x : RBTree α) (k : α) (w : RBTree α) :
    (deleteFixupLRot c x k w).time = deleteFixupLRotations w := by
  rcases w with _ | ⟨_ | _, wl, wk, wr⟩
  · exact time_deleteFixupCase234LRot c x k leaf
  · simp [deleteFixupLRot, deleteFixupLRotations, rotateLeft, time_deleteFixupCase234LRot]
  · exact time_deleteFixupCase234LRot c x k _

omit [LinearOrder α] in
theorem time_deleteFixupRRot (c : Color) (w : RBTree α) (k : α) (x : RBTree α) :
    (deleteFixupRRot c w k x).time = deleteFixupRRotations w := by
  rcases w with _ | ⟨_ | _, wl, wk, wr⟩
  · exact time_deleteFixupCase234RRot c k x leaf
  · simp [deleteFixupRRot, deleteFixupRRotations, rotateRight, time_deleteFixupCase234RRot]
  · exact time_deleteFixupCase234RRot c k x _

omit [LinearOrder α] in
/-- `delMin`, charging only the rotations of each fixup on the way back up. -/
def delMinRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) : TimeM ℕ (RBTree α × Bool × α) :=
  match l with
  | leaf =>
      pure (match c, r with
        | .red, _ => (r, false, k)
        | .black, leaf => (leaf, true, k)
        | .black, node _ rl rk rr => (node .black rl rk rr, false, k))
  | node cl ll lk lr => do
      let (l', deficient, m) ← delMinRot cl ll lk lr
      if deficient then do
        let (t', d') ← deleteFixupLRot c l' k r
        pure (t', d', m)
      else pure (node c l' k r, false, m)

omit [LinearOrder α] in
theorem ret_delMinRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    (delMinRot c l k r).ret = delMin c l k r := by
  induction l generalizing c k r with
  | leaf => rfl
  | node cl ll lk lr ih =>
    have h := ih cl lk lr
    rcases hd : delMinRot cl ll lk lr with ⟨⟨l', d, m⟩, n⟩
    rw [hd] at h
    simp only [delMinRot, delMin, hd, ← h, ret_bind]
    cases d <;> simp [ret_deleteFixupLRot]

omit [LinearOrder α] in
theorem time_delMinRot (c : Color) (l : RBTree α) (k : α) (r : RBTree α) :
    (delMinRot c l k r).time = delMinRotations c l k r := by
  induction l generalizing c k r with
  | leaf => rfl
  | node cl ll lk lr ih =>
    have h := ih cl lk lr
    have hr := ret_delMinRot cl ll lk lr
    rcases hd : delMinRot cl ll lk lr with ⟨⟨l', d, m⟩, n⟩
    rw [hd] at h hr
    simp only [delMinRot, delMinRotations, hd, ← h, ← hr, time_bind]
    cases d <;> simp [time_deleteFixupLRot]

/-- `del`, charging only rotations. -/
def delRot (a : α) : RBTree α → TimeM ℕ (RBTree α × Bool)
  | leaf => pure (leaf, false)
  | node c l k r =>
      if a < k then do
        let (l', deficient) ← delRot a l
        if deficient then deleteFixupLRot c l' k r else pure (node c l' k r, false)
      else if k < a then do
        let (r', deficient) ← delRot a r
        if deficient then deleteFixupRRot c l k r' else pure (node c l k r', false)
      else
        match l with
        | leaf =>
            pure (match c, r with
              | .red, _ => (r, false)
              | .black, leaf => (leaf, true)
              | .black, node _ rl rk rr => (node .black rl rk rr, false))
        | node cl ll lk lr =>
            match r with
            | leaf =>
                pure (match c with
                  | .red => (l, false)
                  | .black => (node .black ll lk lr, false))
            | node cr rl rk rr => do
                let (r', deficient, m) ← delMinRot cr rl rk rr
                if deficient then deleteFixupRRot c l m r'
                else pure (node c (node cl ll lk lr) m r', false)

/-- `delete`, charging only rotations. -/
def deleteRot (a : α) (t : RBTree α) : TimeM ℕ (RBTree α) := Prod.fst <$> delRot a t

theorem ret_delRot (a : α) (t : RBTree α) : (delRot a t).ret = del a t := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr =>
    by_cases h1 : a < k
    · simp only [delRot, del, h1, ↓reduceIte]
      rcases hd : delRot a l with ⟨⟨l', d⟩, n⟩
      rw [hd] at ihl
      simp only [ret_bind, ← ihl]
      cases d <;> simp [ret_deleteFixupLRot]
    by_cases h2 : k < a
    · simp only [delRot, del, h1, h2, ↓reduceIte]
      rcases hd : delRot a r with ⟨⟨r', d⟩, n⟩
      rw [hd] at ihr
      simp only [ret_bind, ← ihr]
      cases d <;> simp [ret_deleteFixupRRot]
    simp only [delRot, del, h1, h2, ↓reduceIte]
    rcases l with _ | ⟨cl, ll, lk, lr⟩
    · rfl
    · rcases r with _ | ⟨cr, rl, rk, rr⟩
      · rfl
      · have h := ret_delMinRot cr rl rk rr
        rcases hd : delMinRot cr rl rk rr with ⟨⟨r', d, m⟩, n⟩
        rw [hd] at h
        simp only [ret_bind, hd, ← h]
        cases d <;> simp [ret_deleteFixupRRot]

/-- **The count is of `delete`'s own rotations**: the counting run returns exactly `delete`'s
tree. -/
theorem ret_deleteRot (a : α) (t : RBTree α) : (deleteRot a t).ret = delete a t := by
  simp [deleteRot, delete, ret_delRot]

theorem time_delRot (a : α) (t : RBTree α) : (delRot a t).time = delRotations a t := by
  induction t with
  | leaf => rfl
  | node c l k r ihl ihr =>
    by_cases h1 : a < k
    · simp only [delRot, delRotations, h1, ↓reduceIte]
      have hr := ret_delRot a l
      rcases hd : delRot a l with ⟨⟨l', d⟩, n⟩
      rw [hd] at ihl hr
      simp only [time_bind, ← ihl, ← hr]
      cases d <;> simp [time_deleteFixupLRot]
    by_cases h2 : k < a
    · simp only [delRot, delRotations, h1, h2, ↓reduceIte]
      have hr := ret_delRot a r
      rcases hd : delRot a r with ⟨⟨r', d⟩, n⟩
      rw [hd] at ihr hr
      simp only [time_bind, ← ihr, ← hr]
      cases d <;> simp [time_deleteFixupRRot]
    simp only [delRot, delRotations, h1, h2, ↓reduceIte]
    rcases l with _ | ⟨cl, ll, lk, lr⟩
    · rfl
    · rcases r with _ | ⟨cr, rl, rk, rr⟩
      · rfl
      · have h := time_delMinRot cr rl rk rr
        have hr := ret_delMinRot cr rl rk rr
        rcases hd : delMinRot cr rl rk rr with ⟨⟨r', d, m⟩, n⟩
        rw [hd] at h hr
        simp only [time_bind, hd, ← h, ← hr]
        cases d <;> simp [time_deleteFixupRRot]

/-- The closed form `delRotations` is the counting run's time. -/
theorem time_deleteRot (a : α) (t : RBTree α) : (deleteRot a t).time = delRotations a t := by
  simp [deleteRot, time_delRot]

/-- **`delete` never rotates more than three times, on *any* tree.** The bound is on the time of
`deleteRot`, whose result is `delete`'s tree (`ret_deleteRot`). Unlike `insert`'s bound it needs
no hypothesis: the argument never uses `Balanced`/`NoRedRed` (see this section's docstring). -/
theorem delete_rotations_le (t : RBTree α) (a : α) : (deleteRot a t).time ≤ 3 := by
  rw [time_deleteRot]
  exact (delRotations_spec a t).1

end RBTree

end AlgoDesign.Searching
