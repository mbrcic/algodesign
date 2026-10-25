/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Delete.Algorithm

/-!
# LLRB deletion: `deleteMin`

`deleteMin_spec` and `valid_deleteMin`: `deleteMin` preserves every invariant, given
`NotTwoNode`; `mem_deleteMin_iff`: it removes exactly the minimum. Also what `moveRedLeft` and
`moveRedRight` preserve, which general deletion reuses.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-! ### `moveRedLeft`/`moveRedRight` preserve `Mem`/`Sorted`

Color-blind stage, same split as `insert`'s: neither operation is anything but a `flipColors`
composed with (possibly) a `rotateLeft`/`rotateRight`, so `Mem`/`Sorted` transfer straight through
from the already-proved rotation/flip lemmas. -/

omit [LinearOrder α] in
/-- A `Mem`-preserving rebuild of a tree preserves any `All p` fact about it — the general
principle `sorted_moveRedLeft` below instantiates for `rotateRight` acting on just the *right*
subtree of an otherwise-untouched node. -/
theorem all_of_mem_iff {p : α → Prop} {t t' : LLRB α} (h : ∀ b, Mem b t' ↔ Mem b t)
    (ha : All p t) : All p t' :=
  all_of_forall_mem fun b hb => ha.of_mem ((h b).mp hb)

theorem sorted_node_right_rotateRight {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    (h : Sorted (node c l k r)) : Sorted (node c l k (rotateRight r)) :=
  ⟨h.1, all_of_mem_iff (mem_rotateRight r) h.2.1, h.2.2.1, sorted_rotateRight h.2.2.2⟩

omit [LinearOrder α] in
theorem mem_moveRedLeft (t : LLRB α) (b : α) : Mem b (moveRedLeft t) ↔ Mem b t := by
  have hft := mem_flipColors t b
  simp only [moveRedLeft]
  split_ifs with h
  · rcases ht : flipColors t with _ | ⟨c, l, k, r⟩
    · rw [ht] at hft; simpa [ht] using hft
    · rw [ht] at hft
      simp only [mem_flipColors, mem_rotateLeft, mem_node, mem_rotateRight]
      tauto
  · exact hft

omit [LinearOrder α] in
theorem mem_moveRedRight (t : LLRB α) (b : α) : Mem b (moveRedRight t) ↔ Mem b t := by
  simp only [moveRedRight]
  split_ifs with h <;> simp [mem_flipColors, mem_rotateRight]

theorem sorted_moveRedLeft {t : LLRB α} (ht : Sorted t) : Sorted (moveRedLeft t) := by
  simp only [moveRedLeft]
  split_ifs with h
  · rcases hft : flipColors t with _ | ⟨c, l, k, r⟩
    · trivial
    · have hs : Sorted (node c l k r) := hft ▸ sorted_flipColors ht
      exact sorted_flipColors (sorted_rotateLeft (sorted_node_right_rotateRight hs))
  · exact sorted_flipColors ht

theorem sorted_moveRedRight {t : LLRB α} (ht : Sorted t) : Sorted (moveRedRight t) := by
  simp only [moveRedRight]
  split_ifs with h
  · exact sorted_flipColors (sorted_rotateRight (sorted_flipColors ht))
  · exact sorted_flipColors ht

theorem min?_moveRedLeft {t : LLRB α} (ht : Sorted t) : min? (moveRedLeft t) = min? t := by
  cases hm : min? t with
  | none =>
    cases t with
    | leaf => simp [moveRedLeft, flipColors, left, right, isRed]
    | node _ _ _ _ => simp [min?] at hm
  | some m =>
    obtain ⟨hmem, hle⟩ := min?_correct ht hm
    have hsorted := sorted_moveRedLeft ht
    have hmem' : Mem m (moveRedLeft t) := (mem_moveRedLeft t m).mpr hmem
    have hle' : All (m ≤ ·) (moveRedLeft t) := all_of_forall_mem fun b hb =>
      hle.of_mem ((mem_moveRedLeft t b).mp hb)
    cases hm' : min? (moveRedLeft t) with
    | none =>
      match hleft : moveRedLeft t with
      | leaf =>
        have : Mem m (leaf : LLRB α) := hleft ▸ hmem'
        exact this.elim
      | node _ _ _ _ =>
        rw [hleft] at hm'
        simp [min?] at hm'
    | some m' =>
      obtain ⟨hmemm', hle'm'⟩ := min?_correct hsorted hm'
      have h1 : m ≤ m' := hle'.of_mem hmemm'
      have h2 : m' ≤ m := hle'm'.of_mem hmem'
      exact congrArg some (le_antisymm h2 h1)

/-! ### Deletion helper invariants

`NotTwoNode` describes a spare red link in a left-leaning tree. It is the precondition maintained
by the `deleteMin` proof. It does not describe every intermediate state of general deletion:
`moveRedRight` may produce a right child with a temporary red right link, as recorded by its
separate contract below. -/

/-- A spare red link: the root is red, or its left child is. -/
def NotTwoNode (t : LLRB α) : Prop := t.IsRed ∨ t.left.IsRed

omit [LinearOrder α] in
/-- Under `NotTwoNode`, a node whose left child *isn't* red must itself carry a red link — the
whole reason `NotTwoNode` is useful: it pins `c` down before `moveRedLeft`/`moveRedRight`'s case
analysis even starts, in both directions (`deleteMin`/`delete`'s "go left" branch reads it off `l`
directly; the "go right" branch gets it the same way, since the preliminary `rotateRight` there
only ever fires when `l.IsRed`, i.e. exactly the case this lemma doesn't need). -/
theorem isRed_of_notTwoNode {c : Color} {l : LLRB α} {k : α} {r : LLRB α}
    (hntn : NotTwoNode (node c l k r)) (hl : ¬ l.IsRed) : c = .red := by
  rcases hntn with h | h
  · exact h
  · exact absurd h hl

omit [LinearOrder α] in
/-- `moveRedLeft`'s effect on its only intended input shape (`deleteMin`/`delete`'s own guard
before calling it): `h`'s left child `node .black ll lk lr` is a bare 2-node (`hll`; `h` itself is
baked in as red here, rather than carried as a hypothesis, since that's what `isRed_of_notTwoNode`
+ the guard always forces it to be at every real call site, and fixing it up front cuts the case
count sharply).

The conclusion does **not** claim the raw output is `LeftLeaning`/`NoRedRed` as a *whole tree* —
it genuinely isn't: Case A (the sibling has no spare red grandchild to further rebalance around)
leaves the output's own right child red, a deliberate, temporary `LeftLeaning` violation that
`fixUp` (run by the caller, one level up, *after* the recursive call into the new left child) is
responsible for cleaning up. What `deleteMin_spec` needs: the
output's own left and right children are each individually fully valid and equal-`bheight`, the
whole tree's `bheight` is unchanged, `NotTwoNode` holds of the new left child (safe to recurse
into), and if the output's own link is red, its right child specifically isn't (feeds
`fixUp_left_spec'`'s `hcr` directly). -/
theorem moveRedLeft_spec {ll lr r : LLRB α} {k lk : α}
    (ht_ll : LeftLeaning (node .red (node .black ll lk lr) k r))
    (ht_nrr : NoRedRed (node .red (node .black ll lk lr) k r))
    (ht_bal : Balanced (node .red (node .black ll lk lr) k r))
    (hll : ¬ ll.IsRed) :
    LeftLeaning (moveRedLeft (node .red (node .black ll lk lr) k r)).left ∧
    NoRedRed (moveRedLeft (node .red (node .black ll lk lr) k r)).left ∧
    Balanced (moveRedLeft (node .red (node .black ll lk lr) k r)).left ∧
    LeftLeaning (moveRedLeft (node .red (node .black ll lk lr) k r)).right ∧
    NoRedRed (moveRedLeft (node .red (node .black ll lk lr) k r)).right ∧
    Balanced (moveRedLeft (node .red (node .black ll lk lr) k r)).right ∧
    bheight (moveRedLeft (node .red (node .black ll lk lr) k r)).left =
      bheight (moveRedLeft (node .red (node .black ll lk lr) k r)).right ∧
    ((moveRedLeft (node .red (node .black ll lk lr) k r)).IsRed →
      ¬ (moveRedLeft (node .red (node .black ll lk lr) k r)).right.IsRed) ∧
    ((moveRedLeft (node .red (node .black ll lk lr) k r)).IsRed →
      ¬ (moveRedLeft (node .red (node .black ll lk lr) k r)).left.IsRed) ∧
    bheight (moveRedLeft (node .red (node .black ll lk lr) k r)) =
      bheight (node .red (node .black ll lk lr) k r) ∧
    NotTwoNode (moveRedLeft (node .red (node .black ll lk lr) k r)).left := by
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;>
    (try rcases rl with _ | ⟨crl, rll, rlk, rlr⟩) <;> (try cases cr) <;> (try cases crl) <;>
    (try have := bheight_pos ll) <;> (try have := bheight_pos lr) <;>
    (try have := bheight_pos rr) <;> (try have := bheight_pos rll) <;>
    (try have := bheight_pos rlr) <;>
    simp_all [moveRedLeft, flipColors, rotateLeft, rotateRight, Color.flip, isRed, left, right,
      NotTwoNode, LeftLeaning, NoRedRed, IsRed, bheight, Balanced] <;> omega

/-- A deletion intermediate may have a red link on either side of its root. Its children
remain left-leaning. This predicate does not replace `LeftLeaning` for completed trees. -/
def LeftLeaningBelowRoot (t : LLRB α) : Prop :=
  LeftLeaning t.left ∧ LeftLeaning t.right

/-- A deletion intermediate has a spare red link at its root or either child. -/
def NotTwoNodeEither (t : LLRB α) : Prop :=
  t.IsRed ∨ t.left.IsRed ∨ t.right.IsRed

omit [LinearOrder α] in
/-- `moveRedRight` preserves black balance and clean red links in both children. The right
child can temporarily lean right after borrowing, so its contract permits either orientation
at that child's root. The final deletion result must still satisfy `LeftLeaning`. -/
theorem moveRedRight_spec {l rl rr : LLRB α} {k rk : α}
    (ht_ll : LeftLeaning (node .red l k (node .black rl rk rr)))
    (ht_nrr : NoRedRed (node .red l k (node .black rl rk rr)))
    (ht_bal : Balanced (node .red l k (node .black rl rk rr)))
    (hrl : ¬ rl.IsRed) :
    LeftLeaning (moveRedRight (node .red l k (node .black rl rk rr))).left ∧
    NoRedRed (moveRedRight (node .red l k (node .black rl rk rr))).left ∧
    Balanced (moveRedRight (node .red l k (node .black rl rk rr))).left ∧
    LeftLeaningBelowRoot (moveRedRight (node .red l k (node .black rl rk rr))).right ∧
    NoRedRed (moveRedRight (node .red l k (node .black rl rk rr))).right ∧
    Balanced (moveRedRight (node .red l k (node .black rl rk rr))).right ∧
    bheight (moveRedRight (node .red l k (node .black rl rk rr))).left =
      bheight (moveRedRight (node .red l k (node .black rl rk rr))).right ∧
    ((moveRedRight (node .red l k (node .black rl rk rr))).IsRed →
      ¬ (moveRedRight (node .red l k (node .black rl rk rr))).right.IsRed) ∧
    bheight (moveRedRight (node .red l k (node .black rl rk rr))) =
      bheight (node .red l k (node .black rl rk rr)) ∧
    NotTwoNodeEither (moveRedRight (node .red l k (node .black rl rk rr))).right := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;>
    (try rcases ll with _ | ⟨cll, lll, llk, llr⟩) <;> (try cases cl) <;> (try cases cll) <;>
    (try have := bheight_pos rl) <;> (try have := bheight_pos rr) <;>
    (try have := bheight_pos lr) <;> (try have := bheight_pos lll) <;>
    (try have := bheight_pos llr) <;>
    simp_all [moveRedRight, flipColors, rotateRight, Color.flip, isRed, left, right,
      NotTwoNodeEither, LeftLeaningBelowRoot, LeftLeaning, NoRedRed, IsRed, bheight, Balanced] <;>
    omega

omit [LinearOrder α] in
theorem rotateLeft_eq_leaf_iff {t : LLRB α} : rotateLeft t = leaf ↔ t = leaf := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [rotateLeft]

omit [LinearOrder α] in
theorem rotateRight_eq_leaf_iff {t : LLRB α} : rotateRight t = leaf ↔ t = leaf := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩ <;> simp [rotateRight]

omit [LinearOrder α] in
theorem flipColors_eq_leaf_iff {t : LLRB α} : flipColors t = leaf ↔ t = leaf := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [flipColors]

omit [LinearOrder α] in
/-- `moveRedLeft` never turns a node into a `leaf` (it only ever recolors/rotates, both of which
preserve node-vs-`leaf` shape) — needed so `deleteMin`'s own `match` on `moveRedLeft`'s result never
actually hits its `leaf` arm when the input wasn't `leaf` to begin with. -/
theorem isRed_iff {t : LLRB α} : t.isRed = true ↔ t.IsRed := by
  cases t with
  | leaf => simp [isRed, IsRed]
  | node c _ _ _ => cases c <;> simp [isRed, IsRed]

omit [LinearOrder α] in
theorem isRed_eq_false_iff {t : LLRB α} : t.isRed = false ↔ ¬ t.IsRed := by
  rw [← isRed_iff]; cases t.isRed <;> simp

omit [LinearOrder α] in
/-- Extracts `NoRedRed` of both children from `NoRedRed` of the whole (opaque) tree — needed
whenever the tree in question is a function application (like `fixUp (...)`/`deleteMin (...)`)
rather than a literal `node`, so `.2.1`/`.2.2` projection on `NoRedRed`'s own `match` doesn't fire
automatically. -/
theorem NoRedRed.children {t : LLRB α} (h : NoRedRed t) : NoRedRed t.left ∧ NoRedRed t.right := by
  cases t with
  | leaf => simp [left, right, NoRedRed]
  | node c l k r => exact ⟨h.2.1, h.2.2⟩

omit [LinearOrder α] in
theorem moveRedLeft_eq_leaf_iff {t : LLRB α} : moveRedLeft t = leaf ↔ t = leaf := by
  simp only [moveRedLeft]
  split_ifs with h
  · rcases hft : flipColors t with _ | ⟨c, l, k, r⟩
    · simp [flipColors_eq_leaf_iff.mp hft]
    · have ht_ne : t ≠ leaf := by
        intro heq; rw [heq] at hft; simp [flipColors] at hft
      simp [flipColors_eq_leaf_iff, rotateLeft_eq_leaf_iff, ht_ne]
  · simp [flipColors_eq_leaf_iff]

omit [LinearOrder α] in
/-- Rebalancing after deletion preserves full red-red safety. A red parent requires both
updated children black-rooted; a black parent may absorb a temporary red right link. -/
theorem fixUp_delete_spec {c : Color} {l r : LLRB α} {k : α}
    (hl : LeftLeaning l) (hr : LeftLeaning r)
    (hnl : NoRedRed l) (hnr : NoRedRed r)
    (hbl : Balanced l) (hbr : Balanced r) (hbh : bheight l = bheight r)
    (hc : c = .red → ¬ l.IsRed ∧ ¬ r.IsRed) :
    bheight (fixUp (node c l k r)) = bheight l + (if c = .black then 1 else 0) ∧
    Balanced (fixUp (node c l k r)) ∧ LeftLeaning (fixUp (node c l k r)) ∧
    NoRedRed (fixUp (node c l k r)) ∧
    ((fixUp (node c l k r)).IsRed → c = .red ∨ r.IsRed) := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩ <;>
    rcases r with _ | ⟨cr, rl, rk, rr⟩ <;>
    (try rcases ll with _ | ⟨cll, lll, llk, llr⟩) <;>
    (try rcases rr with _ | ⟨crr, rrl, rrk, rrr⟩) <;>
    cases c <;> (try cases cl) <;> (try cases cr) <;>
    (try cases cll) <;> (try cases crr) <;>
    simp_all [fixUp, rotateLeft, flipColors, Color.flip, isRed, left, right,
      LeftLeaning, NoRedRed, IsRed, bheight, Balanced]
  omega

omit [LinearOrder α] in
/-- Deleting the minimum preserves full red-red safety and black height when the input
has a spare red link. A black-rooted input also remains black-rooted. These stronger facts
allow the recursive result to be combined with a temporarily red sibling. -/
theorem deleteMin_spec {t : LLRB α} (ht_bal : Balanced t) (ht_ll : LeftLeaning t)
    (ht_nrr : NoRedRed t) (ht_ntn : NotTwoNode t) :
    bheight (deleteMin t) = bheight t ∧ Balanced (deleteMin t) ∧
    LeftLeaning (deleteMin t) ∧ NoRedRed (deleteMin t) ∧
    ((deleteMin t).IsRed → t.IsRed) := by
  induction t using deleteMin.induct with
  | case1 => exact absurd ht_ntn (by simp [NotTwoNode, IsRed, left])
  | case2 c k r =>
    have hc : c = .red := isRed_of_notTwoNode ht_ntn (by simp [IsRed])
    subst hc
    have hr_notred : ¬ r.IsRed := (ht_nrr.1 rfl).2
    have hbh1 : bheight r = 1 := by
      have h1 := ht_bal.1
      simpa [bheight] using h1.symm
    have hr_leaf : r = leaf := by
      rcases r with _ | ⟨cr, rl, rk, rr⟩
      · rfl
      · exfalso
        have hcr : cr = .black := by
          rcases cr with _ | _
          · exact absurd rfl hr_notred
          · rfl
        subst hcr
        have := bheight_pos rl
        simp [bheight] at hbh1
        omega
    subst hr_leaf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [deleteMin, bheight, IsRed, Balanced, LeftLeaning, NoRedRed]
  | case3 c l k r hlne hh =>
    exfalso
    revert hh
    split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    split at hh
    case isTrue hguard =>
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard, ite_true] at heq
          exact absurd heq (by simp [moveRedLeft_eq_leaf_iff])
        · rename_i heq
          simp only [hguard, ite_true] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      rw [hdm]
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
      obtain ⟨hl'_ll, hl'_nrr, hl'_bal, hr'_ll, hr'_nrr, hr'_bal, hbh', hcr', hcl', hbh_pres,
        hntn_l'⟩ := hspec
      obtain ⟨hbhdm, hbaldm, hlldm, hnrrdm, hreddm⟩ := ih hl'_bal hl'_ll hl'_nrr hntn_l'
      have hc' : c' = .red → ¬ (deleteMin l').IsRed ∧ ¬ r'.IsRed := by
        intro hred
        exact ⟨fun hdmred ↦ hcl' hred (hreddm hdmred), hcr' hred⟩
      obtain ⟨hbh3, hbal3, hll3, hnrr3, -⟩ :=
        fixUp_delete_spec (c := c') (l := deleteMin l') (r := r') (k := k')
          hlldm hr'_ll hnrrdm hr'_nrr hbaldm hr'_bal (by rw [hbhdm]; exact hbh') hc'
      refine ⟨?_, hbal3, hll3, hnrr3, fun _ ↦ rfl⟩
      rw [hbh3, hbhdm]
      exact hbh_pres
    case isFalse hguard =>
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard] at heq
          exact absurd heq (by simp)
        · rename_i heq
          simp only [hguard] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      rw [hdm]
      injection hh with hc hl hk hr
      subst hc; subst hl; subst hk; subst hr
      have hntn_l : NotTwoNode l := by
        have hb : l.isRed = true ∨ l.left.isRed = true := by
          rcases hb1 : l.isRed with _ | _ <;> rcases hb2 : l.left.isRed with _ | _ <;> simp_all
        rcases hb with hb | hb
        · exact Or.inl (isRed_iff.mp hb)
        · exact Or.inr (isRed_iff.mp hb)
      obtain ⟨hbhdm, hbaldm, hlldm, hnrrdm, hreddm⟩ :=
        ih ht_bal.2.1 ht_ll.2.1 ht_nrr.2.1 hntn_l
      have hc' : c = .red → ¬ (deleteMin l).IsRed ∧ ¬ r.IsRed := by
        intro hred
        exact ⟨fun hdmred ↦ (ht_nrr.1 hred).1 (hreddm hdmred), (ht_nrr.1 hred).2⟩
      obtain ⟨hbh3, hbal3, hll3, hnrr3, hred3⟩ :=
        fixUp_delete_spec (c := c) (l := deleteMin l) (r := r) (k := k)
          hlldm ht_ll.2.2 hnrrdm ht_nrr.2.2 hbaldm ht_bal.2.2 (by rw [hbhdm]; exact ht_bal.1) hc'
      refine ⟨?_, hbal3, hll3, hnrr3, ?_⟩
      · rw [hbh3, hbhdm]; simp [bheight]
      · intro hred
        rcases hred3 hred with hc | hr
        · exact hc
        · exact absurd hr ht_ll.1

omit [LinearOrder α] in
/-- `moveRedLeft` never collapses a non-empty left child down to `leaf` -- needed so that
`deleteMin`'s recursive call `deleteMin l'` always lands on a genuinely smaller, still-nonempty
subtree whenever the original left child was nonempty (i.e. so `l' = leaf` is never a case the
exact-removal proof below has to handle). -/
theorem moveRedLeft_left_ne_leaf {c : Color} {l : LLRB α} {k : α} {r : LLRB α} (hl : l ≠ leaf) :
    (moveRedLeft (node c l k r)).left ≠ leaf := by
  rcases l with _ | ⟨cl, ll, lk, lr⟩
  · exact absurd rfl hl
  rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> (try cases cr) <;>
    (try rcases rl with _ | ⟨crl, rll, rlk, rlr⟩) <;> (try cases crl) <;>
    simp [moveRedLeft, flipColors, rotateLeft, rotateRight, Color.flip, left, right, isRed]

omit [LinearOrder α] in
/-- `deleteMin` never introduces a key that was absent from its input. This one-way membership
statement requires no ordering or color invariant; it does not characterize the removed key. -/
theorem mem_deleteMin (t : LLRB α) (b : α) :
    Mem b (deleteMin t) → Mem b t := by
  induction t using deleteMin.induct with
  | case1 => intro h; simp [deleteMin] at h
  | case2 c k r => intro h; simp only [deleteMin] at h; tauto
  | case3 c l k r hlne hh =>
    exfalso
    revert hh
    split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    intro h
    have hmem_lkr : Mem b (node c' l' k' r') → Mem b (node c l k r) := by
      split at hh
      · rename_i hguard
        rw [← hh, mem_moveRedLeft]
        exact id
      · rename_i hguard
        rw [← hh]
        exact id
    split at hh
    case isTrue hguard =>
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard, ite_true] at heq
          exact absurd heq (by simp [moveRedLeft_eq_leaf_iff])
        · rename_i heq
          simp only [hguard, ite_true] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      rw [hdm, mem_fixUp, mem_node] at h
      rcases h with h | rfl | h
      · exact hmem_lkr (Or.inl (ih h))
      · exact hmem_lkr (Or.inr (Or.inl rfl))
      · exact hmem_lkr (Or.inr (Or.inr h))
    case isFalse hguard =>
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard] at heq
          exact absurd heq (by simp)
        · rename_i heq
          simp only [hguard] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      rw [hdm, mem_fixUp, mem_node] at h
      rcases h with h | rfl | h
      · exact hmem_lkr (Or.inl (ih h))
      · exact hmem_lkr (Or.inr (Or.inl rfl))
      · exact hmem_lkr (Or.inr (Or.inr h))

/-- **Exact minimum-removal**: `deleteMin` keeps exactly the keys of its input other than the
minimum itself -- the two-way strengthening of `mem_deleteMin` above. Needs `Sorted` (to know the
minimum is strictly below everything else) but no color invariant, matching `mem_deleteMin`'s own
scope. -/
theorem mem_deleteMin_iff {t : LLRB α} (ht : Sorted t) {m : α} (hm : min? t = some m) (b : α) :
    Mem b (deleteMin t) ↔ Mem b t ∧ b ≠ m := by
  induction t using deleteMin.induct with
  | case1 => simp [min?] at hm
  | case2 c k r =>
    have hmk : m = k := by simpa [min?] using hm.symm
    subst hmk
    simp only [deleteMin, mem_node, mem_leaf, false_or]
    constructor
    · intro h
      exact ⟨Or.inr h, (ne_of_lt (ht.2.1.of_mem h)).symm⟩
    · rintro ⟨rfl | h, hne⟩
      · exact absurd rfl hne
      · exact h
  | case3 c l k r hlne hh =>
    exfalso
    revert hh
    split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    split at hh
    case isTrue hguard =>
      have hl'ne : l' ≠ leaf := by
        have hne := moveRedLeft_left_ne_leaf (c := c) (k := k) (r := r) hlne
        rw [hh] at hne
        simpa [left] using hne
      have hsorted_lkr : Sorted (node c' l' k' r') := by rw [← hh]; exact sorted_moveRedLeft ht
      have hmem_lkr : ∀ x, Mem x (node c' l' k' r') ↔ Mem x (node c l k r) := fun x => by
        rw [← hh]; exact mem_moveRedLeft _ x
      have hmin_lkr : min? (node c' l' k' r') = min? (node c l k r) := by
        rw [← hh]; exact min?_moveRedLeft ht
      have hm' : min? l' = some m := by
        rw [min?_node_of_ne_leaf hl'ne] at hmin_lkr
        rw [hmin_lkr]; exact hm
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard, ite_true] at heq
          exact absurd heq (by simp [moveRedLeft_eq_leaf_iff])
        · rename_i heq
          simp only [hguard, ite_true] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      have hmk' : m < k' := hsorted_lkr.1.of_mem (min?_correct hsorted_lkr.2.2.1 hm').1
      have hr'k' : ∀ x, Mem x r' → k' < x := fun x hx => hsorted_lkr.2.1.of_mem hx
      have goal_lhs :
          Mem b (deleteMin (node c l k r)) ↔ Mem b (deleteMin l') ∨ b = k' ∨ Mem b r' := by
        rw [hdm, mem_fixUp, mem_node]
      have goal_rhs : Mem b (node c l k r) ↔ Mem b l' ∨ b = k' ∨ Mem b r' :=
        (hmem_lkr b).symm.trans (mem_node b c' l' k' r')
      rw [goal_lhs, goal_rhs, ih hsorted_lkr.2.2.1 hm']
      constructor
      · rintro (⟨hbl', hbm⟩ | rfl | hbr')
        · exact ⟨Or.inl hbl', hbm⟩
        · exact ⟨Or.inr (Or.inl rfl), (ne_of_lt hmk').symm⟩
        · exact ⟨Or.inr (Or.inr hbr'), (ne_of_lt (lt_trans hmk' (hr'k' _ hbr'))).symm⟩
      · rintro ⟨hbl' | rfl | hbr', hne⟩
        · exact Or.inl ⟨hbl', hne⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hbr')
    case isFalse hguard =>
      have hl'ne : l' ≠ leaf := by
        injection hh with e1 e2 e3 e4
        rw [← e2]; exact hlne
      have hsorted_lkr : Sorted (node c' l' k' r') := by rw [← hh]; exact ht
      have hmem_lkr : ∀ x, Mem x (node c' l' k' r') ↔ Mem x (node c l k r) := fun x => by
        rw [← hh]
      have hmin_lkr : min? (node c' l' k' r') = min? (node c l k r) := by rw [← hh]
      have hm' : min? l' = some m := by
        rw [min?_node_of_ne_leaf hl'ne] at hmin_lkr
        rw [hmin_lkr]; exact hm
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard] at heq
          exact absurd heq (by simp)
        · rename_i heq
          simp only [hguard] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      have hmk' : m < k' := hsorted_lkr.1.of_mem (min?_correct hsorted_lkr.2.2.1 hm').1
      have hr'k' : ∀ x, Mem x r' → k' < x := fun x hx => hsorted_lkr.2.1.of_mem hx
      have goal_lhs :
          Mem b (deleteMin (node c l k r)) ↔ Mem b (deleteMin l') ∨ b = k' ∨ Mem b r' := by
        rw [hdm, mem_fixUp, mem_node]
      have goal_rhs : Mem b (node c l k r) ↔ Mem b l' ∨ b = k' ∨ Mem b r' :=
        (hmem_lkr b).symm.trans (mem_node b c' l' k' r')
      rw [goal_lhs, goal_rhs, ih hsorted_lkr.2.2.1 hm']
      constructor
      · rintro (⟨hbl', hbm⟩ | rfl | hbr')
        · exact ⟨Or.inl hbl', hbm⟩
        · exact ⟨Or.inr (Or.inl rfl), (ne_of_lt hmk').symm⟩
        · exact ⟨Or.inr (Or.inr hbr'), (ne_of_lt (lt_trans hmk' (hr'k' _ hbr'))).symm⟩
      · rintro ⟨hbl' | rfl | hbr', hne⟩
        · exact Or.inl ⟨hbl', hne⟩
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr hbr')

/-- When the left child is empty, `deleteMin` removes the root key. -/
theorem not_mem_deleteMin_root_of_leaf_left {c : Color} {k : α} {r : LLRB α}
    (ht : Sorted (node c leaf k r)) : ¬ Mem k (deleteMin (node c leaf k r)) := by
  simp only [deleteMin]
  intro h
  exact (lt_irrefl k) (ht.2.1.of_mem h)

/-- `deleteMin` preserves `Sorted` -- the other color-blind half of its correctness, needing no
color invariant either (mirrors `sorted_insertAux`). -/
theorem sorted_deleteMin {t : LLRB α} (ht : Sorted t) : Sorted (deleteMin t) := by
  induction t using deleteMin.induct with
  | case1 => simpa [deleteMin] using ht
  | case2 c k r => simpa [deleteMin] using ht.2.2.2
  | case3 c l k r hlne hh =>
    exfalso
    revert hh
    split
    · simp [moveRedLeft_eq_leaf_iff]
    · simp
  | case4 c l k r hlne c' l' k' r' hh ih =>
    have hsorted_lkr : Sorted (node c' l' k' r') := by
      split at hh
      · rename_i hguard
        rw [← hh]; exact sorted_moveRedLeft ht
      · rename_i hguard
        rw [← hh]; exact ht
    split at hh
    case isTrue hguard =>
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard, ite_true] at heq
          exact absurd heq (by simp [moveRedLeft_eq_leaf_iff])
        · rename_i heq
          simp only [hguard, ite_true] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      rw [hdm]
      exact sorted_fixUp
        ⟨all_of_forall_mem (fun b hb => hsorted_lkr.1.of_mem (mem_deleteMin l' b hb)),
          hsorted_lkr.2.1, ih hsorted_lkr.2.2.1, hsorted_lkr.2.2.2⟩
    case isFalse hguard =>
      have hdm : deleteMin (node c l k r) = fixUp (node c' (deleteMin l') k' r') := by
        simp only [deleteMin]
        split
        · rename_i heq
          simp only [hguard] at heq
          exact absurd heq (by simp)
        · rename_i heq
          simp only [hguard] at heq
          have heq2 := heq.symm.trans hh
          injection heq2 with e1 e2 e3 e4
          subst e1; subst e2; subst e3; subst e4
          rfl
      rw [hdm]
      exact sorted_fixUp
        ⟨all_of_forall_mem (fun b hb => hsorted_lkr.1.of_mem (mem_deleteMin l' b hb)),
          hsorted_lkr.2.1, ih hsorted_lkr.2.2.1, hsorted_lkr.2.2.2⟩

/-- `deleteMin` preserves ordering, left-leaning links, and black balance under its recursive
precondition. `deleteMin_spec` additionally proves unconditional red-red safety and preservation
of a black root. This corollary keeps the conditional conclusion.

This is an invariant-preservation result for the recursive helper, not an exact characterization
of the removed key or a correctness theorem for general `delete`. -/
theorem valid_deleteMin {t : LLRB α} (hs : Sorted t) (hll : LeftLeaning t) (hnrr : NoRedRed t)
    (hbal : Balanced t) (hntn : NotTwoNode t) :
    Sorted (deleteMin t) ∧ LeftLeaning (deleteMin t) ∧
    (¬ (deleteMin t).IsRed → NoRedRed (deleteMin t)) ∧ Balanced (deleteMin t) := by
  obtain ⟨-, hbal', hll', hnrr', -⟩ := deleteMin_spec hbal hll hnrr hntn
  exact ⟨sorted_deleteMin hs, hll', fun _ ↦ hnrr', hbal'⟩

end LLRB

end AlgoDesign.Searching
