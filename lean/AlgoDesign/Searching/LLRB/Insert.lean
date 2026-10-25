/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LLRB.Search

/-!
# LLRB: insertion

Sedgewick's `insert`: an ordinary BST insertion repaired on the way up by `fixUp`'s three moves
(`rotateLeft`, `rotateRight`, `flipColors`), the root forced black at the end. `mem_insert` and
`sorted_insert` are the color-blind half, `valid_insert` the color invariants, and `insertSpec`:
`insert` discharges `InsertSpec`. `insertM`, the comparison-counting twin, is at the end, next to
the `insert` it erases to (`ret_insertM`).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace LLRB

variable {α : Type}
variable [LinearOrder α]

/-- **What any insertion of `a` owes**: the key set gains exactly `a`, and a legal tree stays legal.
The per-operation form the proofs discharge; the promise, `SearchTree.Promise`, states the same
for every operation at once. -/
def InsertSpec (a : α) (before after : LLRB α) : Prop :=
  (∀ b, Mem b after ↔ (b = a ∨ Mem b before)) ∧ (Valid before → Valid after)

/-- Sedgewick's `rotateLeft`: `h`'s right child comes up to take `h`'s place, `h` becomes its new
left child. Only meaningful (and only ever called) when `h`'s right child is actually a node —
the `leaf`/`leaf` fallback case just returns the input unchanged, since there's nothing to
rotate. -/
def rotateLeft : LLRB α → LLRB α
  | node c l k (node _ rl rk rr) => node c (node .red l k rl) rk rr
  | t => t

/-- Sedgewick's `rotateRight`, symmetric to `rotateLeft`. -/
def rotateRight : LLRB α → LLRB α
  | node c (node _ ll lk lr) k r => node c ll lk (node .red lr k r)
  | t => t

/-- Sedgewick's `flipColors`: flips `h`'s own color and both its children's — the move that
splits a (temporary) 4-node, represented as a black node with two red children, into a red node
with two black children one level up. Only meaningful when both children are nodes; the fallback
case is unreachable in practice (`fixUp` only ever calls this once it's checked `h.left.isRed` and
`h.right.isRed`, which are both `false` on `leaf`). -/
def flipColors : LLRB α → LLRB α
  | node c (node cl ll lk lr) k (node cr rl rk rr) =>
      node c.flip (node cl.flip ll lk lr) k (node cr.flip rl rk rr)
  | t => t

/-- Sedgewick's fix-up sequence, run on the way back up from every recursive `insert` call: lean
a stray red right link back left, split a temporary 4-node's rightward lean, then split the
4-node itself if both children ended up red. -/
def fixUp (h : LLRB α) : LLRB α :=
  let h1 := if h.right.isRed && !h.left.isRed then rotateLeft h else h
  let h2 := if h1.left.isRed && h1.left.left.isRed then rotateRight h1 else h1
  if h2.left.isRed && h2.right.isRed then flipColors h2 else h2

/-- Insert `a`, following the ordering at every node (a duplicate key is a no-op, same as
`BST.insert` — this models a `Set`), running `fixUp` on the way back up from every recursive
call. Doesn't yet force the root black — `insert` below does that, matching Sedgewick's own
top-level/recursive-helper split. -/
def insertAux (a : α) : LLRB α → LLRB α
  | leaf => node .red leaf a leaf
  | node c l k r =>
      fixUp <|
        if a < k then node c (insertAux a l) k r
        else if k < a then node c l k (insertAux a r)
        else node c l k r

/-- Insert `a`, then force the root's link black — Sedgewick's `root.color = BLACK`, needed
because `insertAux`'s recursive fix-ups can leave the root red (a split 4-node pushes red
upward; at the true root there's nowhere further up for it to go). -/
def insert (a : α) (t : LLRB α) : LLRB α :=
  match insertAux a t with
  | leaf => leaf
  | node _ l k r => node .black l k r

/-! ### `insert` preserves `Sorted` and `Mem`

Color-blind stage first: `Sorted` and `Mem` don't look at a node's color at all, so
`rotateLeft`/`rotateRight`/`flipColors`/`fixUp` preserve both unconditionally — no case split on
whether a fix-up rule actually fires is needed here. That split (and the real difficulty) only
shows up once the *color* invariants (`LeftLeaning`/`NoRedRed`/`BlackHeightOk`) are in play. -/

omit [LinearOrder α] in
@[simp] theorem mem_leaf (a : α) : Mem a (leaf : LLRB α) ↔ False := Iff.rfl

omit [LinearOrder α] in
@[simp] theorem mem_node (a : α) (c : Color) (l : LLRB α) (k : α) (r : LLRB α) :
    Mem a (node c l k r) ↔ Mem a l ∨ a = k ∨ Mem a r := Iff.rfl

omit [LinearOrder α] in
theorem All.imp {p q : α → Prop} (h : ∀ a, p a → q a) : ∀ {t : LLRB α}, All p t → All q t
  | leaf, _ => trivial
  | node _ _ _ _, ⟨hl, hk, hr⟩ => ⟨hl.imp (fun _ => h _), h _ hk, hr.imp (fun _ => h _)⟩

omit [LinearOrder α] in
theorem all_of_forall_mem {p : α → Prop} {t : LLRB α} (h : ∀ b, Mem b t → p b) : All p t := by
  induction t with
  | leaf => trivial
  | node _ l k r ihl ihr =>
    exact ⟨ihl (fun b hb => h b (Or.inl hb)), h k (Or.inr (Or.inl rfl)),
      ihr (fun b hb => h b (Or.inr (Or.inr hb)))⟩

omit [LinearOrder α] in
theorem mem_rotateLeft (t : LLRB α) (b : α) : Mem b (rotateLeft t) ↔ Mem b t := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [rotateLeft]
  tauto

omit [LinearOrder α] in
theorem mem_rotateRight (t : LLRB α) (b : α) : Mem b (rotateRight t) ↔ Mem b t := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩ <;> simp [rotateRight]
  tauto

omit [LinearOrder α] in
theorem mem_flipColors (t : LLRB α) (b : α) : Mem b (flipColors t) ↔ Mem b t := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> simp [flipColors]

omit [LinearOrder α] in
theorem mem_fixUp (t : LLRB α) (b : α) : Mem b (fixUp t) ↔ Mem b t := by
  simp only [fixUp]
  split_ifs <;> simp [mem_rotateLeft, mem_rotateRight, mem_flipColors]

theorem sorted_rotateLeft {t : LLRB α} (ht : Sorted t) : Sorted (rotateLeft t) := by
  rcases t with _ | ⟨c, l, k, _ | ⟨cr, rl, rk, rr⟩⟩
  · trivial
  · exact ht
  · obtain ⟨hl, hr, hsl, hsr⟩ := ht
    obtain ⟨hrl_lt, hk_lt_rk, hrr_lt⟩ := hr
    obtain ⟨hrl_bound, hrr_bound, hsrl, hsrr⟩ := hsr
    exact ⟨⟨hl.imp (fun _ hx => lt_trans hx hk_lt_rk), hk_lt_rk, hrl_bound⟩, hrr_bound,
      ⟨hl, hrl_lt, hsl, hsrl⟩, hsrr⟩

theorem sorted_rotateRight {t : LLRB α} (ht : Sorted t) : Sorted (rotateRight t) := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, r⟩
  · trivial
  · exact ht
  · obtain ⟨hl, hr, hsl, hsr⟩ := ht
    obtain ⟨hll_lt_k, hlk_lt_k, hlr_lt_k⟩ := hl
    obtain ⟨hll_bound, hlr_bound, hsll, hslr⟩ := hsl
    exact ⟨hll_bound, ⟨hlr_bound, hlk_lt_k, hr.imp (fun _ hx => lt_trans hlk_lt_k hx)⟩, hsll,
      ⟨hlr_lt_k, hr, hslr, hsr⟩⟩

theorem sorted_flipColors {t : LLRB α} (ht : Sorted t) : Sorted (flipColors t) := by
  rcases t with _ | ⟨c, _ | ⟨cl, ll, lk, lr⟩, k, _ | ⟨cr, rl, rk, rr⟩⟩ <;> exact ht

theorem sorted_fixUp {t : LLRB α} (ht : Sorted t) : Sorted (fixUp t) := by
  simp only [fixUp]
  split_ifs <;>
    first
      | exact ht
      | exact sorted_rotateLeft ht
      | exact sorted_rotateRight ht
      | exact sorted_flipColors ht
      | exact sorted_flipColors (sorted_rotateLeft ht)
      | exact sorted_flipColors (sorted_rotateRight ht)
      | exact sorted_rotateRight (sorted_rotateLeft ht)
      | exact sorted_flipColors (sorted_rotateRight (sorted_rotateLeft ht))

theorem mem_insertAux (t : LLRB α) (a b : α) : Mem b (insertAux a t) ↔ b = a ∨ Mem b t := by
  induction t with
  | leaf => simp [insertAux]
  | node c l k r ihl ihr =>
    unfold insertAux
    split
    · rename_i h
      simp only [mem_fixUp, mem_node, ihl]
      tauto
    · split
      · rename_i h h'
        simp only [mem_fixUp, mem_node, ihr]
        tauto
      · rename_i h h'
        have hka : k = a := le_antisymm (not_lt.mp h) (not_lt.mp h')
        simp only [mem_fixUp, mem_node]
        constructor
        · rintro (hl | rfl | hr) <;> tauto
        · rintro (rfl | hl | rfl | hr) <;> tauto

theorem All.insertAux {p : α → Prop} {t : LLRB α} (h : All p t) {a : α} (ha : p a) :
    All p (insertAux a t) :=
  all_of_forall_mem fun b hb =>
    ((mem_insertAux t a b).mp hb).elim (fun hba => by rw [hba]; exact ha) h.of_mem

theorem sorted_insertAux {t : LLRB α} (ht : Sorted t) (a : α) : Sorted (insertAux a t) := by
  induction t with
  | leaf => simp [insertAux, Sorted, All]
  | node c l k r ihl ihr =>
    unfold insertAux
    split
    · rename_i h
      obtain ⟨hl, hr, hsl, hsr⟩ := ht
      exact sorted_fixUp ⟨hl.insertAux h, hr, ihl hsl, hsr⟩
    · split
      · rename_i h h'
        obtain ⟨hl, hr, hsl, hsr⟩ := ht
        exact sorted_fixUp ⟨hl, hr.insertAux h', hsl, ihr hsr⟩
      · exact sorted_fixUp ht

theorem mem_insert (t : LLRB α) (a b : α) : Mem b (insert a t) ↔ b = a ∨ Mem b t := by
  rw [← mem_insertAux t a b]
  unfold insert
  cases insertAux a t <;> simp

theorem sorted_insert {t : LLRB α} (ht : Sorted t) (a : α) : Sorted (insert a t) := by
  have h := sorted_insertAux ht a
  unfold insert
  rcases hi : insertAux a t with _ | ⟨c, l, k, r⟩ <;> rw [hi] at h <;> exact h

/-! ### `insert` preserves the color invariants (`LeftLeaning`, `NoRedRed`, `BlackHeightOk`)

The genuinely hard part: `insertAux`'s naive per-step invariant isn't strong enough on its own (a
red-rooted result can have a red *left* child -- exactly the violation `fixUp` cleans up one level
further up the recursion, not at the level that introduced it), so the induction needs a
color-conditional strengthened statement (`insertAux_spec` below), following the same shape used
in Nipkow's Isabelle/HOL red-black tree proofs.

`blackHeight`'s `Option`-based formulation is awkward to induct on directly (nested
`Option.bind`s), so this section works instead with a *total* ℕ-valued `bheight` (count black
links down the left spine) and a structural `Balanced` predicate, then bridges back to
`BlackHeightOk` with one lemma (`blackHeight_eq_some_iff`), so `BlackHeightOk` is used as stated. -/

omit [LinearOrder α] in
/-- `fixUp`'s effect when the violation (if any) came from the *left* recursive call: `l'` is
`insertAux`'s output on the left child, already known balanced (same `bheight` as before) and
`LeftLeaning`, but possibly red with a red left child of its own (the one violation `insertAux`'s
per-step invariant allows) -- `r` is an untouched, already-valid right child. Restores all three
invariants and the black-height count in one step.

Note the shape of `hl'_nrr_or`: the red-with-a-red-left-child slack is only ever available under a
*black* parent link (if `c` were red, `NoRedRed` of the original node would already have forced the
left child black, so `insertAux` returns a plain `NoRedRed` there) -- and a red-red pair under a red
link is genuinely beyond what one `fixUp` can repair, so the `¬ c = .red` conjunct is load-bearing,
not decoration. -/
theorem fixUp_left_spec {c : Color} {l' r : LLRB α} {k : α} (hr_black : ¬ r.IsRed)
    (hr_ll : LeftLeaning r) (hr_nrr : NoRedRed r) (hr_bal : Balanced r)
    (hl'_ll : LeftLeaning l') (hl'_bal : Balanced l')
    (hl'_nrr_or : NoRedRed l' ∨ ¬ c = .red ∧ l'.IsRed ∧ NoRedRed l'.left ∧ NoRedRed l'.right)
    (hbh : bheight l' = bheight r) :
    bheight (fixUp (node c l' k r)) = bheight l' + (if c = .black then 1 else 0) ∧
    Balanced (fixUp (node c l' k r)) ∧
    LeftLeaning (fixUp (node c l' k r)) ∧
    (¬ c = .red → NoRedRed (fixUp (node c l' k r))) ∧
    (c = .red → (fixUp (node c l' k r)).IsRed ∧
      NoRedRed (fixUp (node c l' k r)).left ∧ NoRedRed (fixUp (node c l' k r)).right) := by
  have hrf : r.isRed = false := isRed_eq_false hr_black
  rcases l' with _ | ⟨cl', _ | ⟨cll', A, x, B⟩, lk, lr⟩ <;> cases c <;>
    (try cases cl') <;> (try cases cll') <;>
    simp_all [fixUp, rotateLeft, rotateRight, flipColors, Color.flip, isRed, left, right,
      LeftLeaning, NoRedRed, IsRed, bheight, Balanced] <;> omega

omit [LinearOrder α] in
/-- Generalizes `fixUp_left_spec` to also allow `r` itself to be red, not just black — needed for
`deleteMin`'s own use of `fixUp`, where the right subtree comes untouched out of `moveRedLeft`'s
Case A (see `moveRedLeft_spec`'s docstring) already sitting on a temporarily red link, a
`LeftLeaning` violation that is *exactly* what `fixUp`'s own `rotateLeft`/`flipColors` steps exist
to clean up — not something the caller needs to rule out first.

Two extra hypotheses are needed in exchange (without `hrl'` the statement is false):
* `hcr`, forbidding `c`/`r` both red at once (the two-red-links-in-a-row case `fixUp` was never
  meant to repair, mirroring `fixUp_right_spec`'s analogous `hc` hypothesis on `l`);
* `hrl'`, forbidding `r` red *together with* `l'` sitting on the individually-safe slack — when `r`
  is red, `l'` must be fully clean `NoRedRed` (whatever its own color) for `fixUp` to actually
  clear the violation in one step (either `rotateLeft`, when `l'` isn't red, or `flipColors`
  directly, when it is).

Neither combination `moveRedLeft` ever actually produces (Case A has `c` black and hands back a
fully clean `l'`-side story from the *next* recursive call, per `deleteMin_spec`; Case B has `r`
black), but the lemma needs to say so honestly rather than bake it in silently. -/
theorem fixUp_left_spec' {c : Color} {l' r : LLRB α} {k : α} (hcr : c = .red → ¬ r.IsRed)
    (hrl' : r.IsRed → NoRedRed l')
    (hr_ll : LeftLeaning r) (hr_nrr : NoRedRed r) (hr_bal : Balanced r)
    (hl'_ll : LeftLeaning l') (hl'_bal : Balanced l')
    (hl'_nrr_or : NoRedRed l' ∨ ¬ c = .red ∧ l'.IsRed ∧ NoRedRed l'.left ∧ NoRedRed l'.right)
    (hbh : bheight l' = bheight r) :
    bheight (fixUp (node c l' k r)) = bheight l' + (if c = .black then 1 else 0) ∧
    Balanced (fixUp (node c l' k r)) ∧
    LeftLeaning (fixUp (node c l' k r)) ∧
    (¬ c = .red → NoRedRed (fixUp (node c l' k r))) ∧
    (c = .red → (fixUp (node c l' k r)).IsRed ∧
      NoRedRed (fixUp (node c l' k r)).left ∧ NoRedRed (fixUp (node c l' k r)).right) := by
  rcases l' with _ | ⟨cl', _ | ⟨cll', A, x, B⟩, lk, lr⟩ <;> cases c <;>
    (try cases cl') <;> (try cases cll') <;>
    rcases r with _ | ⟨cr, rl, rk, rr⟩ <;> (try cases cr) <;>
    (try rcases rr with _ | ⟨crr, rrl, rrk, rrr⟩) <;> (try cases crr) <;>
    simp_all [fixUp, rotateLeft, rotateRight, flipColors, Color.flip, isRed, left, right,
      LeftLeaning, NoRedRed, IsRed, bheight, Balanced]
  omega

omit [LinearOrder α] in
/-- Symmetric to `fixUp_left_spec`, for a violation coming from the *right* recursive call.
Because of `LeftLeaning`, a red node's right child is always black -- so `insertAux`'s recursive
call on the right can never itself produce a red-rooted result that needs the "maybe red-red"
slack `fixUp_left_spec` carries; `r'` here is always known plain `NoRedRed`.

The untouched left child `l`, on the other hand, *may* be red (a red left link under a black parent
link is exactly what this variant is built out of), so all that can be assumed of it is the
`NoRedRed` consequence `hc`: a red parent link forces a black left child. -/
theorem fixUp_right_spec {c : Color} {l r' : LLRB α} {k : α} (hc : c = .red → ¬ l.IsRed)
    (hl_ll : LeftLeaning l) (hl_nrr : NoRedRed l) (hl_bal : Balanced l)
    (hr'_ll : LeftLeaning r') (hr'_nrr : NoRedRed r') (hr'_bal : Balanced r')
    (hbh : bheight l = bheight r') :
    bheight (fixUp (node c l k r')) = bheight l + (if c = .black then 1 else 0) ∧
    Balanced (fixUp (node c l k r')) ∧
    LeftLeaning (fixUp (node c l k r')) ∧
    (¬ c = .red → NoRedRed (fixUp (node c l k r'))) ∧
    (c = .red → (fixUp (node c l k r')).IsRed ∧
      NoRedRed (fixUp (node c l k r')).left ∧ NoRedRed (fixUp (node c l k r')).right) := by
  by_cases hr : r'.IsRed
  · rcases r' with _ | ⟨cr, rl, rk, rr⟩
    · exact absurd hr (by simp [IsRed])
    have hcr : cr = Color.red := hr
    subst hcr
    obtain ⟨hrnr, hrl_nrr, hrr_nrr⟩ := hr'_nrr
    obtain ⟨hrl_black, hrr_black⟩ := hrnr rfl
    have hrlf : rl.isRed = false := isRed_eq_false hrl_black
    have hrrf : rr.isRed = false := isRed_eq_false hrr_black
    by_cases hlred : l.IsRed
    · rcases l with _ | ⟨cl, ll, lk, lr⟩
      · exact absurd hlred (by simp [IsRed])
      have hcl : cl = Color.red := hlred
      subst hcl
      obtain ⟨hlnr, hll_nrr, hlr_nrr⟩ := hl_nrr
      obtain ⟨hll_black, hlr_black⟩ := hlnr rfl
      have hllf : ll.isRed = false := isRed_eq_false hll_black
      have hlrf : lr.isRed = false := isRed_eq_false hlr_black
      have hcb : c = Color.black := by
        cases c
        · exact absurd hlred (hc rfl)
        · rfl
      subst hcb
      simp_all [fixUp, left, right, isRed, flipColors, Color.flip, rotateLeft,
        LeftLeaning, NoRedRed, IsRed, bheight, Balanced]
    · have hlf : l.isRed = false := isRed_eq_false hlred
      simp_all [fixUp, left, right, isRed, rotateLeft,
        LeftLeaning, NoRedRed, IsRed, bheight, Balanced]
  · have e1 : fixUp (node c l k r') = node c l k r' := by
      have hrf : r'.isRed = false := isRed_eq_false hr
      by_cases hlred : l.IsRed
      · rcases l with _ | ⟨cl, ll, lk, lr⟩
        · exact absurd hlred (by simp [IsRed])
        · have hcl : cl = Color.red := hlred
          subst hcl
          obtain ⟨hh, -, -⟩ := hl_nrr
          simp [fixUp, left, right, isRed_red, hrf, isRed_eq_false (hh rfl).1]
      · simp [fixUp, left, right, hrf, isRed_eq_false hlred]
    rw [e1]
    exact ⟨by simp [bheight], ⟨hbh, hl_bal, hr'_bal⟩, ⟨hr, hl_ll, hr'_ll⟩,
      fun _ => ⟨fun h => ⟨hc h, hr⟩, hl_nrr, hr'_nrr⟩,
      fun h => ⟨by simpa [IsRed] using h, hl_nrr, hr'_nrr⟩⟩

/-- The strengthened induction hypothesis `insertAux` actually needs: not just "the invariants are
preserved," but a color-conditional statement precise enough to survive the recursive step. A
red-rooted `insertAux` result may have a red *left* child (that's the violation `fixUp` exists to
clean up one level further up) -- so the conclusion only promises plain `NoRedRed` when the input
was already black, and separately promises the "root red, children individually `NoRedRed`" slack
when the input was red. -/
theorem insertAux_spec {t : LLRB α} (a : α) (ht_bal : Balanced t) (ht_ll : LeftLeaning t)
    (ht_nrr : NoRedRed t) :
    bheight (insertAux a t) = bheight t ∧ Balanced (insertAux a t) ∧
    LeftLeaning (insertAux a t) ∧
    (¬ t.IsRed → NoRedRed (insertAux a t)) ∧
    (t.IsRed → (insertAux a t).IsRed ∧ NoRedRed (insertAux a t).left ∧
      NoRedRed (insertAux a t).right) := by
  induction t with
  | leaf =>
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;>
      simp [insertAux, Balanced, LeftLeaning, NoRedRed, IsRed, bheight]
  | node c l k r ihl ihr =>
    obtain ⟨hbh, hbl, hbr⟩ := ht_bal
    obtain ⟨hr_black, hl_ll, hr_ll⟩ := ht_ll
    obtain ⟨hnr, hl_nrr, hr_nrr⟩ := ht_nrr
    unfold insertAux
    split
    · obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := ihl hbl hl_ll hl_nrr
      have hdisj : NoRedRed (insertAux a l) ∨
          ¬ c = .red ∧ (insertAux a l).IsRed ∧ NoRedRed (insertAux a l).left ∧
            NoRedRed (insertAux a l).right := by
        by_cases hlred : l.IsRed
        · obtain ⟨p1, p2, p3⟩ := hb5 hlred
          exact Or.inr ⟨fun hcr => (hnr hcr).1 hlred, p1, p2, p3⟩
        · exact Or.inl (hb4 hlred)
      obtain ⟨e1, e2, e3, e4, e5⟩ :=
        fixUp_left_spec hr_black hr_ll hr_nrr hbr hb3 hb2 hdisj (by omega)
      exact ⟨by simp only [bheight]; rw [e1, hb1], e2, e3, e4, e5⟩
    · split
      · obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := ihr hbr hr_ll hr_nrr
        obtain ⟨e1, e2, e3, e4, e5⟩ :=
          fixUp_right_spec (fun hcr => (hnr hcr).1) hl_ll hl_nrr hbl hb3 (hb4 hr_black) hb2
            (by omega)
        exact ⟨by simp only [bheight]; rw [e1], e2, e3, e4, e5⟩
      · obtain ⟨e1, e2, e3, e4, e5⟩ :=
          fixUp_right_spec (fun hcr => (hnr hcr).1) hl_ll hl_nrr hbl hr_ll hr_nrr hbr hbh
        exact ⟨by simp only [bheight]; rw [e1], e2, e3, e4, e5⟩

/-- **`insert` produces a legal LLRB tree from a legal one** -- the payoff of this whole section.
Combined with `sorted_insert`/`mem_insert` above, `insert` is fully verified: it's the ordinary
BST insert, and it never violates any of the three color invariants along the way. -/
theorem valid_insert {t : LLRB α} (ht : Valid t) (a : α) : Valid (insert a t) := by
  obtain ⟨hs, hrb, hll, hnrr, hbh⟩ := ht
  have hbal : Balanced t := blackHeightOk_iff_balanced.mp hbh
  obtain ⟨-, e2, e3, e4, -⟩ := insertAux_spec a hbal hll hnrr
  have hnrr' : NoRedRed (insertAux a t) := e4 (not_isRed_of_rootBlack hrb)
  have hsi : Sorted (insertAux a t) := sorted_insertAux hs a
  unfold insert
  rcases hi : insertAux a t with _ | ⟨c', l', k', r'⟩ <;> rw [hi] at e2 e3 hnrr' hsi
  · exact ⟨trivial, trivial, trivial, trivial, Option.some_ne_none _⟩
  · exact ⟨hsi, rfl, e3, ⟨fun h => absurd h (by decide), hnrr'.2.1, hnrr'.2.2⟩,
      blackHeightOk_iff_balanced.mpr e2⟩

/-- `insertAux`, one tick per three-way comparison: one per node on the path down. -/
def insertAuxM (a : α) : LLRB α → TimeM ℕ (LLRB α)
  | leaf => pure (node .red leaf a leaf)
  | node c l k r => do
      tick 1
      if a < k then (fun l' ↦ fixUp (node c l' k r)) <$> insertAuxM a l
      else if k < a then (fun r' ↦ fixUp (node c l k r')) <$> insertAuxM a r
      else pure (fixUp (node c l k r))

/-- Insert, counted as `insertAuxM` counts, the root then painted black at no cost. -/
def insertM (a : α) (t : LLRB α) : TimeM ℕ (LLRB α) :=
  (fun t' ↦ match t' with
    | leaf => leaf
    | node _ l k r => node .black l k r) <$> insertAuxM a t

theorem ret_insertAuxM (a : α) (t : LLRB α) : (insertAuxM a t).ret = insertAux a t := by
  induction t with
  | leaf => simp [insertAuxM, insertAux]
  | node c l k r ihl ihr =>
    simp only [insertAuxM, insertAux, ret_bind]
    by_cases h : a < k
    · simp [h, ihl]
    · by_cases h' : k < a
      · simp [h, h', ihr]
      · simp [h, h']

theorem ret_insertM (a : α) (t : LLRB α) : (insertM a t).ret = insert a t := by
  simp only [insertM, insert, ret_map, ret_insertAuxM]

/-- **`insert` discharges `InsertSpec`**, assembled from `mem_insert` and `valid_insert`. -/
theorem insertSpec (t : LLRB α) (a : α) : InsertSpec a t (insert a t) :=
  ⟨mem_insert t a, fun hv => valid_insert hv a⟩

end LLRB

end AlgoDesign.Searching
