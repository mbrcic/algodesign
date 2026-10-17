/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Mathlib.Order.Defs.LinearOrder

/-!
# Range bounds

The two ends of a range query, what it means for a key to lie between them (`InRange`, decided
by `inRange`), and the range query itself, `keysInRange`: the keys of an in-order listing that the
bounds admit. `SearchTree.range`, `BST.range`, `LLRB.range`, `RBTree.range` and `BTree.range` are
each `keysInRange` on their listing; `SearchTree.Promise.range_spec` is its law on every search
tree. No bound, a bound the key may equal, or one it must pass.
-/

@[expose] public section

namespace AlgoDesign.Searching

/-- One end of a range query. -/
inductive RangeBound (α : Type) : Type where
  /-- No bound on this end: every key passes. -/
  | unbounded : RangeBound α
  /-- Keys equal to `a` pass. -/
  | included (a : α) : RangeBound α
  /-- Keys equal to `a` do not. -/
  | excluded (a : α) : RangeBound α
  deriving Repr

namespace RangeBound

variable {α : Type} [LinearOrder α]

/-- `k` clears this bound, read as the *lower* end of a range. -/
def Lower : RangeBound α → α → Prop
  | unbounded, _ => True
  | included b, k => b ≤ k
  | excluded b, k => b < k

/-- `k` clears this bound, read as the *upper* end. The mirror of `Lower`. -/
def Upper : RangeBound α → α → Prop
  | unbounded, _ => True
  | included b, k => k ≤ b
  | excluded b, k => k < b

instance : (lo : RangeBound α) → (k : α) → Decidable (lo.Lower k)
  | unbounded, _ => inferInstanceAs (Decidable True)
  | included b, k => inferInstanceAs (Decidable (b ≤ k))
  | excluded b, k => inferInstanceAs (Decidable (b < k))

instance : (hi : RangeBound α) → (k : α) → Decidable (hi.Upper k)
  | unbounded, _ => inferInstanceAs (Decidable True)
  | included b, k => inferInstanceAs (Decidable (k ≤ b))
  | excluded b, k => inferInstanceAs (Decidable (k < b))

end RangeBound

/-- `k` lies between the two bounds. -/
def InRange [LinearOrder α] (lo hi : RangeBound α) (k : α) : Prop := lo.Lower k ∧ hi.Upper k

instance [LinearOrder α] (lo hi : RangeBound α) (k : α) : Decidable (InRange lo hi k) :=
  by unfold InRange; infer_instance

/-- Is `k` between the two bounds? The test a range query filters by: `InRange`, decided. -/
def inRange [LinearOrder α] (lo hi : RangeBound α) (k : α) : Bool := decide (InRange lo hi k)

@[simp] theorem inRange_eq_true [LinearOrder α] (lo hi : RangeBound α) (k : α) :
    inRange lo hi k = true ↔ InRange lo hi k := by
  simp [inRange]

/-- **The range query**: the keys of the listing `l` that the bounds admit, in `l`'s order. -/
def keysInRange [LinearOrder α] (lo hi : RangeBound α) (l : List α) : List α :=
  l.filter (inRange lo hi)

@[simp] theorem inRange_unbounded [LinearOrder α] (k : α) :
    InRange (α := α) .unbounded .unbounded k := ⟨trivial, trivial⟩

end AlgoDesign.Searching

end
