/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Treap.Insert

/-!
# Treap: join

`join` glues two treaps whose keys are separated, the higher-priority root on top: it keeps
membership, both invariants, and every priority (`priorityOf_join`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Treap

variable {α : Type}
variable [LinearOrder α]

/-! ### `join`

`join l r` merges two treaps, `l`'s keys left of `r`'s. The root of higher priority stays on top,
the right one on a tie, and the other tree is joined into its inner side. It glues a deleted node's
children back together (`deleteJoin`). -/

/-- Join two treaps, every key of `l` below every key of `r`: the root of higher priority stays
on top, the right one on a tie. -/
def join : Treap α → Treap α → Treap α
  | leaf, r => r
  | l, leaf => l
  | node ll lk lp lr, node rl rk rp rr =>
      if rp < lp then node ll lk lp (join lr (node rl rk rp rr))
      else node (join (node ll lk lp lr) rl) rk rp rr
termination_by l r => sizeOf l + sizeOf r
decreasing_by all_goals (simp_wf; omega)

omit [LinearOrder α] in
/-- **`join` is correct on keys**: no key is added or lost. Unconditional — no assumption on how
`l`'s and `r`'s keys relate is needed for *this* fact (only `sorted_join`, which additionally
places them correctly, needs that). -/
theorem mem_join (b : α) : ∀ l r : Treap α, Mem b (join l r) ↔ Mem b l ∨ Mem b r := by
  intro l r
  induction l, r using join.induct with
  | case1 r => simp [join]
  | case2 l => cases l <;> simp [join]
  | case3 ll lk lp lr rl rk rp rr hge ih =>
    simp only [join, hge, ↓reduceIte, mem_node, ih]
    tauto
  | case4 ll lk lp lr rl rk rp rr hlt ih =>
    simp only [join, hlt, ↓reduceIte, mem_node, ih]
    tauto

omit [LinearOrder α] in
/-- `AllPriority q` is preserved by `join`, unconditionally: `join` never invents a priority. -/
theorem AllPriority.join {q : ℕ → Prop} {l r : Treap α} (hl : AllPriority q l)
    (hr : AllPriority q r) : AllPriority q (Treap.join l r) := by
  induction l, r using join.induct with
  | case1 r => unfold Treap.join; exact hr
  | case2 l => cases l with
    | leaf => trivial
    | node _ _ _ _ => unfold Treap.join; exact hl
  | case3 ll lk lp lr rl rk rp rr hge ih =>
    obtain ⟨hll, hlp, hlr⟩ := hl
    unfold Treap.join
    split_ifs
    exact ⟨hll, hlp, ih hlr hr⟩
  | case4 ll lk lp lr rl rk rp rr hlt ih =>
    obtain ⟨hrl, hrp, hrr⟩ := hr
    unfold Treap.join
    split_ifs
    exact ⟨ih hl hrl, hrp, hrr⟩

/-- **`join` is correct on the BST invariant**, given that `l`'s keys are all below `r`'s. -/
theorem sorted_join {l r : Treap α} (hl : Sorted l) (hr : Sorted r)
    (hsep : ∀ x y, Mem x l → Mem y r → x < y) : Sorted (Treap.join l r) := by
  induction l, r using join.induct with
  | case1 r => unfold Treap.join; exact hr
  | case2 l => cases l with
    | leaf => trivial
    | node _ _ _ _ => unfold Treap.join; exact hl
  | case3 ll lk lp lr rl rk rp rr hge ih =>
    obtain ⟨hll, hlr, hsll, hslr⟩ := hl
    simp only [join, hge, ↓reduceIte]
    refine ⟨hll, ?_, hsll, ih hslr hr (fun x y hx hy => hsep x y (Or.inr (Or.inr hx)) hy)⟩
    refine all_of_forall_mem (fun y hy => ?_)
    rw [mem_join] at hy
    rcases hy with hy | hy
    · exact hlr.of_mem hy
    · exact hsep lk y (Or.inr (Or.inl rfl)) hy
  | case4 ll lk lp lr rl rk rp rr hlt ih =>
    obtain ⟨hrl, hrr, hsrl, hsrr⟩ := hr
    simp only [join, hlt, ↓reduceIte]
    refine ⟨?_, hrr, ih hl hsrl (fun x y hx hy => hsep x y hx (Or.inl hy)), hsrr⟩
    refine all_of_forall_mem (fun x hx => ?_)
    rw [mem_join] at hx
    rcases hx with hx | hx
    · exact hsep x rk hx (Or.inr (Or.inl rfl))
    · exact hrl.of_mem hx

omit [LinearOrder α] in
/-- **`join` is correct on heap-order**, with *no* assumption needed on how `l`'s and `r`'s
priorities relate — `HeapOrdered`'s "everywhere ≤ root" phrasing already guarantees that whichever
root `join` promotes dominates the loser's entire subtree, not just its immediate children. -/
theorem heapOrdered_join {l r : Treap α} (hl : HeapOrdered l) (hr : HeapOrdered r) :
    HeapOrdered (Treap.join l r) := by
  induction l, r using join.induct with
  | case1 r => unfold Treap.join; exact hr
  | case2 l => cases l with
    | leaf => trivial
    | node _ _ _ _ => unfold Treap.join; exact hl
  | case3 ll lk lp lr rl rk rp rr hge ih =>
    obtain ⟨hll, hlr, hhll, hhlr⟩ := hl
    have hrbound : AllPriority (· ≤ rp) (node rl rk rp rr) := hr.self_le
    simp only [join, hge, ↓reduceIte, heapOrdered_node]
    exact ⟨hll, hlr.join (hrbound.imp (fun _ h => by omega)), hhll, ih hhlr hr⟩
  | case4 ll lk lp lr rl rk rp rr hlt ih =>
    obtain ⟨hrl, hrr, hhrl, hhrr⟩ := hr
    have hlbound : AllPriority (· ≤ lp) (node ll lk lp lr) := hl.self_le
    simp only [join, hlt, ↓reduceIte, heapOrdered_node]
    exact ⟨(hlbound.imp (fun _ h => by omega)).join hrl, hrr, ih hl hhrl, hhrr⟩

/-- **`join` moves no priority.** A key of either side keeps the priority it had there; the two
sides hold disjoint keys, so at most one of the two lookups answers. -/
theorem priorityOf_join {l r : Treap α} (hl : Sorted l) (hr : Sorted r)
    (hsep : ∀ x y, Mem x l → Mem y r → x < y) (b : α) :
    priorityOf b (join l r) = (priorityOf b l).or (priorityOf b r) := by
  induction l, r using join.induct with
  | case1 r => simp [join]
  | case2 l => cases l <;> simp [join]
  | case3 ll lk lp lr rl rk rp rr hge ih =>
    obtain ⟨hll, hlr, hsll, hslr⟩ := hl
    simp only [join, hge, ↓reduceIte]
    rcases lt_trichotomy b lk with h | rfl | h
    · rw [priorityOf_left h, priorityOf_left h,
        priorityOf_eq_none_of_not_mem hr (fun hm => lt_asymm h
          (hsep lk b (Or.inr (Or.inl rfl)) hm)), Option.or_none]
    · rw [priorityOf_root, priorityOf_root, Option.some_or]
    · rw [priorityOf_right h, priorityOf_right h,
        ih hslr hr (fun x y hx hy => hsep x y (Or.inr (Or.inr hx)) hy)]
  | case4 ll lk lp lr rl rk rp rr hlt ih =>
    obtain ⟨hrl, hrr, hsrl, hsrr⟩ := hr
    simp only [join, hlt, ↓reduceIte]
    rcases lt_trichotomy b rk with h | rfl | h
    · rw [priorityOf_left h, priorityOf_left h,
        ih hl hsrl (fun x y hx hy => hsep x y hx (Or.inl hy))]
    · rw [priorityOf_root, priorityOf_root,
        priorityOf_eq_none_of_not_mem hl (fun hm => lt_irrefl b
          (hsep b b hm (Or.inr (Or.inl rfl)))), Option.none_or]
    · rw [priorityOf_right h, priorityOf_right h,
        priorityOf_eq_none_of_not_mem hl (fun hm => lt_asymm h
          (hsep b rk hm (Or.inr (Or.inl rfl)))), Option.none_or]

end Treap

end AlgoDesign.Searching
