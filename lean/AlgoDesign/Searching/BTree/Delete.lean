/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Delete.Extreme

/-!
# B-tree: deletion

`deleteSpec`: CLRS §18.3's `delete` (the algorithm is in `Delete/Algorithm.lean`) discharges
`DeleteSpec` on a `Valid` tree, with `delRec_spec` the invariant of its descent.
`deleteSpec_leaf` is the smallest witness that `DeleteSpec` is satisfiable.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## What `delete` must do -/

/-- `delete a` removes exactly `a` from the key set. -/
def DeleteMem (a : α) (before after : BTree α) : Prop :=
  ∀ b, Mem b after ↔ (b ≠ a ∧ Mem b before)

/-- `delete` keeps a legal tree legal, at the same minimum degree. -/
def DeleteValid (deg : ℕ) (before after : BTree α) : Prop :=
  Valid deg before → Valid deg after

/-- The `delete` obligation: `DeleteMem` and `DeleteValid`. The per-operation form the
proofs discharge; `BTree.promise` is proved from it. -/
def DeleteSpec (deg : ℕ) (a : α) (before after : BTree α) : Prop :=
  DeleteMem a before after ∧ DeleteValid deg before after

/-! ## `DeleteSpec` is satisfiable: the one-leaf witness -/

/-- Erasing from a one-leaf tree discharges `DeleteSpec`: the leaf is the root, which has no
occupancy floor. -/
theorem deleteSpec_leaf {deg : ℕ} {ks : List α} (h : Valid deg (leaf ks)) (a : α) :
    DeleteSpec deg a (leaf ks) (leaf (ks.erase a)) := by
  obtain ⟨hb, _, hkc, hdeg⟩ := valid_iff_legal.1 h
  have hnd : ks.Nodup := nodup_of_boundedKeys hb
  refine ⟨fun b => ?_, fun _ => ?_⟩
  · simpa using hnd.mem_erase_iff
  · refine valid_iff_legal.2 ⟨⟨?_, by simp, by simp⟩, by simp [SameDepth, depth?], ⟨Or.inl rfl, ?_⟩,
      hdeg⟩
    · exact List.Pairwise.sublist (List.erase_sublist (a := a) (l := ks)) hb.1
    · have : (ks.erase a).length ≤ ks.length :=
        List.Sublist.length_le (List.erase_sublist (a := a) (l := ks))
      have := hkc.2
      omega

/-! ## What the descent needs before it can be proved

`bounded_narrow_hi`/`bounded_widen_lo` re-bound a subtree by the key lifted out of it as the new
separator. `KeyCountOkAfter` is the occupancy bound `delRec` leaves: `KeyCountOk`, except that a
merge can take the root's last key. And `slot` is related to `takeWhile`. -/

mutual

/-- Narrow a tree's upper bound to any key that strictly dominates its contents. `delRec` needs
this once: the predecessor `takeMax` lifts out becomes the separator, so the subtree it came from
has to be re-bounded by it. -/
theorem bounded_narrow_hi {m : α} : ∀ {lo hi : Option α} {t : BTree α},
    Bounded lo hi t → (∀ b, Mem b t → b < m) → Bounded lo (some m) t
  | _, _, leaf _, hb, hlt =>
      ⟨hb.1, hb.2.1, fun y hy x hx => by
        rw [Option.mem_some_iff] at hy; subst hy; exact hlt x hx⟩
  | _, _, node _ _, hb, hlt => by
      obtain ⟨hbk, hlen, hbc⟩ := hb
      refine ⟨⟨hbk.1, hbk.2.1, fun y hy x hx => ?_⟩, hlen, ?_⟩
      · rw [Option.mem_some_iff] at hy
        subst hy
        exact hlt x (Or.inl hx)
      · exact boundedChildren_narrow_hi hbc (fun b hb' => hlt b (Or.inr hb'))

/-- `bounded_narrow_hi`'s companion, walking a node's children against `boundsList`: only the last
pair carries the tree's own upper bound, so only the last child changes. -/
theorem boundedChildren_narrow_hi {m : α} :
    ∀ {lo hi : Option α} {ks : List α} {cs : List (BTree α)},
      BoundedChildren (boundsList lo hi ks) cs → (∀ b, MemChildren b cs → b < m) →
      BoundedChildren (boundsList lo (some m) ks) cs
  | _, _, [], cs, hbc, hlt => by
      simp only [boundsList] at hbc ⊢
      cases cs with
      | nil => exact absurd hbc (by simp [BoundedChildren])
      | cons c cs' =>
          obtain ⟨hc, hcs⟩ := hbc
          refine ⟨bounded_narrow_hi hc (fun b hb' => hlt b (Or.inl hb')), ?_⟩
          cases cs' with
          | nil => trivial
          | cons _ _ => simp [BoundedChildren] at hcs
  | _, _, _ :: _, cs, hbc, hlt => by
      simp only [boundsList] at hbc ⊢
      cases cs with
      | nil => exact absurd hbc (by simp [BoundedChildren])
      | cons c cs' =>
          obtain ⟨hc, hcs⟩ := hbc
          exact ⟨hc, boundedChildren_narrow_hi hcs (fun b hb' => hlt b (Or.inr hb'))⟩

end

mutual

/-- The mirror: widen a tree's lower bound to any key it strictly dominates, for the successor
that `takeMin` lifts out. -/
theorem bounded_widen_lo {m : α} : ∀ {lo hi : Option α} {t : BTree α},
    Bounded lo hi t → (∀ b, Mem b t → m < b) → Bounded (some m) hi t
  | _, _, leaf _, hb, hgt =>
      ⟨hb.1, fun y hy x hx => by
        rw [Option.mem_some_iff] at hy; subst hy; exact hgt x hx, hb.2.2⟩
  | _, _, node _ _, hb, hgt => by
      obtain ⟨hbk, hlen, hbc⟩ := hb
      refine ⟨⟨hbk.1, fun y hy x hx => ?_, hbk.2.2⟩, hlen, ?_⟩
      · rw [Option.mem_some_iff] at hy
        subst hy
        exact hgt x (Or.inl hx)
      · exact boundedChildren_widen_lo hbc (fun b hb' => hgt b (Or.inr hb'))

/-- Only the first pair of `boundsList` carries the tree's own lower bound, so only the first
child changes. -/
theorem boundedChildren_widen_lo {m : α} :
    ∀ {lo hi : Option α} {ks : List α} {cs : List (BTree α)},
      BoundedChildren (boundsList lo hi ks) cs → (∀ b, MemChildren b cs → m < b) →
      BoundedChildren (boundsList (some m) hi ks) cs
  | _, _, [], cs, hbc, hgt => by
      simp only [boundsList] at hbc ⊢
      cases cs with
      | nil => exact absurd hbc (by simp [BoundedChildren])
      | cons c cs' =>
          obtain ⟨hc, hcs⟩ := hbc
          refine ⟨bounded_widen_lo hc (fun b hb' => hgt b (Or.inl hb')), ?_⟩
          cases cs' with
          | nil => trivial
          | cons _ _ => simp [BoundedChildren] at hcs
  | _, _, _ :: _, cs, hbc, hgt => by
      simp only [boundsList] at hbc ⊢
      cases cs with
      | nil => exact absurd hbc (by simp [BoundedChildren])
      | cons c cs' =>
          obtain ⟨hc, hcs⟩ := hbc
          exact ⟨bounded_widen_lo hc (fun b hb' => hgt b (Or.inl hb')), hcs⟩

end

/-- **What `delRec` leaves behind.** Identical to `KeyCountOk` except that an internal root is
allowed to have been emptied: CLRS's merge can take the root's last key, and `collapseRoot` is
what absorbs that. Away from the root the two agree, which `keyCountOkAfter_false` records. -/
def KeyCountOkAfter (deg : ℕ) (isRoot : Bool) : BTree α → Prop
  | leaf ks => (isRoot ∨ ks.length ≥ deg - 1) ∧ ks.length ≤ 2 * deg - 1
  | node ks cs => (isRoot ∨ deg - 1 ≤ ks.length) ∧ ks.length ≤ 2 * deg - 1 ∧
      ChildrenKeyCountOk deg cs

omit [LinearOrder α] in
/-- Away from the root, "after" is just `KeyCountOk`. -/
theorem keyCountOkAfter_false {deg : ℕ} {t : BTree α} :
    KeyCountOkAfter deg false t ↔ KeyCountOk deg false t := by
  cases t with
  | leaf ks => simp [KeyCountOkAfter, KeyCountOk]
  | node ks cs => simp [KeyCountOkAfter, KeyCountOk]

omit [LinearOrder α] in
/-- The root is the one node allowed to be short, so a legal non-root is a legal root. -/
theorem keyCountOk_root_of_nonRoot {deg : ℕ} (hdeg : 2 ≤ deg) {t : BTree α}
    (h : KeyCountOk deg false t) : KeyCountOk deg true t := by
  cases t with
  | leaf ks => exact ⟨Or.inl rfl, h.2⟩
  | node ks cs =>
      have hlow : deg - 1 ≤ ks.length := h.1
      exact ⟨show 1 ≤ ks.length by omega, h.2.1, h.2.2⟩

/-- **`collapseRoot` restores the root's own occupancy bound.** An internal root emptied by a merge
has exactly one child left — `Bounded` says so — and that child becomes the tree. This is the only
place a B-tree's height decreases, mirroring the root split that is the only place it increases. -/
theorem collapseRoot_spec {deg : ℕ} (hdeg : 2 ≤ deg) {lo hi : Option α} {t : BTree α}
    (hb : Bounded lo hi t) (hs : SameDepth t) (hk : KeyCountOkAfter deg true t) :
    Bounded lo hi (collapseRoot t) ∧ SameDepth (collapseRoot t) ∧
      KeyCountOk deg true (collapseRoot t) ∧ ∀ b, Mem b (collapseRoot t) ↔ Mem b t := by
  cases t with
  | leaf ks => exact ⟨hb, hs, ⟨Or.inl rfl, hk.2⟩, fun _ => Iff.rfl⟩
  | node ks cs =>
      cases ks with
      | nil =>
          obtain ⟨c, rfl⟩ : ∃ c, cs = [c] := by
            have hlen := hb.2.1
            simp only [List.length_nil] at hlen
            cases cs with
            | nil => simp at hlen
            | cons c cs' =>
                cases cs' with
                | nil => exact ⟨c, rfl⟩
                | cons _ _ => simp at hlen
          have hbc : Bounded lo hi c := by
            have := hb.2.2
            simp only [boundsList, BoundedChildren] at this
            exact this.1
          have hsc : SameDepth c := by
            simpa [SameDepth, depth?, childrenDepth?] using hs
          have hkc : KeyCountOk deg false c := hk.2.2.1
          have hcol : collapseRoot (node ([] : List α) [c]) = c := by simp only [collapseRoot]
          rw [hcol]
          refine ⟨hbc, hsc, keyCountOk_root_of_nonRoot hdeg hkc, fun b => ?_⟩
          simp only [mem_node, List.not_mem_nil, memChildren_cons, memChildren_nil, or_false,
            false_or]
      | cons k ks' =>
          have hcol : collapseRoot (node (k :: ks') cs) = node (k :: ks') cs := by
            simp only [collapseRoot]
          rw [hcol]
          exact ⟨hb, hs, ⟨show 1 ≤ (k :: ks').length by simp, hk.2.1, hk.2.2⟩, fun _ => Iff.rfl⟩

/-- `slot` cuts the key list exactly where `takeWhile` does. -/
theorem take_drop_slot (a : α) : ∀ ks : List α,
    ks.take (slot a ks) = ks.takeWhile (· < a) ∧ ks.drop (slot a ks) = ks.dropWhile (· < a)
  | [] => by simp [slot]
  | k :: ks => by
      obtain ⟨iht, ihd⟩ := take_drop_slot a ks
      by_cases h : k < a
      · have hslot : slot a (k :: ks) = slot a ks + 1 := by simp [slot, h]
        rw [hslot, List.take_succ_cons, List.drop_succ_cons, iht, ihd]
        simp [h]
      · have hslot : slot a (k :: ks) = 0 := by simp [slot, h]
        rw [hslot, List.take_zero, List.drop_zero]
        simp [h]

/-- The descent never points past the end of a node. -/
theorem slot_le (a : α) (ks : List α) : slot a ks ≤ ks.length := by
  have h := congrArg List.length
    (List.takeWhile_append_dropWhile (p := fun x => decide (x < a)) (l := ks))
  simp only [List.length_append] at h
  simp only [slot]
  omega

/-- Everything left of the slot is strictly below the key being deleted. -/
theorem mem_takeWhile_lt {a : α} : ∀ {ks : List α} {x : α}, x ∈ ks.takeWhile (· < a) → x < a
  | [], x, hx => by simp at hx
  | k :: ks, x, hx => by
      by_cases h : k < a
      · have he : (k :: ks).takeWhile (· < a) = k :: ks.takeWhile (· < a) := by
          simp [h]
        rw [he] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h
        · exact mem_takeWhile_lt hx
      · have he : (k :: ks).takeWhile (· < a) = [] := by simp [h]
        rw [he] at hx
        simp at hx

/-- And the first key at or right of the slot is not below it — which is why `delRec` only has to
compare against that one key to know whether it has found `a`. -/
theorem not_lt_head_dropWhile {a k : α} : ∀ {ks kr : List α},
    ks.dropWhile (· < a) = k :: kr → ¬ (k < a)
  | [], kr, h => by simp at h
  | x :: xs, kr, h => by
      by_cases hx : x < a
      · have he : (x :: xs).dropWhile (· < a) = xs.dropWhile (· < a) := by
          simp [hx]
        rw [he] at h
        exact not_lt_head_dropWhile h
      · have he : (x :: xs).dropWhile (· < a) = x :: xs := by
          simp [hx]
        rw [he] at h
        simp only [List.cons.injEq] at h
        rw [← h.1]
        exact hx

/-- The node the descent has reached, opened at the slot: the two children flanking the key `a`
would occupy if it were here, with everything `bounded_pair` gives about them and the two ways of
putting them back. Every branch of `delRec` that looks at a key needs this. -/
theorem slot_pair {deg e : ℕ} {isRoot : Bool} {a : α} {lo hi : Option α}
    {ks : List α} {cs : List (BTree α)} {k : α} {kr : List α}
    {c r : BTree α} {rest : List (BTree α)}
    (hb : Bounded lo hi (node ks cs)) (hd : childrenDepth? cs = some e)
    (hk : KeyCountOk deg isRoot (node ks cs))
    (hkr : ks.drop (slot a ks) = k :: kr) (hcr : cs.drop (slot a ks) = c :: r :: rest) :
    ∃ kl cl, ks.take (slot a ks) = kl ∧ cs.take (slot a ks) = cl ∧
      ks = kl ++ k :: kr ∧ cs = cl ++ c :: r :: rest ∧ cl.length = kl.length ∧
      Legal deg (loAt lo kl) (some k) e c ∧ Legal deg (some k) (hiAt hi kr) e r ∧
      (∀ x ∈ loAt lo kl, x < k) ∧ (∀ y ∈ hiAt hi kr, k < y) ∧
      (∀ (c' : BTree α) (k' : α) (r' : BTree α), Bounded (loAt lo kl) (some k') c' →
         Bounded (some k') (hiAt hi kr) r' → (∀ x ∈ loAt lo kl, x < k') →
         (∀ y ∈ hiAt hi kr, k' < y) →
         Bounded lo hi (node (kl ++ k' :: kr) (cl ++ c' :: r' :: rest))) ∧
      (∀ m : BTree α, Bounded (loAt lo kl) (hiAt hi kr) m →
         Bounded lo hi (node (kl ++ kr) (cl ++ m :: rest))) := by
  have harity : cs.length = ks.length + 1 := hb.2.1
  have hsl : slot a ks ≤ ks.length := slot_le a ks
  refine ⟨ks.take (slot a ks), cs.take (slot a ks), rfl, rfl, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.take_append_drop (slot a ks) ks]
    rw [hkr]
  · conv_lhs => rw [← List.take_append_drop (slot a ks) cs]
    rw [hcr]
  · have h1 : (ks.take (slot a ks)).length = slot a ks := by
      rw [List.length_take]; omega
    have h2 : (cs.take (slot a ks)).length = slot a ks := by
      rw [List.length_take]; omega
    omega
  · have hks : ks = ks.take (slot a ks) ++ k :: kr := by
      conv_lhs => rw [← List.take_append_drop (slot a ks) ks]
      rw [hkr]
    have hcs : cs = cs.take (slot a ks) ++ c :: r :: rest := by
      conv_lhs => rw [← List.take_append_drop (slot a ks) cs]
      rw [hcr]
    have hlen : (cs.take (slot a ks)).length = (ks.take (slot a ks)).length := by
      have h1 : (ks.take (slot a ks)).length = slot a ks := by
        rw [List.length_take]; omega
      have h2 : (cs.take (slot a ks)).length = slot a ks := by
        rw [List.length_take]; omega
      omega
    have hb' : Bounded lo hi
        (node (ks.take (slot a ks) ++ k :: kr) (cs.take (slot a ks) ++ c :: r :: rest)) := by
      rw [← hks, ← hcs]; exact hb
    obtain ⟨⟨hbc, hbr, hlok, hkhi⟩, hput, hmerge⟩ :=
      bounded_pair (ks.take (slot a ks)) (cs.take (slot a ks)) hlen lo hi k kr c r rest hb'
    have hmemc : c ∈ cs := by rw [hcs]; simp
    have hmemr : r ∈ cs := by rw [hcs]; simp
    have hcne : cs ≠ [] := by rw [hcs]; simp
    have hdall : ∀ x ∈ cs, depth? x = some e := (childrenDepth?_iff hcne).mp hd
    have hkall : ∀ x ∈ cs, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk.2.2
    exact ⟨⟨hbc, hdall c hmemc, hkall c hmemc⟩, ⟨hbr, hdall r hmemr, hkall r hmemr⟩,
      hlok, hkhi, hput, hmerge⟩

/-- Every key and every child strictly left of a node's key sits strictly below it. -/
theorem lt_of_memChildren_left : ∀ (kl : List α) (cl : List (BTree α)), cl.length = kl.length →
    ∀ (lo hi : Option α) (k : α) (kr : List α) (cs2 : List (BTree α)) (b : α),
      Bounded lo hi (node (kl ++ k :: kr) (cl ++ cs2)) → (b ∈ kl ∨ MemChildren b cl) → b < k := by
  intro kl
  induction kl with
  | nil =>
      intro cl hlen lo hi k kr cs2 b _ hbm
      obtain rfl : cl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp at hbm
  | cons k0 kl' ih =>
      intro cl hlen lo hi k kr cs2 b hb hbm
      obtain ⟨c0, cl', rfl⟩ : ∃ c0 cl', cl = c0 :: cl' := by
        cases cl with
        | nil => simp at hlen
        | cons c0 cl' => exact ⟨c0, cl', rfl⟩
      have hlen' : cl'.length = kl'.length := by simpa using hlen
      obtain ⟨hbk, hlenb, hbc⟩ := hb
      simp only [List.cons_append, boundsList, BoundedChildren] at hbc
      obtain ⟨hbc0, hbrest⟩ := hbc
      have hk0k : k0 < k := (List.pairwise_cons.mp hbk.1).1 k (by simp)
      have hsub : Bounded (some k0) hi (node (kl' ++ k :: kr) (cl' ++ cs2)) := by
        refine ⟨hbk.of_cons, ?_, hbrest⟩
        simp only [List.length_append, List.length_cons] at hlenb ⊢
        omega
      rcases hbm with hbm | hbm
      · rcases List.mem_cons.mp hbm with rfl | hbm
        · exact hk0k
        · exact ih cl' hlen' (some k0) hi k kr cs2 b hsub (Or.inl hbm)
      · rcases (memChildren_cons ..).mp hbm with hbm | hbm
        · exact lt_trans ((mem_bounds_of_bounded hbc0 hbm).2 k0 rfl) hk0k
        · exact ih cl' hlen' (some k0) hi k kr cs2 b hsub (Or.inr hbm)

/-- And everything strictly right of it sits strictly above. Once the prefix is stripped the node
starting at `k` bounds its own tail below by `k`, so no second induction is needed. -/
theorem gt_of_memChildren_right : ∀ (kl : List α) (cl : List (BTree α)), cl.length = kl.length →
    ∀ (lo hi : Option α) (k : α) (kr : List α) (c : BTree α) (cr : List (BTree α)) (b : α),
      Bounded lo hi (node (kl ++ k :: kr) (cl ++ c :: cr)) →
      (b ∈ kr ∨ MemChildren b cr) → k < b := by
  intro kl
  induction kl with
  | nil =>
      intro cl hlen lo hi k kr c cr b hb hbm
      obtain rfl : cl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp only [List.nil_append] at hb
      obtain ⟨hbk, hlenb, hbc⟩ := hb
      simp only [boundsList, BoundedChildren] at hbc
      have hsub : Bounded (some k) hi (node kr cr) := by
        refine ⟨hbk.of_cons, ?_, hbc.2⟩
        simp only [List.length_cons] at hlenb
        omega
      exact (mem_bounds_of_bounded hsub (by rcases hbm with h | h; exacts [Or.inl h, Or.inr h])).1
        k rfl
  | cons k0 kl' ih =>
      intro cl hlen lo hi k kr c cr b hb hbm
      obtain ⟨c0, cl', rfl⟩ : ∃ c0 cl', cl = c0 :: cl' := by
        cases cl with
        | nil => simp at hlen
        | cons c0 cl' => exact ⟨c0, cl', rfl⟩
      have hlen' : cl'.length = kl'.length := by simpa using hlen
      obtain ⟨hbk, hlenb, hbc⟩ := hb
      simp only [List.cons_append, boundsList, BoundedChildren] at hbc
      have hsub : Bounded (some k0) hi (node (kl' ++ k :: kr) (cl' ++ c :: cr)) := by
        refine ⟨hbk.of_cons, ?_, hbc.2⟩
        simp only [List.length_append, List.length_cons] at hlenb ⊢
        omega
      exact ih cl' hlen' (some k0) hi k kr c cr b hsub hbm

/-! ## `delete`, against `DeleteSpec`

`delRec.induct` has nine branches; three are unreachable. `spot_outside_ne` says the deleted key
is in the child the descent enters or nowhere in the node. `collapseRoot_spec` turns
`KeyCountOkAfter` back into `KeyCountOk`. -/

/-- Sharper than `lt_of_memChildren_left`: a child strictly left of a key is below *some key of the
prefix*, not merely below the key itself. That is what rules out the key being deleted hiding in a
child the descent walked past. -/
theorem lt_key_of_memChildren_left :
    ∀ (kl : List α) (cl : List (BTree α)), cl.length = kl.length →
      ∀ (lo hi : Option α) (ks2 : List α) (cs2 : List (BTree α)) (b : α),
        Bounded lo hi (node (kl ++ ks2) (cl ++ cs2)) → MemChildren b cl → ∃ x ∈ kl, b < x := by
  intro kl
  induction kl with
  | nil =>
      intro cl hlen lo hi ks2 cs2 b _ hbm
      obtain rfl : cl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      simp at hbm
  | cons k0 kl' ih =>
      intro cl hlen lo hi ks2 cs2 b hb hbm
      obtain ⟨c0, cl', rfl⟩ : ∃ c0 cl', cl = c0 :: cl' := by
        cases cl with
        | nil => simp at hlen
        | cons c0 cl' => exact ⟨c0, cl', rfl⟩
      have hlen' : cl'.length = kl'.length := by simpa using hlen
      obtain ⟨hbk, hlenb, hbc⟩ := hb
      simp only [List.cons_append, boundsList, BoundedChildren] at hbc
      obtain ⟨hbc0, hbrest⟩ := hbc
      have hsub : Bounded (some k0) hi (node (kl' ++ ks2) (cl' ++ cs2)) := by
        refine ⟨hbk.of_cons, ?_, hbrest⟩
        simp only [List.length_append, List.length_cons] at hlenb ⊢
        omega
      rcases (memChildren_cons ..).mp hbm with hbm | hbm
      · exact ⟨k0, by simp, (mem_bounds_of_bounded hbc0 hbm).2 k0 rfl⟩
      · obtain ⟨x, hx, hbx⟩ := ih cl' hlen' (some k0) hi ks2 cs2 b hsub hbm
        exact ⟨x, List.mem_cons_of_mem _ hx, hbx⟩

/-- **The key being deleted is in the hole, or nowhere.** If `a` sits in the child the descent is
about to enter, it sits in no other part of the node -- not in a key, not in a sibling. The
ordering invariant is what forbids it: the target's flanking bounds separate it from everything
else the node holds. -/
theorem spot_outside_ne {deg d : ℕ} {lo hi : Option α} {sp : Spot α} {a : α}
    (h : SpotLegal deg lo hi d sp) (hmem : Mem a sp.target) :
    ∀ b, (b ∈ sp.keysL ∨ MemChildren b sp.childrenL ∨
          b ∈ sp.keysR ∨ MemChildren b sp.childrenR) → b ≠ a := by
  obtain ⟨hb, hd, hk, hlen⟩ := h
  have hb0 : Bounded lo hi
      (node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR)) := hb
  obtain ⟨hbt, -⟩ :=
    bounded_hole sp.keysL sp.childrenL hlen lo hi sp.keysR sp.childrenR sp.target hb0
  have hlow : ∀ x ∈ loAt lo sp.keysL, x < a := (mem_bounds_of_bounded hbt hmem).1
  have hhigh : ∀ y ∈ hiAt hi sp.keysR, a < y := (mem_bounds_of_bounded hbt hmem).2
  have harity := hb0.2.1
  simp only [List.length_append, List.length_cons] at harity
  have hlenR : sp.childrenR.length = sp.keysR.length := by omega
  have hpl : sp.keysL.Pairwise (· < ·) := (List.pairwise_append.mp hb0.1.1).1
  have hpr : sp.keysR.Pairwise (· < ·) := (List.pairwise_append.mp hb0.1.1).2.1
  intro b hbm
  rcases hbm with hbm | hbm | hbm | hbm
  · -- a key left of the hole: at most the last of them, which is below `a`
    cases hkl : sp.keysL.getLast? with
    | none =>
        rw [List.getLast?_eq_none_iff] at hkl
        rw [hkl] at hbm
        simp at hbm
    | some klast =>
        have hla : klast < a := hlow klast (by simp [loAt, hkl])
        obtain ⟨kl', hkl'⟩ : ∃ kl', sp.keysL = kl' ++ [klast] :=
          ⟨sp.keysL.dropLast, (dropLast_getLast_eq hkl).symm⟩
        rw [hkl'] at hbm hpl
        rcases List.mem_append.mp hbm with hbm | hbm
        · exact ne_of_lt (lt_trans
            ((List.pairwise_append.mp hpl).2.2 b hbm klast (by simp)) hla)
        · simp only [List.mem_singleton] at hbm
          subst hbm
          exact ne_of_lt hla
  · -- a child left of the hole: below some key of the prefix, which is below `a`
    cases hkl : sp.keysL.getLast? with
    | none =>
        rw [List.getLast?_eq_none_iff] at hkl
        have hnil : sp.childrenL = [] :=
          List.eq_nil_of_length_eq_zero (by rw [hlen, hkl]; simp)
        rw [hnil] at hbm
        simp at hbm
    | some klast =>
        have hla : klast < a := hlow klast (by simp [loAt, hkl])
        obtain ⟨x, hx, hbx⟩ :=
          lt_key_of_memChildren_left sp.keysL sp.childrenL hlen lo hi sp.keysR
            (sp.target :: sp.childrenR) b hb0 hbm
        obtain ⟨kl', hkl'⟩ : ∃ kl', sp.keysL = kl' ++ [klast] :=
          ⟨sp.keysL.dropLast, (dropLast_getLast_eq hkl).symm⟩
        rw [hkl'] at hx hpl
        have hxle : x ≤ klast := by
          rcases List.mem_append.mp hx with hx | hx
          · exact le_of_lt ((List.pairwise_append.mp hpl).2.2 x hx klast (by simp))
          · simp only [List.mem_singleton] at hx
            exact le_of_eq hx
        exact ne_of_lt (lt_trans hbx (lt_of_le_of_lt hxle hla))
  · -- a key right of the hole: at least the first of them, which is above `a`
    cases hkr : sp.keysR with
    | nil => rw [hkr] at hbm; simp at hbm
    | cons k0 kr' =>
        have hak : a < k0 := hhigh k0 (by simp [hiAt, hkr])
        rw [hkr] at hbm hpr
        rcases List.mem_cons.mp hbm with rfl | hbm
        · exact (ne_of_lt hak).symm
        · exact (ne_of_lt (lt_trans hak ((List.pairwise_cons.mp hpr).1 b hbm))).symm
  · -- a child right of the hole: above the first key right of it
    cases hkr : sp.keysR with
    | nil =>
        have hnil : sp.childrenR = [] :=
          List.eq_nil_of_length_eq_zero (by rw [hlenR, hkr]; simp)
        rw [hnil] at hbm
        simp at hbm
    | cons k0 kr' =>
        have hak : a < k0 := hhigh k0 (by simp [hiAt, hkr])
        have hb1 : Bounded lo hi
            (node (sp.keysL ++ k0 :: kr') (sp.childrenL ++ sp.target :: sp.childrenR)) := by
          rw [← hkr]; exact hb0
        exact (ne_of_lt (lt_trans hak
          (gt_of_memChildren_right sp.keysL sp.childrenL hlen lo hi k0 kr' sp.target
            sp.childrenR b hb1 (Or.inr hbm)))).symm

theorem delRec_spec {deg : ℕ} (hdeg : 2 ≤ deg) (a : α) :
    ∀ (t : BTree α) (d : ℕ) (lo hi : Option α) (isRoot : Bool),
      Bounded lo hi t → depth? t = some d → KeyCountOk deg isRoot t →
      (isRoot = true ∨ hasSpare deg t = true) →
      (∀ b, Mem b (delRec deg a t).1 ↔ (b ≠ a ∧ Mem b t)) ∧
      ((delRec deg a t).2 = true ↔ Mem a t) ∧
      Bounded lo hi (delRec deg a t).1 ∧
      depth? (delRec deg a t).1 = some d ∧
      KeyCountOkAfter deg isRoot (delRec deg a t).1 := by
  intro t
  induction t using delRec.induct (deg := deg) (a := a) with
  | case1 ks =>
      intro d lo hi isRoot hb hd hk hspare
      have hnd : ks.Nodup := nodup_of_boundedKeys hb
      have hsub := List.erase_sublist (a := a) (l := ks)
      have hle : (ks.erase a).length ≤ ks.length := List.Sublist.length_le hsub
      have hge : ks.length ≤ (ks.erase a).length + 1 := by
        rw [List.length_erase]
        split <;> omega
      have hd0 : d = 0 := by simpa [depth?] using hd.symm
      subst hd0
      have hdel : delRec deg a (leaf ks) = (leaf (ks.erase a), decide (a ∈ ks)) := by
        simp [delRec]
      rw [hdel]
      refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
      · simpa using hnd.mem_erase_iff
      · simp
      · refine ⟨List.Pairwise.sublist hsub hb.1, ?_, ?_⟩
        · exact fun l hl x hx => hb.2.1 l hl x (hsub.mem hx)
        · exact fun y hy x hx => hb.2.2 y hy x (hsub.mem hx)
      · simp [depth?]
      · have hub : ks.length ≤ 2 * deg - 1 := hk.2
        refine ⟨?_, by omega⟩
        cases isRoot with
        | true => exact Or.inl rfl
        | false =>
            refine Or.inr ?_
            have hs : deg ≤ ks.length := by
              have h0 := hspare.resolve_left (by simp)
              simp only [hasSpare, nodeKeys_leaf] at h0
              exact of_decide_eq_true h0
            omega
  | case2 ks cs k kr c r rest hkr hcr hlt sp ih =>
      intro d lo hi isRoot hb hd hk hspare
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      obtain ⟨kl, cl, rfl, rfl, hks, hcs, hlen, hlc, hlr, hlok, hkhi, hput, hmergeput⟩ :=
        slot_pair (a := a) hb he hk hkr hcr
      set sp0 : Spot α :=
        ⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ with hsp0
      have hsp0n : sp0.node = node ks cs := by
        simp only [hsp0, Spot.node]
        rw [← hks, ← hcs]
      have hsp0c : sp0.children = cs := by
        simp only [hsp0, Spot.children]
        rw [← hcs]
      have hleg0 : SpotLegal deg lo hi e sp0 :=
        ⟨by rw [hsp0n]; exact hb, by rw [hsp0c]; exact he, by rw [hsp0c]; exact hk.2.2, hlen⟩
      have hsib : sp0.childrenL ≠ [] ∨ sp0.childrenR ≠ [] := Or.inr (by simp [hsp0])
      obtain ⟨hleg', hmemiff, hmono, hspare', hcnt1, hcnt2⟩ := ensureSpare_spec hdeg hleg0 hsib
      have hspdef : ensureSpare deg sp0 = sp := rfl
      rw [hspdef] at hleg' hmemiff hmono hspare' hcnt1 hcnt2
      obtain ⟨hb', hd', hk', hlen'⟩ := hleg'
      have hb0' : Bounded lo hi
          (node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR)) := hb'
      obtain ⟨hbt, hputh⟩ :=
        bounded_hole sp.keysL sp.childrenL hlen' lo hi sp.keysR sp.childrenR sp.target hb0'
      have hcne : sp.children ≠ [] := by simp [Spot.children]
      have hdall : ∀ x ∈ sp.children, depth? x = some e := (childrenDepth?_iff hcne).mp hd'
      have hkall : ∀ x ∈ sp.children, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk'
      have hmt : sp.target ∈ sp.children := by simp [Spot.children]
      obtain ⟨ihmem, ihfound, ihb, ihdep, ihk⟩ :=
        ih e (loAt lo sp.keysL) (hiAt hi sp.keysR) false hbt (hdall sp.target hmt)
          (hkall sp.target hmt) (Or.inr hspare')
      have ihk' : KeyCountOk deg false (delRec deg a sp.target).1 := keyCountOkAfter_false.mp ihk
      -- `a` sits below the key at the slot, so if the node holds it at all it holds it in `c`
      have hbl : Bounded lo hi
          (node (ks.take (slot a ks) ++ k :: kr) (cs.take (slot a ks) ++ c :: r :: rest)) := by
        rw [← hks, ← hcs]; exact hb
      have hklt : ∀ x ∈ ks.take (slot a ks), x < a := by
        intro x hx
        exact mem_takeWhile_lt (by rw [← (take_drop_slot a ks).1]; exact hx)
      have hainc : Mem a (node ks cs) → Mem a c := by
        intro hmn
        rw [hks, hcs] at hmn
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append,
          List.mem_cons] at hmn
        rcases hmn with (hx | rfl | hx) | (hx | hx | hx | hx)
        · exact absurd (hklt a hx) (lt_irrefl a)
        · exact absurd hlt (lt_irrefl a)
        · exact absurd (lt_trans hlt (gt_of_memChildren_right (ks.take (slot a ks))
            (cs.take (slot a ks)) hlen lo hi k kr c (r :: rest) a hbl (Or.inl hx))) (lt_irrefl a)
        · obtain ⟨x, hxm, hax⟩ := lt_key_of_memChildren_left (ks.take (slot a ks))
            (cs.take (slot a ks)) hlen lo hi (k :: kr) (c :: r :: rest) a hbl hx
          exact absurd (lt_trans hax (hklt x hxm)) (lt_irrefl a)
        · exact hx
        · exact absurd (lt_trans hlt (gt_of_memChildren_right (ks.take (slot a ks))
            (cs.take (slot a ks)) hlen lo hi k kr c (r :: rest) a hbl
            (Or.inr (Or.inl hx)))) (lt_irrefl a)
        · exact absurd (lt_trans hlt (gt_of_memChildren_right (ks.take (slot a ks))
            (cs.take (slot a ks)) hlen lo hi k kr c (r :: rest) a hbl
            (Or.inr (Or.inr hx)))) (lt_irrefl a)
      have hat : Mem a (node ks cs) ↔ Mem a sp.target := by
        constructor
        · intro hmn
          exact hmono a (by rw [hsp0]; exact hainc hmn)
        · intro hmt2
          rw [← hsp0n, ← hmemiff a]
          exact Or.inr ((memChildren_iff a _).mpr ⟨sp.target, by simp, hmt2⟩)
      have houts : ∀ b, (b ∈ sp.keysL ∨ MemChildren b sp.childrenL ∨
          b ∈ sp.keysR ∨ MemChildren b sp.childrenR) → b ≠ a := by
        intro b hbm hba
        have hmn : Mem a sp.node := by
          have hopen : Mem a (node (sp.keysL ++ sp.keysR)
              (sp.childrenL ++ sp.target :: sp.childrenR)) := by
            simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append]
            rcases hbm with hx | hx | hx | hx
            · exact Or.inl (Or.inl (hba ▸ hx))
            · exact Or.inr (Or.inl (hba ▸ hx))
            · exact Or.inl (Or.inr (hba ▸ hx))
            · exact Or.inr (Or.inr (Or.inr (hba ▸ hx)))
          exact hopen
        have hta : Mem a sp.target := hat.mp (by rw [← hsp0n, ← hmemiff a]; exact hmn)
        exact spot_outside_ne ⟨hb', hd', hk', hlen'⟩ hta b hbm hba
      have hdel : delRec deg a (node ks cs)
          = (({ ensureSpare deg sp0 with
                  target := (delRec deg a (ensureSpare deg sp0).target).1 } : Spot α).node,
             (delRec deg a (ensureSpare deg sp0).target).2) := by
        rw [delRec]
        split
        · rename_i k1 kr1 c1 r1 rest1 h1 h2
          rw [hkr] at h1
          rw [hcr] at h2
          simp only [List.cons.injEq] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1
          obtain ⟨rfl, rfl, rfl⟩ := h2
          simp [hlt, hsp0]
        · rename_i c1 h1 h2
          rw [hkr] at h1
          simp at h1
        · rename_i h1 h2
          exact (h1 k kr c r rest hkr hcr).elim
      rw [hdel, hspdef]
      have hresn : ({ sp with target := (delRec deg a sp.target).1 } : Spot α).node
          = node (sp.keysL ++ sp.keysR)
                 (sp.childrenL ++ (delRec deg a sp.target).1 :: sp.childrenR) := rfl
      have hspn : sp.node
          = node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR) := rfl
      have hmemL : ∀ x ∈ sp.childrenL, x ∈ sp.children := by
        intro x hx; simp [Spot.children, hx]
      have hmemR : ∀ x ∈ sp.childrenR, x ∈ sp.children := by
        intro x hx; simp [Spot.children, hx]
      refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
      · rw [hresn, ← hsp0n, ← hmemiff b, hspn]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append]
        constructor
        · rintro ((hx | hx) | (hx | hx | hx))
          · exact ⟨houts b (Or.inl hx), Or.inl (Or.inl hx)⟩
          · exact ⟨houts b (Or.inr (Or.inr (Or.inl hx))), Or.inl (Or.inr hx)⟩
          · exact ⟨houts b (Or.inr (Or.inl hx)), Or.inr (Or.inl hx)⟩
          · exact ⟨((ihmem b).mp hx).1, Or.inr (Or.inr (Or.inl ((ihmem b).mp hx).2))⟩
          · exact ⟨houts b (Or.inr (Or.inr (Or.inr hx))), Or.inr (Or.inr (Or.inr hx))⟩
        · rintro ⟨hne, (hx | hx) | (hx | hx | hx)⟩
          · exact Or.inl (Or.inl hx)
          · exact Or.inl (Or.inr hx)
          · exact Or.inr (Or.inl hx)
          · exact Or.inr (Or.inr (Or.inl ((ihmem b).mpr ⟨hne, hx⟩)))
          · exact Or.inr (Or.inr (Or.inr hx))
      · rw [ihfound]
        exact hat.symm
      · rw [hresn]
        exact hputh _ ihb
      · rw [hresn]
        simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hdall x (hmemL x hx)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ihdep
          · exact hdall x (hmemR x hx)
      · rw [hresn]
        have hk0 : (nodeKeys sp0.node).length = ks.length := by rw [hsp0n]; simp
        have hkl : (nodeKeys sp.node).length = (sp.keysL ++ sp.keysR).length := by rw [hspn]; simp
        rw [hkl, hk0] at hcnt1 hcnt2
        have hub : ks.length ≤ 2 * deg - 1 := hk.2.1
        refine ⟨?_, by omega, ?_⟩
        · cases isRoot with
          | true => exact Or.inl rfl
          | false =>
              refine Or.inr ?_
              have hs : deg ≤ ks.length := by
                have h0 := hspare.resolve_left (by simp)
                simp only [hasSpare, nodeKeys_node] at h0
                exact of_decide_eq_true h0
              omega
        · refine (childrenKeyCountOk_iff _).mpr ?_
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hkall x (hmemL x hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ihk'
            · exact hkall x (hmemR x hx)
  | case3 ks cs k kr c r rest hkr hcr hnlt hsc c' pred htm =>
      intro d lo hi isRoot hb hd hk hspare
      have hdel : delRec deg a (node ks cs)
          = (node (ks.take (slot a ks) ++ pred :: kr) (cs.take (slot a ks) ++ c' :: r :: rest),
             true) := by
        rw [delRec]
        split
        · rename_i k1 kr1 c1 r1 rest1 h1 h2
          rw [hkr] at h1
          rw [hcr] at h2
          simp only [List.cons.injEq] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1
          obtain ⟨rfl, rfl, rfl⟩ := h2
          simp [hnlt, hsc, htm]
        · rename_i c1 h1 h2
          rw [hkr] at h1
          simp at h1
        · rename_i h1 h2
          exact (h1 k kr c r rest hkr hcr).elim
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      obtain ⟨kl, cl, htk, htc, hks, hcs, hlen, hlc, hlr, hlok, hkhi, hput, hmerge⟩ :=
        slot_pair (a := a) hb he hk hkr hcr
      -- `a` is not below the key at the slot and the key is not below `a`: they are equal.
      have hnkl : ¬ (k < a) :=
        not_lt_head_dropWhile (by rw [← (take_drop_slot a ks).2]; exact hkr)
      have hak : a = k := le_antisymm (not_lt.mp hnkl) (not_lt.mp hnlt)
      subst hak
      have hb' : Bounded lo hi (node (kl ++ a :: kr) (cl ++ c :: r :: rest)) := by
        rw [← hks, ← hcs]; exact hb
      obtain ⟨t', m, heq, hmemm, hmax, hiffm, hltm, hlegm⟩ :=
        takeMax_spec hdeg c e (loAt lo kl) (some a) hlc hsc
      rw [htm] at heq
      simp only [Prod.mk.injEq, Option.some.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hpreda : pred < a := (mem_bounds_of_bounded hlc.1 hmemm).2 a rfl
      have hleft : ∀ b, (b ∈ kl ∨ MemChildren b cl) → b < a :=
        fun b hbm => lt_of_memChildren_left kl cl hlen lo hi a kr (c :: r :: rest) b hb' hbm
      have hright : ∀ b, (b ∈ kr ∨ MemChildren b (r :: rest)) → a < b :=
        fun b hbm => gt_of_memChildren_right kl cl hlen lo hi a kr c (r :: rest) b hb' hbm
      have hinc : ∀ b, Mem b c → b < a := fun b hbm => (mem_bounds_of_bounded hlc.1 hbm).2 a rfl
      rw [hdel, htk, htc]
      refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
      · rw [hks, hcs]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append, List.mem_cons]
        constructor
        · rintro ((hbm | rfl | hbm) | (hbm | hbm | hbm | hbm))
          · exact ⟨ne_of_lt (hleft b (Or.inl hbm)), Or.inl (Or.inl hbm)⟩
          · exact ⟨ne_of_lt hpreda, Or.inr (Or.inr (Or.inl hmemm))⟩
          · exact ⟨(ne_of_lt (hright b (Or.inl hbm))).symm, Or.inl (Or.inr (Or.inr hbm))⟩
          · exact ⟨ne_of_lt (hleft b (Or.inr hbm)), Or.inr (Or.inl hbm)⟩
          · refine ⟨ne_of_lt (hinc b ((hiffm b).mp hbm).1), ?_⟩
            exact Or.inr (Or.inr (Or.inl ((hiffm b).mp hbm).1))
          · exact ⟨(ne_of_lt (hright b (Or.inr (Or.inl hbm)))).symm,
                   Or.inr (Or.inr (Or.inr (Or.inl hbm)))⟩
          · exact ⟨(ne_of_lt (hright b (Or.inr (Or.inr hbm)))).symm,
                   Or.inr (Or.inr (Or.inr (Or.inr hbm)))⟩
        · rintro ⟨hne, (hbm | rfl | hbm) | (hbm | hbm | hbm | hbm)⟩
          · exact Or.inl (Or.inl hbm)
          · exact absurd rfl hne
          · exact Or.inl (Or.inr (Or.inr hbm))
          · exact Or.inr (Or.inl hbm)
          · by_cases hbp : b = pred
            · exact Or.inl (Or.inr (Or.inl hbp))
            · exact Or.inr (Or.inr (Or.inl ((hiffm b).mpr ⟨hbm, hbp⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl hbm)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hbm)))
      · simp only [true_iff]
        rw [hks]
        exact Or.inl (by simp)
      · refine hput c' pred r ?_ ?_ ?_ ?_
        · exact bounded_narrow_hi hlegm.1 hltm
        · refine bounded_widen_lo hlr.1 (fun b hbm => ?_)
          exact lt_trans hpreda ((mem_bounds_of_bounded hlr.1 hbm).1 a rfl)
        · exact fun x hx => (mem_bounds_of_bounded hlc.1 hmemm).1 x hx
        · exact fun y hy => lt_trans hpreda (hkhi y hy)
      · simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        have hall : ∀ y ∈ cs, depth? y = some e :=
          (childrenDepth?_iff (by rw [hcs]; simp)).mp he
        rcases List.mem_append.mp hx with hx | hx
        · exact hall x (by rw [hcs]; simp [hx])
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hlegm.2.1
          · exact hall x (by rw [hcs]; simp [hx])
      · have hkall : ∀ x ∈ cs, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk.2.2
        have hlenk : (kl ++ pred :: kr).length = ks.length := by
          rw [hks]; simp
        refine ⟨?_, ?_, ?_⟩
        · cases isRoot with
          | true => exact Or.inl rfl
          | false =>
              refine Or.inr ?_
              rw [hlenk]
              exact hk.1
        · rw [hlenk]
          exact hk.2.1
        · refine (childrenKeyCountOk_iff _).mpr ?_
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hkall x (by rw [hcs]; simp [hx])
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hlegm.2.2
            · exact hkall x (by rw [hcs]; simp [hx])
  | case4 ks cs k kr c r rest hkr hcr hnlt hsc c' htm =>
      -- Unreachable: `c` has a key to spare, so `takeMax` cannot come back empty.
      intro d lo hi isRoot hb hd hk hspare
      exfalso
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      obtain ⟨kl, cl, htk, htc, hks, hcs, hlen, hlc, hlr, hlok, hkhi, hput, hmerge⟩ :=
        slot_pair (a := a) hb he hk hkr hcr
      obtain ⟨t', m, heq, -, -, -, -, -⟩ := takeMax_spec hdeg c e (loAt lo kl) (some k) hlc hsc
      rw [htm] at heq
      simp at heq
  | case5 ks cs k kr c r rest hkr hcr hnlt hnsc hsr r' succ htm =>
      intro d lo hi isRoot hb hd hk hspare
      have hdel : delRec deg a (node ks cs)
          = (node (ks.take (slot a ks) ++ succ :: kr) (cs.take (slot a ks) ++ c :: r' :: rest),
             true) := by
        rw [delRec]
        split
        · rename_i k1 kr1 c1 r1 rest1 h1 h2
          rw [hkr] at h1
          rw [hcr] at h2
          simp only [List.cons.injEq] at h1 h2
          obtain ⟨rfl, rfl⟩ := h1
          obtain ⟨rfl, rfl, rfl⟩ := h2
          simp [hnlt, hnsc, hsr, htm]
        · rename_i c1 h1 h2
          rw [hkr] at h1
          simp at h1
        · rename_i h1 h2
          exact (h1 k kr c r rest hkr hcr).elim
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      obtain ⟨kl, cl, htk, htc, hks, hcs, hlen, hlc, hlr, hlok, hkhi, hput, hmerge⟩ :=
        slot_pair (a := a) hb he hk hkr hcr
      have hnkl : ¬ (k < a) :=
        not_lt_head_dropWhile (by rw [← (take_drop_slot a ks).2]; exact hkr)
      have hak : a = k := le_antisymm (not_lt.mp hnkl) (not_lt.mp hnlt)
      subst hak
      have hb' : Bounded lo hi (node (kl ++ a :: kr) (cl ++ c :: r :: rest)) := by
        rw [← hks, ← hcs]; exact hb
      obtain ⟨t', m, heq, hmemm, hmin, hiffm, hgtm, hlegm⟩ :=
        takeMin_spec hdeg r e (some a) (hiAt hi kr) hlr hsr
      rw [htm] at heq
      simp only [Prod.mk.injEq, Option.some.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hasucc : a < succ := (mem_bounds_of_bounded hlr.1 hmemm).1 a rfl
      have hleft : ∀ b, (b ∈ kl ∨ MemChildren b cl) → b < a :=
        fun b hbm => lt_of_memChildren_left kl cl hlen lo hi a kr (c :: r :: rest) b hb' hbm
      have hright : ∀ b, (b ∈ kr ∨ MemChildren b (r :: rest)) → a < b :=
        fun b hbm => gt_of_memChildren_right kl cl hlen lo hi a kr c (r :: rest) b hb' hbm
      have hinc : ∀ b, Mem b c → b < a := fun b hbm => (mem_bounds_of_bounded hlc.1 hbm).2 a rfl
      rw [hdel, htk, htc]
      refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
      · rw [hks, hcs]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append, List.mem_cons]
        constructor
        · rintro ((hbm | rfl | hbm) | (hbm | hbm | hbm | hbm))
          · exact ⟨ne_of_lt (hleft b (Or.inl hbm)), Or.inl (Or.inl hbm)⟩
          · exact ⟨(ne_of_lt hasucc).symm, Or.inr (Or.inr (Or.inr (Or.inl hmemm)))⟩
          · exact ⟨(ne_of_lt (hright b (Or.inl hbm))).symm, Or.inl (Or.inr (Or.inr hbm))⟩
          · exact ⟨ne_of_lt (hleft b (Or.inr hbm)), Or.inr (Or.inl hbm)⟩
          · exact ⟨ne_of_lt (hinc b hbm), Or.inr (Or.inr (Or.inl hbm))⟩
          · refine ⟨(ne_of_lt (hright b (Or.inr (Or.inl ((hiffm b).mp hbm).1)))).symm, ?_⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl ((hiffm b).mp hbm).1)))
          · exact ⟨(ne_of_lt (hright b (Or.inr (Or.inr hbm)))).symm,
                   Or.inr (Or.inr (Or.inr (Or.inr hbm)))⟩
        · rintro ⟨hne, (hbm | rfl | hbm) | (hbm | hbm | hbm | hbm)⟩
          · exact Or.inl (Or.inl hbm)
          · exact absurd rfl hne
          · exact Or.inl (Or.inr (Or.inr hbm))
          · exact Or.inr (Or.inl hbm)
          · exact Or.inr (Or.inr (Or.inl hbm))
          · by_cases hbs : b = succ
            · exact Or.inl (Or.inr (Or.inl hbs))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ((hiffm b).mpr ⟨hbm, hbs⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr hbm)))
      · simp only [true_iff]
        rw [hks]
        exact Or.inl (by simp)
      · refine hput c succ r' ?_ ?_ ?_ ?_
        · exact bounded_narrow_hi hlc.1 (fun b hbm => lt_trans (hinc b hbm) hasucc)
        · exact bounded_widen_lo hlegm.1 hgtm
        · exact fun x hx => lt_trans (hlok x hx) hasucc
        · exact fun y hy => (mem_bounds_of_bounded hlr.1 hmemm).2 y hy
      · simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        have hall : ∀ y ∈ cs, depth? y = some e :=
          (childrenDepth?_iff (by rw [hcs]; simp)).mp he
        rcases List.mem_append.mp hx with hx | hx
        · exact hall x (by rw [hcs]; simp [hx])
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hall x (by rw [hcs]; simp)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hlegm.2.1
            · exact hall x (by rw [hcs]; simp [hx])
      · have hkall : ∀ x ∈ cs, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk.2.2
        have hlenk : (kl ++ succ :: kr).length = ks.length := by rw [hks]; simp
        refine ⟨?_, ?_, ?_⟩
        · cases isRoot with
          | true => exact Or.inl rfl
          | false => exact Or.inr (by rw [hlenk]; exact hk.1)
        · rw [hlenk]; exact hk.2.1
        · refine (childrenKeyCountOk_iff _).mpr ?_
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hkall x (by rw [hcs]; simp [hx])
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hkall x (by rw [hcs]; simp)
            · rcases List.mem_cons.mp hx with rfl | hx
              · exact hlegm.2.2
              · exact hkall x (by rw [hcs]; simp [hx])
  | case6 ks cs k kr c r rest hkr hcr hnlt hnsc hsr r' htm =>
      -- Unreachable for the same reason, on the right sibling.
      intro d lo hi isRoot hb hd hk hspare
      exfalso
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      obtain ⟨kl, cl, htk, htc, hks, hcs, hlen, hlc, hlr, hlok, hkhi, hput, hmerge⟩ :=
        slot_pair (a := a) hb he hk hkr hcr
      obtain ⟨t', m, heq, -, -, -, -, -⟩ :=
        takeMin_spec hdeg r e (some k) (hiAt hi kr) hlr hsr
      rw [htm] at heq
      simp at heq
  | case7 ks cs k kr c r rest hkr hcr hnlt hnsc hnsr ih =>
      intro d lo hi isRoot hb hd hk hspare
      have hdel : delRec deg a (node ks cs)
          = (node (ks.take (slot a ks) ++ kr)
                  (cs.take (slot a ks) ++ (delRec deg a (mergeNodes c k r)).1 :: rest),
             (delRec deg a (mergeNodes c k r)).2) := by
        rw [delRec]
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
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      obtain ⟨kl, cl, htk, htc, hks, hcs, hlen, hlc, hlr, hlok, hkhi, hput, hmergeput⟩ :=
        slot_pair (a := a) hb he hk hkr hcr
      have hnkl : ¬ (k < a) :=
        not_lt_head_dropWhile (by rw [← (take_drop_slot a ks).2]; exact hkr)
      have hak : a = k := le_antisymm (not_lt.mp hnkl) (not_lt.mp hnlt)
      subst hak
      have hb' : Bounded lo hi (node (kl ++ a :: kr) (cl ++ c :: r :: rest)) := by
        rw [← hks, ← hcs]; exact hb
      have hnsc' : hasSpare deg c = false := by simpa using hnsc
      have hnsr' : hasSpare deg r = false := by simpa using hnsr
      have hbm : Bounded (loAt lo kl) (hiAt hi kr) (mergeNodes c a r) :=
        bounded_mergeNodes hlc.2.1 hlr.2.1 hlc.1 hlr.1 hlok hkhi
      have hdm : depth? (mergeNodes c a r) = some e := depth_mergeNodes hlc.2.1 hlr.2.1
      have hkm : KeyCountOk deg false (mergeNodes c a r) :=
        keyCount_mergeNodes hdeg hlc.2.1 hlr.2.1 hlc.2.2 hlr.2.2 hnsc' hnsr'
      have hspm : hasSpare deg (mergeNodes c a r) = true :=
        hasSpare_mergeNodes hdeg hlc.2.1 hlr.2.1 hlc.2.2 hlr.2.2
      obtain ⟨ihmem, ihfound, ihb, ihdep, ihk⟩ :=
        ih e (loAt lo kl) (hiAt hi kr) false hbm hdm hkm (Or.inr hspm)
      have ihk' : KeyCountOk deg false (delRec deg a (mergeNodes c a r)).1 :=
        keyCountOkAfter_false.mp ihk
      have hmm : ∀ b, Mem b (mergeNodes c a r) ↔ (Mem b c ∨ b = a ∨ Mem b r) :=
        fun b => mem_mergeNodes hlc.2.1 hlr.2.1
      have hleft : ∀ b, (b ∈ kl ∨ MemChildren b cl) → b < a :=
        fun b hbm2 => lt_of_memChildren_left kl cl hlen lo hi a kr (c :: r :: rest) b hb' hbm2
      have hright : ∀ b, (b ∈ kr ∨ MemChildren b (r :: rest)) → a < b :=
        fun b hbm2 => gt_of_memChildren_right kl cl hlen lo hi a kr c (r :: rest) b hb' hbm2
      have hinc : ∀ b, Mem b c → b < a := fun b hbm2 => (mem_bounds_of_bounded hlc.1 hbm2).2 a rfl
      rw [hdel, htk, htc]
      refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
      · rw [hks, hcs]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append, List.mem_cons]
        constructor
        · rintro ((hbm2 | hbm2) | (hbm2 | hbm2 | hbm2))
          · exact ⟨ne_of_lt (hleft b (Or.inl hbm2)), Or.inl (Or.inl hbm2)⟩
          · exact ⟨(ne_of_lt (hright b (Or.inl hbm2))).symm, Or.inl (Or.inr (Or.inr hbm2))⟩
          · exact ⟨ne_of_lt (hleft b (Or.inr hbm2)), Or.inr (Or.inl hbm2)⟩
          · obtain ⟨hne, hmem⟩ := (ihmem b).mp hbm2
            rcases (hmm b).mp hmem with h | h | h
            · exact ⟨hne, Or.inr (Or.inr (Or.inl h))⟩
            · exact absurd h hne
            · exact ⟨hne, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
          · exact ⟨(ne_of_lt (hright b (Or.inr (Or.inr hbm2)))).symm,
                   Or.inr (Or.inr (Or.inr (Or.inr hbm2)))⟩
        · rintro ⟨hne, (hbm2 | rfl | hbm2) | (hbm2 | hbm2 | hbm2 | hbm2)⟩
          · exact Or.inl (Or.inl hbm2)
          · exact absurd rfl hne
          · exact Or.inl (Or.inr hbm2)
          · exact Or.inr (Or.inl hbm2)
          · exact Or.inr (Or.inr (Or.inl ((ihmem b).mpr ⟨hne, (hmm b).mpr (Or.inl hbm2)⟩)))
          · exact Or.inr (Or.inr (Or.inl
              ((ihmem b).mpr ⟨hne, (hmm b).mpr (Or.inr (Or.inr hbm2))⟩)))
          · exact Or.inr (Or.inr (Or.inr hbm2))
      · rw [ihfound]
        constructor
        · intro _
          rw [hks]
          exact Or.inl (by simp)
        · intro _
          exact (hmm a).mpr (Or.inr (Or.inl rfl))
      · exact hmergeput _ ihb
      · simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        have hall : ∀ y ∈ cs, depth? y = some e :=
          (childrenDepth?_iff (by rw [hcs]; simp)).mp he
        rcases List.mem_append.mp hx with hx | hx
        · exact hall x (by rw [hcs]; simp [hx])
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ihdep
          · exact hall x (by rw [hcs]; simp [hx])
      · have hkall : ∀ x ∈ cs, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk.2.2
        have hlenk : (kl ++ kr).length + 1 = ks.length := by
          rw [hks]; simp; omega
        refine ⟨?_, ?_, ?_⟩
        · cases isRoot with
          | true => exact Or.inl rfl
          | false =>
              refine Or.inr ?_
              have hs : deg ≤ ks.length := by
                have h0 := hspare.resolve_left (by simp)
                simp only [hasSpare, nodeKeys_node] at h0
                exact of_decide_eq_true h0
              omega
        · have := hk.2.1
          omega
        · refine (childrenKeyCountOk_iff _).mpr ?_
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hkall x (by rw [hcs]; simp [hx])
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ihk'
            · exact hkall x (by rw [hcs]; simp [hx])
  | case8 ks cs c hkr hcr sp ih =>
      -- Every key is below `a`, so the last child is where `a` would be.
      intro d lo hi isRoot hb hd hk hspare
      obtain ⟨e, he, rfl⟩ : ∃ e, childrenDepth? cs = some e ∧ d = e + 1 := by
        simp only [depth?, Option.map_eq_some_iff] at hd
        obtain ⟨e, h₁, h₂⟩ := hd
        exact ⟨e, h₁, h₂.symm⟩
      have harity : cs.length = ks.length + 1 := hb.2.1
      have hks : ks.take (slot a ks) = ks := by
        conv_rhs => rw [← List.take_append_drop (slot a ks) ks]
        rw [hkr, List.append_nil]
      have hcs : cs = cs.take (slot a ks) ++ [c] := by
        conv_lhs => rw [← List.take_append_drop (slot a ks) cs]
        rw [hcr]
      have hslot : slot a ks = ks.length := by
        have h1 := congrArg List.length hks
        have h2 := slot_le a ks
        rw [List.length_take] at h1
        omega
      have hlen : (cs.take (slot a ks)).length = (ks.take (slot a ks)).length := by
        rw [List.length_take, List.length_take]
        omega
      set sp0 : Spot α := ⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ with hsp0
      have hsp0n : sp0.node = node ks cs := by
        simp only [hsp0, Spot.node, List.append_nil]
        rw [hks, ← hcs]
      have hsp0c : sp0.children = cs := by
        simp only [hsp0, Spot.children]
        rw [← hcs]
      have hleg0 : SpotLegal deg lo hi e sp0 :=
        ⟨by rw [hsp0n]; exact hb, by rw [hsp0c]; exact he, by rw [hsp0c]; exact hk.2.2, hlen⟩
      have hkspos : 1 ≤ ks.length := by
        cases isRoot with
        | true => exact hk.1
        | false =>
            have h1 : deg - 1 ≤ ks.length := hk.1
            omega
      have hsib : sp0.childrenL ≠ [] ∨ sp0.childrenR ≠ [] :=
        Spot.sibling_of_keys hleg0.1 (by rw [hsp0n]; simp only [nodeKeys_node]; omega)
      obtain ⟨hleg', hmemiff, hmono, hspare', hcnt1, hcnt2⟩ := ensureSpare_spec hdeg hleg0 hsib
      have hspdef : ensureSpare deg sp0 = sp := rfl
      rw [hspdef] at hleg' hmemiff hmono hspare' hcnt1 hcnt2
      obtain ⟨hb', hd', hk', hlen'⟩ := hleg'
      have hb0' : Bounded lo hi
          (node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR)) := hb'
      obtain ⟨hbt, hputh⟩ :=
        bounded_hole sp.keysL sp.childrenL hlen' lo hi sp.keysR sp.childrenR sp.target hb0'
      have hcne : sp.children ≠ [] := by simp [Spot.children]
      have hdall : ∀ x ∈ sp.children, depth? x = some e := (childrenDepth?_iff hcne).mp hd'
      have hkall : ∀ x ∈ sp.children, KeyCountOk deg false x := (childrenKeyCountOk_iff _).mp hk'
      have hmt : sp.target ∈ sp.children := by simp [Spot.children]
      obtain ⟨ihmem, ihfound, ihb, ihdep, ihk⟩ :=
        ih e (loAt lo sp.keysL) (hiAt hi sp.keysR) false hbt (hdall sp.target hmt)
          (hkall sp.target hmt) (Or.inr hspare')
      have ihk' : KeyCountOk deg false (delRec deg a sp.target).1 := keyCountOkAfter_false.mp ihk
      have hklt : ∀ x ∈ ks, x < a := by
        intro x hx
        exact mem_takeWhile_lt (by rw [← (take_drop_slot a ks).1, hks]; exact hx)
      have hbl : Bounded lo hi (node (ks.take (slot a ks)) (cs.take (slot a ks) ++ [c])) := by
        rw [hks, ← hcs]; exact hb
      have hainc : Mem a (node ks cs) → Mem a c := by
        intro hmn
        rw [hcs] at hmn
        simp only [mem_node, memChildren_append, memChildren_cons, memChildren_nil,
          or_false] at hmn
        rcases hmn with hx | hx | hx
        · exact absurd (hklt a hx) (lt_irrefl a)
        · obtain ⟨x, hxm, hax⟩ := lt_key_of_memChildren_left (ks.take (slot a ks))
            (cs.take (slot a ks)) hlen lo hi [] [c] a (by simpa using hbl) hx
          rw [hks] at hxm
          exact absurd (lt_trans hax (hklt x hxm)) (lt_irrefl a)
        · exact hx
      have hat : Mem a (node ks cs) ↔ Mem a sp.target := by
        constructor
        · intro hmn
          exact hmono a (by rw [hsp0]; exact hainc hmn)
        · intro hmt2
          rw [← hsp0n, ← hmemiff a]
          exact Or.inr ((memChildren_iff a _).mpr ⟨sp.target, by simp, hmt2⟩)
      have houts : ∀ b, (b ∈ sp.keysL ∨ MemChildren b sp.childrenL ∨
          b ∈ sp.keysR ∨ MemChildren b sp.childrenR) → b ≠ a := by
        intro b hbm hba
        have hmn : Mem a sp.node := by
          have hopen : Mem a (node (sp.keysL ++ sp.keysR)
              (sp.childrenL ++ sp.target :: sp.childrenR)) := by
            simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append]
            rcases hbm with hx | hx | hx | hx
            · exact Or.inl (Or.inl (hba ▸ hx))
            · exact Or.inr (Or.inl (hba ▸ hx))
            · exact Or.inl (Or.inr (hba ▸ hx))
            · exact Or.inr (Or.inr (Or.inr (hba ▸ hx)))
          exact hopen
        have hta : Mem a sp.target := hat.mp (by rw [← hsp0n, ← hmemiff a]; exact hmn)
        exact spot_outside_ne ⟨hb', hd', hk', hlen'⟩ hta b hbm hba
      have hdel : delRec deg a (node ks cs)
          = (({ ensureSpare deg sp0 with
                  target := (delRec deg a (ensureSpare deg sp0).target).1 } : Spot α).node,
             (delRec deg a (ensureSpare deg sp0).target).2) := by
        rw [delRec]
        split
        · rename_i k1 kr1 c1 r1 rest1 h1 h2
          rw [hkr] at h1
          simp at h1
        · rename_i c1 h1 h2
          rw [hcr] at h2
          simp only [List.cons.injEq, and_true] at h2
          obtain rfl := h2
          simp [hsp0]
        · rename_i h1 h2
          exact (h2 c hkr hcr).elim
      rw [hdel, hspdef]
      have hresn : ({ sp with target := (delRec deg a sp.target).1 } : Spot α).node
          = node (sp.keysL ++ sp.keysR)
                 (sp.childrenL ++ (delRec deg a sp.target).1 :: sp.childrenR) := rfl
      have hspn : sp.node
          = node (sp.keysL ++ sp.keysR) (sp.childrenL ++ sp.target :: sp.childrenR) := rfl
      have hmemL : ∀ x ∈ sp.childrenL, x ∈ sp.children := by
        intro x hx; simp [Spot.children, hx]
      have hmemR : ∀ x ∈ sp.childrenR, x ∈ sp.children := by
        intro x hx; simp [Spot.children, hx]
      refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
      · rw [hresn, ← hsp0n, ← hmemiff b, hspn]
        simp only [mem_node, memChildren_append, memChildren_cons, List.mem_append]
        constructor
        · rintro ((hx | hx) | (hx | hx | hx))
          · exact ⟨houts b (Or.inl hx), Or.inl (Or.inl hx)⟩
          · exact ⟨houts b (Or.inr (Or.inr (Or.inl hx))), Or.inl (Or.inr hx)⟩
          · exact ⟨houts b (Or.inr (Or.inl hx)), Or.inr (Or.inl hx)⟩
          · exact ⟨((ihmem b).mp hx).1, Or.inr (Or.inr (Or.inl ((ihmem b).mp hx).2))⟩
          · exact ⟨houts b (Or.inr (Or.inr (Or.inr hx))), Or.inr (Or.inr (Or.inr hx))⟩
        · rintro ⟨hne, (hx | hx) | (hx | hx | hx)⟩
          · exact Or.inl (Or.inl hx)
          · exact Or.inl (Or.inr hx)
          · exact Or.inr (Or.inl hx)
          · exact Or.inr (Or.inr (Or.inl ((ihmem b).mpr ⟨hne, hx⟩)))
          · exact Or.inr (Or.inr (Or.inr hx))
      · rw [ihfound]
        exact hat.symm
      · rw [hresn]
        exact hputh _ ihb
      · rw [hresn]
        simp only [depth?, Option.map_eq_some_iff]
        refine ⟨e, ?_, rfl⟩
        refine (childrenDepth?_iff (by simp)).mpr ?_
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hdall x (hmemL x hx)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact ihdep
          · exact hdall x (hmemR x hx)
      · rw [hresn]
        have hk0 : (nodeKeys sp0.node).length = ks.length := by rw [hsp0n]; simp
        have hkl : (nodeKeys sp.node).length = (sp.keysL ++ sp.keysR).length := by rw [hspn]; simp
        rw [hkl, hk0] at hcnt1 hcnt2
        have hub : ks.length ≤ 2 * deg - 1 := hk.2.1
        refine ⟨?_, by omega, ?_⟩
        · cases isRoot with
          | true => exact Or.inl rfl
          | false =>
              refine Or.inr ?_
              have hs : deg ≤ ks.length := by
                have h0 := hspare.resolve_left (by simp)
                simp only [hasSpare, nodeKeys_node] at h0
                exact of_decide_eq_true h0
              omega
        · refine (childrenKeyCountOk_iff _).mpr ?_
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hkall x (hmemL x hx)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ihk'
            · exact hkall x (hmemR x hx)
  | case9 ks cs h1 h2 =>
      -- Both patterns fail only if the node has fewer children than keys, which `Bounded` forbids.
      intro d lo hi isRoot hb hd hk hspare
      exfalso
      have harity : cs.length = ks.length + 1 := hb.2.1
      have hsl : slot a ks ≤ ks.length := slot_le a ks
      have hdk : (ks.drop (slot a ks)).length = ks.length - slot a ks := by simp
      have hdc : (cs.drop (slot a ks)).length = cs.length - slot a ks := by simp
      rcases Nat.lt_or_ge (slot a ks) ks.length with hlt | hgeq
      · obtain ⟨k, kr, hk1⟩ : ∃ k kr, ks.drop (slot a ks) = k :: kr := by
          cases hx : ks.drop (slot a ks) with
          | nil => rw [hx] at hdk; simp at hdk; omega
          | cons k kr => exact ⟨k, kr, rfl⟩
        obtain ⟨c, r, rest, hc1⟩ : ∃ c r rest, cs.drop (slot a ks) = c :: r :: rest := by
          cases hx : cs.drop (slot a ks) with
          | nil => rw [hx] at hdc; simp at hdc; omega
          | cons c cs2 =>
              cases cs2 with
              | nil => rw [hx] at hdc; simp at hdc; omega
              | cons r rest => exact ⟨c, r, rest, rfl⟩
        exact h1 k kr c r rest hk1 hc1
      · have hsl2 : slot a ks = ks.length := le_antisymm hsl hgeq
        have hk1 : ks.drop (slot a ks) = [] := by rw [hsl2]; simp
        obtain ⟨c, hc1⟩ : ∃ c, cs.drop (slot a ks) = [c] := by
          cases hx : cs.drop (slot a ks) with
          | nil => rw [hx] at hdc; simp at hdc; omega
          | cons c cs2 =>
              cases cs2 with
              | nil => exact ⟨c, rfl⟩
              | cons _ _ => rw [hx] at hdc; simp at hdc; omega
        exact h2 c hk1 hc1

/-- `delete` discharges `DeleteSpec`. -/
theorem deleteSpec {deg : ℕ} {bt : BTree α} (h : Valid deg bt) (a : α) :
    DeleteSpec deg a bt (delete deg a bt).1 := by
  obtain ⟨hb, hs, hk, hdeg⟩ := valid_iff_legal.1 h
  obtain ⟨d, hd⟩ : ∃ d, depth? bt = some d := Option.ne_none_iff_exists'.mp hs
  obtain ⟨hmem, -, hb', hd', hk'⟩ :=
    delRec_spec hdeg a bt d none none true hb hd hk (Or.inl rfl)
  obtain ⟨hcb, hcs, hck, hcm⟩ :=
    collapseRoot_spec hdeg hb' (by simp only [SameDepth, hd']; simp) hk'
  refine ⟨fun b => ?_, fun _ => valid_iff_legal.2 ⟨hcb, hcs, hck, hdeg⟩⟩
  simp only [delete]
  rw [hcm b]
  exact hmem b

/-- `delete` reports whether the key was there: the flag is `true` exactly when `a` was a member. -/
theorem delete_found {deg : ℕ} {bt : BTree α} (h : Valid deg bt) (a : α) :
    (delete deg a bt).2 = true ↔ Mem a bt := by
  obtain ⟨hb, hs, hk, hdeg⟩ := valid_iff_legal.1 h
  obtain ⟨d, hd⟩ : ∃ d, depth? bt = some d := Option.ne_none_iff_exists'.mp hs
  obtain ⟨-, hfound, -, -, -⟩ :=
    delRec_spec hdeg a bt d none none true hb hd hk (Or.inl rfl)
  simpa only [delete] using hfound

end BTree

end AlgoDesign.Searching
