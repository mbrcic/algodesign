/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BST.Basic

/-!
# Binary search tree: search and order queries

`search` (`search_correct`), `min?`/`max?`, `floor?`/`ceiling?`, the range query `range`
(`mem_range`, and `floor?`/`ceiling?` as its last and first keys), and `rank`/`select?`, inverse to
each other (`rank_select?`, `select?_rank`).
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BST

variable {α : Type}
variable [LinearOrder α]

/-- Does `a` occur in the tree? Follows the ordering the same way `insert` does. -/
def search (a : α) : BST α → Bool
  | leaf => false
  | node l k r =>
      if a < k then search a l
      else if k < a then search a r
      else true

/-- Search is correct on any `Sorted` tree: it finds exactly the keys that are there. Without
`Sorted`, only the easy direction (`search` returning `true` implies the key is present) would
hold — a search on an *unsorted* tree could easily miss a key that's present somewhere off the
path it follows. -/
theorem search_correct {t : BST α} (ht : Sorted t) (a : α) : search a t = true ↔ Mem a t := by
  induction t with
  | leaf => simp [search]
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold search
    split
    · rename_i h
      rw [ihl hsl]
      simp only [mem_node]
      constructor
      · tauto
      · rintro (hml | rfl | hmr)
        · exact hml
        · exact absurd h (lt_irrefl _)
        · exact absurd (hr.of_mem hmr) (by rw [not_lt]; exact le_of_lt h)
    · split
      · rename_i h h'
        rw [ihr hsr]
        simp only [mem_node]
        constructor
        · tauto
        · rintro (hml | rfl | hmr)
          · exact absurd (hl.of_mem hml) (not_lt.mpr (le_of_lt h'))
          · exact absurd h' (lt_irrefl _)
          · exact hmr
      · rename_i h h'
        have : a = k := le_antisymm (not_lt.mp h') (not_lt.mp h)
        simp [this]

/-- The smallest key, if any — always the leftmost node, ignoring the right subtree entirely
(that's the whole point of the BST ordering: everything in the right subtree is bigger than the
node's own key, which already beats anything the left subtree could offer). -/
def min? : BST α → Option α
  | leaf => none
  | node l k _ => some ((min? l).getD k)

omit [LinearOrder α] in
@[simp] theorem min?_leaf : min? (leaf : BST α) = none := rfl

/-- **`min?` is correct**: on a `Sorted` tree, if it returns `some m`, `m` is present and is a
lower bound for the whole tree. -/
theorem min?_correct {t : BST α} (ht : Sorted t) {m : α} (hm : min? t = some m) :
    Mem m t ∧ All (m ≤ ·) t := by
  induction t with
  | leaf => simp at hm
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    have heq : (min? l).getD k = m := by unfold min? at hm; exact Option.some.inj hm
    cases hl' : min? l with
    | none =>
      rw [hl', Option.getD_none] at heq
      subst heq
      have hlleaf : l = leaf := by
        cases l with
        | leaf => rfl
        | node _ _ _ => simp [min?] at hl'
      subst hlleaf
      exact ⟨Or.inr (Or.inl rfl), trivial, le_refl _, hr.imp (fun _ h => le_of_lt h)⟩
    | some m' =>
      rw [hl', Option.getD_some] at heq
      subst heq
      obtain ⟨hmem, hle⟩ := ihl hsl hl'
      have hmk : m' < k := hl.of_mem hmem
      exact ⟨Or.inl hmem, hle, le_of_lt hmk, hr.imp (fun x hx => le_of_lt (lt_trans hmk hx))⟩

/-- The largest key, symmetric to `min?`. -/
def max? : BST α → Option α
  | leaf => none
  | node _ k r => some ((max? r).getD k)

omit [LinearOrder α] in
@[simp] theorem max?_leaf : max? (leaf : BST α) = none := rfl

/-- **`max?` is correct**, symmetric to `min?_correct`. -/
theorem max?_correct {t : BST α} (ht : Sorted t) {m : α} (hm : max? t = some m) :
    Mem m t ∧ All (· ≤ m) t := by
  induction t with
  | leaf => simp at hm
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    have heq : (max? r).getD k = m := by unfold max? at hm; exact Option.some.inj hm
    cases hr' : max? r with
    | none =>
      rw [hr', Option.getD_none] at heq
      subst heq
      have hrleaf : r = leaf := by
        cases r with
        | leaf => rfl
        | node _ _ _ => simp [max?] at hr'
      subst hrleaf
      exact ⟨Or.inr (Or.inl rfl), hl.imp (fun _ h => le_of_lt h), le_refl _, trivial⟩
    | some m' =>
      rw [hr', Option.getD_some] at heq
      subst heq
      obtain ⟨hmem, hle⟩ := ihr hsr hr'
      have hkm : k < m' := hr.of_mem hmem
      exact ⟨Or.inr (Or.inr hmem), hl.imp (fun x hx => le_of_lt (lt_trans hx hkm)), le_of_lt hkm,
        hle⟩

/-- The largest key `≤ a`, if any. If `a` itself is a key, that's the answer; if `a < k`, the
answer (if any) is in the left subtree only; if `a > k`, the right subtree might have something
closer to `a` — but if not, `k` itself is still `≤ a` and beats nothing being found at all. -/
def floor? (a : α) : BST α → Option α
  | leaf => none
  | node l k r =>
      if a < k then floor? a l
      else if k < a then some ((floor? a r).getD k)
      else some k

/-- If `floor?` finds nothing, nothing present is `≤ a` — every key in the tree is bigger. Needed
to handle `floor?_correct`'s "right subtree came up empty, fall back to `k`" case: that fallback
is only correct because nothing in `r` could have beaten `k` anyway. -/
theorem floor?_eq_none {t : BST α} (ht : Sorted t) {a : α} (h : floor? a t = none) :
    ∀ x, Mem x t → a < x := by
  induction t with
  | leaf => intro x hx; cases hx
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold floor? at h
    split_ifs at h with hak hka
    · -- hak : a < k, h : floor? a l = none
      intro x hx
      rcases hx with hx | rfl | hx
      · exact ihl hsl h x hx
      · exact hak
      · exact lt_trans hak (hr.of_mem hx)

    -- `split_ifs` already discharges the remaining cases (`k < a` / `a = k`): both give
    -- `h : some _ = none`, an immediate contradiction it resolves on its own.

/-- **`floor?` is correct**: on a `Sorted` tree, a `some f` result is a key that's `≤ a`, and no
key present is both `≤ a` and bigger than `f` — `f` is the *greatest* lower-or-equal key. -/
theorem floor?_correct {t : BST α} (ht : Sorted t) {a f : α} (hf : floor? a t = some f) :
    Mem f t ∧ f ≤ a ∧ ∀ x, Mem x t → x ≤ a → x ≤ f := by
  induction t with
  | leaf => simp [floor?] at hf
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold floor? at hf
    split_ifs at hf with hak hka
    · obtain ⟨hmem, hfa, hbest⟩ := ihl hsl hf
      refine ⟨Or.inl hmem, hfa, fun x hx hxa => ?_⟩
      rcases hx with hx | rfl | hx
      · exact hbest x hx hxa
      · exact absurd hxa (not_le.mpr hak)
      · exact absurd hxa (not_le.mpr (lt_trans hak (hr.of_mem hx)))
    · rcases hr' : floor? a r with _ | fr
      · rw [hr', Option.getD_none] at hf
        obtain rfl := Option.some.inj hf
        refine ⟨Or.inr (Or.inl rfl), le_of_lt hka, fun x hx hxa => ?_⟩
        rcases hx with hx | rfl | hx
        · exact le_of_lt (hl.of_mem hx)
        · exact le_refl _
        · exact absurd (floor?_eq_none hsr hr' x hx) (not_lt.mpr hxa)
      · rw [hr', Option.getD_some] at hf
        obtain rfl := Option.some.inj hf
        obtain ⟨hmem, hfa, hbest⟩ := ihr hsr hr'
        refine ⟨Or.inr (Or.inr hmem), hfa, fun x hx hxa => ?_⟩
        rcases hx with hx | rfl | hx
        · exact le_of_lt (lt_trans (hl.of_mem hx) (hr.of_mem hmem))
        · exact le_of_lt (hr.of_mem hmem)
        · exact hbest x hx hxa
    · obtain rfl := Option.some.inj hf
      have hkey : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
      refine ⟨Or.inr (Or.inl rfl), le_of_eq hkey, fun x hx hxa => ?_⟩
      rcases hx with hx | rfl | hx
      · exact le_of_lt (hl.of_mem hx)
      · exact le_refl _
      · exact absurd hxa (not_le.mpr (hkey ▸ hr.of_mem hx))

/-- The smallest key `≥ a`, symmetric to `floor?`. -/
def ceiling? (a : α) : BST α → Option α
  | leaf => none
  | node l k r =>
      if k < a then ceiling? a r
      else if a < k then some ((ceiling? a l).getD k)
      else some k

/-- If `ceiling?` finds nothing, nothing present is `≥ a`, symmetric to `floor?_eq_none`. -/
theorem ceiling?_eq_none {t : BST α} (ht : Sorted t) {a : α} (h : ceiling? a t = none) :
    ∀ x, Mem x t → x < a := by
  induction t with
  | leaf => intro x hx; cases hx
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold ceiling? at h
    split_ifs at h with hka hak
    · -- hka : k < a, h : ceiling? a r = none
      intro x hx
      rcases hx with hx | rfl | hx
      · exact lt_trans (hl.of_mem hx) hka
      · exact hka
      · exact ihr hsr h x hx

    -- `split_ifs` already discharges the remaining cases (`a < k` / `a = k`): both give
    -- `h : some _ = none`, an immediate contradiction it resolves on its own.

/-- **`ceiling?` is correct**, symmetric to `floor?_correct`. -/
theorem ceiling?_correct {t : BST α} (ht : Sorted t) {a c : α} (hc : ceiling? a t = some c) :
    Mem c t ∧ a ≤ c ∧ ∀ x, Mem x t → a ≤ x → c ≤ x := by
  induction t with
  | leaf => simp [ceiling?] at hc
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold ceiling? at hc
    split_ifs at hc with hka hak
    · obtain ⟨hmem, hac, hbest⟩ := ihr hsr hc
      refine ⟨Or.inr (Or.inr hmem), hac, fun x hx hxa => ?_⟩
      rcases hx with hx | rfl | hx
      · exact absurd hxa (not_le.mpr (lt_trans (hl.of_mem hx) hka))
      · exact absurd hxa (not_le.mpr hka)
      · exact hbest x hx hxa
    · rcases hl' : ceiling? a l with _ | cl
      · rw [hl', Option.getD_none] at hc
        obtain rfl := Option.some.inj hc
        refine ⟨Or.inr (Or.inl rfl), le_of_lt hak, fun x hx hxa => ?_⟩
        rcases hx with hx | rfl | hx
        · exact absurd (ceiling?_eq_none hsl hl' x hx) (not_lt.mpr hxa)
        · exact le_refl _
        · exact le_of_lt (hr.of_mem hx)
      · rw [hl', Option.getD_some] at hc
        obtain rfl := Option.some.inj hc
        obtain ⟨hmem, hac, hbest⟩ := ihl hsl hl'
        refine ⟨Or.inl hmem, hac, fun x hx hxa => ?_⟩
        rcases hx with hx | rfl | hx
        · exact hbest x hx hxa
        · exact le_of_lt (hl.of_mem hmem)
        · exact le_of_lt (lt_trans (hl.of_mem hmem) (hr.of_mem hx))
    · obtain rfl := Option.some.inj hc
      have hkey : k = a := le_antisymm (not_lt.mp hak) (not_lt.mp hka)
      refine ⟨Or.inr (Or.inl rfl), le_of_eq hkey.symm, fun x hx hxa => ?_⟩
      rcases hx with hx | rfl | hx
      · exact absurd hxa (not_le.mpr (hkey ▸ hl.of_mem hx))
      · exact le_refl _
      · exact le_of_lt (hr.of_mem hx)

/-! ### The keys as a list, and range queries

`range` is a specification: the keys the bounds admit, in order. -/

/-- **Range query**: the keys between two bounds, in order. -/
def range (lo hi : RangeBound α) (t : BST α) : List α :=
  keysInRange lo hi (toList t)

/-- **`range` holds exactly the keys of the tree that the bounds admit.** -/
theorem mem_range {lo hi : RangeBound α} {t : BST α} {a : α} :
    a ∈ range lo hi t ↔ Mem a t ∧ InRange lo hi a := by
  simp [range, keysInRange, List.mem_filter, mem_toList]

/-- **The keys come out in increasing order**, the box's promise: a sorted tree's `toList` is
strictly increasing, so the next larger key and every key in a range are read off it. -/
theorem sorted_toList {t : BST α} (ht : Sorted t) : (toList t).Pairwise (· < ·) := by
  induction t with
  | leaf => simp
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, sl, sr⟩ := ht
    simp only [toList_node]
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨ihl sl, ⟨fun b hb => hr.of_mem ((mem_toList r).1 hb), ihr sr⟩, ?_⟩
    intro a ha b hb
    have hak : a < k := hl.of_mem ((mem_toList l).1 ha)
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hak
    · exact lt_trans hak (hr.of_mem ((mem_toList r).1 hb))

/-- Bounding neither end asks for the whole tree. -/
@[simp] theorem range_unbounded (t : BST α) :
    range .unbounded .unbounded t = toList t := by
  simp [range, keysInRange, inRange, InRange, RangeBound.Lower, RangeBound.Upper]

/-- **`floor?` is the last key of a range**: the largest key `≤ a` is the last key `range` returns
with no lower bound and `a` included as the upper one. This is the link `RangeQuery.lean`'s header
states between the single-key queries and the range query. -/
theorem floor?_eq_getLast?_range {t : BST α} (ht : Sorted t) (a : α) :
    floor? a t = (range .unbounded (.included a) t).getLast? := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    have hnil : a < k → (toList r).filter (inRange .unbounded (.included a)) = [] := by
      intro hak
      refine List.filter_eq_nil_iff.mpr (fun x hx => ?_)
      have hkx : k < x := hr.of_mem ((mem_toList r).mp hx)
      simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, not_le.mpr (lt_trans hak hkx)]
    simp only [range, keysInRange] at ihl ihr ⊢
    rw [toList_node, List.filter_append, List.filter_cons]
    by_cases hak : a < k
    · have hka : ¬ k ≤ a := not_le.mpr hak
      have hP : inRange .unbounded (.included a) k = false := by
        simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, hka]
      simp only [floor?, hak, ↓reduceIte, hP, Bool.false_eq_true]
      rw [hnil hak, List.append_nil, ihl hsl]
    · have hka : k ≤ a := not_lt.mp hak
      have hP : inRange .unbounded (.included a) k = true := by
        simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, hka]
      simp only [floor?, hak, ↓reduceIte, hP, List.getLast?_append, List.getLast?_cons]
      by_cases hka' : k < a
      · simp only [hka', ↓reduceIte, ihr hsr, Option.some_or]
      · have heq : k = a := le_antisymm hka (not_lt.mp hka')
        subst heq
        have hnil' : (toList r).filter (inRange .unbounded (.included k)) = [] := by
          refine List.filter_eq_nil_iff.mpr (fun x hx => ?_)
          have hkx : k < x := hr.of_mem ((mem_toList r).mp hx)
          simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, not_le.mpr hkx]
        simp [hnil']

/-- **`ceiling?` is the first key of a range**, the mirror of `floor?_eq_getLast?_range`. -/
theorem ceiling?_eq_head?_range {t : BST α} (ht : Sorted t) (a : α) :
    ceiling? a t = (range (.included a) .unbounded t).head? := by
  induction t with
  | leaf => rfl
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    have hnil : k < a → (toList l).filter (inRange (.included a) .unbounded) = [] := by
      intro hka
      refine List.filter_eq_nil_iff.mpr (fun x hx => ?_)
      have hxk : x < k := hl.of_mem ((mem_toList l).mp hx)
      simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, not_le.mpr (lt_trans hxk hka)]
    simp only [range, keysInRange] at ihl ihr ⊢
    rw [toList_node, List.filter_append, List.filter_cons]
    by_cases hka : k < a
    · have hak : ¬ a ≤ k := not_le.mpr hka
      have hP : inRange (.included a) .unbounded k = false := by
        simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, hak]
      simp only [ceiling?, hka, ↓reduceIte, hP, Bool.false_eq_true]
      rw [hnil hka, List.nil_append, ihr hsr]
    · have hak : a ≤ k := not_lt.mp hka
      have hP : inRange (.included a) .unbounded k = true := by
        simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, hak]
      simp only [ceiling?, hka, ↓reduceIte, hP, List.head?_append, List.head?_cons]
      by_cases hak' : a < k
      · simp only [hak', ↓reduceIte, ihl hsl]
        cases (List.filter (inRange (.included a) .unbounded) (toList l)).head? <;> rfl
      · have heq : a = k := le_antisymm hak (not_lt.mp hak')
        subst heq
        have hnil' : (toList l).filter (inRange (.included a) .unbounded) = [] := by
          refine List.filter_eq_nil_iff.mpr (fun x hx => ?_)
          have hxk : x < a := hl.of_mem ((mem_toList l).mp hx)
          simp [inRange, InRange, RangeBound.Lower, RangeBound.Upper, not_le.mpr hxk]
        simp [hnil']

/-- How many keys are strictly less than `a` — `a`'s position if it were inserted (or, if it's
already present, the position it's actually at). -/
def rank (a : α) : BST α → ℕ
  | leaf => 0
  | node l k r =>
      if a < k then rank a l
      else if k < a then l.size + 1 + rank a r
      else l.size

/-- The key at position `i` (0-indexed, in sorted order), if any. -/
def select? (i : ℕ) : BST α → Option α
  | leaf => none
  | node l k r =>
      if i < l.size then select? i l
      else if i = l.size then some k
      else select? (i - l.size - 1) r

theorem select?_mem {t : BST α} (ht : Sorted t) {i : ℕ} {a : α} (h : select? i t = some a) :
    Mem a t := by
  induction t generalizing i with
  | leaf => simp [select?] at h
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold select? at h
    split_ifs at h with hi1 hi2
    · exact Or.inl (ihl hsl h)
    · exact Or.inr (Or.inl (Option.some.inj h).symm)
    · exact Or.inr (Or.inr (ihr hsr h))

/-- A present key's rank is always a valid index — strictly less than the tree's size. Needed so
`select?_rank`'s recursive call lands in the `i < l.size` (or symmetric) branch of `select?`. -/
theorem rank_lt_size {t : BST α} (ht : Sorted t) {a : α} (ha : Mem a t) : rank a t < t.size := by
  induction t with
  | leaf => cases ha
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    rcases ha with ha | heq | ha
    · have hak : a < k := hl.of_mem ha
      have hlt : rank a l < l.size := ihl hsl ha
      simp only [rank, ite_eq_left hak, size_node]
      omega
    · simp only [rank, heq, ite_eq_right (lt_irrefl k), size_node]
      omega
    · have hka : k < a := hr.of_mem ha
      have hlt : rank a r < r.size := ihr hsr ha
      simp only [rank, ite_eq_right (not_lt.mpr (le_of_lt hka)), ite_eq_left hka, size_node]
      omega

/-- **`rank`/`select?` are inverse operations**, half 1: the key `select?` finds at position `i`
really does have rank `i`. -/
theorem rank_select? {t : BST α} (ht : Sorted t) {i : ℕ} {a : α} (h : select? i t = some a) :
    rank a t = i := by
  induction t generalizing i with
  | leaf => simp [select?] at h
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    unfold select? at h
    split_ifs at h with hi1 hi2
    · have ha : Mem a l := select?_mem hsl h
      have hak : a < k := hl.of_mem ha
      simp only [rank, ite_eq_left hak]
      exact ihl hsl h
    · have hkey : k = a := Option.some.inj h
      simp only [rank, hkey, lt_irrefl, ite_false]
      omega
    · have ha : Mem a r := select?_mem hsr h
      have hka : k < a := hr.of_mem ha
      have := ihr hsr h
      simp only [rank, ite_eq_right (not_lt.mpr (le_of_lt hka)), ite_eq_left hka]
      omega

/-- **`rank`/`select?` are inverse operations**, half 2: the key at its own rank is itself. -/
theorem select?_rank {t : BST α} (ht : Sorted t) {a : α} (ha : Mem a t) :
    select? (rank a t) t = some a := by
  induction t with
  | leaf => cases ha
  | node l k r ihl ihr =>
    obtain ⟨hl, hr, hsl, hsr⟩ := ht
    rcases ha with ha | heq | ha
    · have hak : a < k := hl.of_mem ha
      have hlt : rank a l < l.size := rank_lt_size hsl ha
      simp only [rank, ite_eq_left hak, select?, ite_eq_left hlt]
      exact ihl hsl ha
    · simp [rank, select?, heq]
    · have hka : k < a := hr.of_mem ha
      simp only [rank, ite_eq_right (not_lt.mpr (le_of_lt hka)), ite_eq_left hka]
      have hnlt : ¬ l.size + 1 + rank a r < l.size := by omega
      have hne : l.size + 1 + rank a r ≠ l.size := by omega
      simp only [select?, ite_eq_right hnlt, ite_eq_right hne]
      have heq2 : l.size + 1 + rank a r - l.size - 1 = rank a r := by omega
      rw [heq2]
      exact ihr hsr ha

end BST

end AlgoDesign.Searching
