/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.Treap.Delete

/-!
# Treap: existence and uniqueness

A treap's shape is determined by its data: two valid treaps with the same keys and the same
distinct priorities are equal (`eq_of_valid`, `eq_of_represents`), and `ofList` builds one for
every assignment with distinct keys (`existsUnique_of_nodup`). `eq_of_insertSpec`,
`eq_of_deleteSpec`: so `InsertSpec` and `DeleteSpec` each leave exactly one possible result.
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace Treap

variable {α : Type}
variable [LinearOrder α]

/-- `t` represents exactly the key/priority assignment `ps`: its key set is `ps`'s keys, and every
pair in `ps` is really stored at that priority. -/
def Represents (t : Treap α) (ps : List (α × ℕ)) : Prop :=
  (∀ a, Mem a t ↔ a ∈ ps.map Prod.fst) ∧ ∀ a n, (a, n) ∈ ps → priorityOf a t = some n

/-! ### Uniqueness: a treap's shape is determined by its data

The root must hold the maximum priority, key order then splits the rest, and the argument repeats;
so the same data in any insertion order gives the same tree. It needs `PriorityInjective`: with a
tie, two valid trees can hold the same data. -/

/-- Distinct keys carry distinct priorities. The hypothesis that makes a treap's shape unique:
without it a tie can be broken either way, and two different valid trees hold the same data. -/
def PriorityInjective (t : Treap α) : Prop :=
  ∀ a b, Mem a t → Mem b t → priorityOf a t = priorityOf b t → a = b

theorem eq_of_valid : ∀ (t₁ t₂ : Treap α), Valid t₁ → Valid t₂ →
    (∀ a, Mem a t₁ ↔ Mem a t₂) → (∀ a, priorityOf a t₁ = priorityOf a t₂) →
    PriorityInjective t₁ → t₁ = t₂ := by
  intro t₁
  induction t₁ with
  | leaf =>
    intro t₂ _ _ hkeys _ _
    exact (eq_leaf_of_not_mem (fun a ha => (hkeys a).mpr ha)).symm
  | node l₁ k₁ p₁ r₁ ihl ihr =>
    intro t₂ h₁ h₂ hkeys hprio hinj
    have hk₁ : Mem k₁ (node l₁ k₁ p₁ r₁) := Or.inr (Or.inl rfl)
    have hk₁' : Mem k₁ t₂ := (hkeys k₁).mp hk₁
    rcases t₂ with _ | ⟨l₂, k₂, p₂, r₂⟩
    · exact absurd hk₁' (by simp)
    obtain ⟨hs₁, ho₁⟩ := h₁
    obtain ⟨hs₂, ho₂⟩ := h₂
    have hp₁ : priorityOf k₁ (node l₁ k₁ p₁ r₁) = some p₁ := priorityOf_root _ _ _ _
    have hp₂ : priorityOf k₂ (node l₂ k₂ p₂ r₂) = some p₂ := priorityOf_root _ _ _ _
    -- each root's priority bounds the other's, because each is the maximum of its own tree
    have hle₁ : p₁ ≤ p₂ := priorityOf_le_root ho₂ (by rw [← hprio k₁]; exact hp₁)
    have hle₂ : p₂ ≤ p₁ := priorityOf_le_root ho₁ (by rw [hprio k₂]; exact hp₂)
    have hpp : p₂ = p₁ := le_antisymm hle₂ hle₁
    subst hpp
    -- ... so the two roots carry the same priority, and injectivity forces the same key
    have hk₂' : Mem k₂ (node l₁ k₁ p₂ r₁) := (hkeys k₂).mpr (Or.inr (Or.inl rfl))
    have hkk : k₁ = k₂ := hinj k₁ k₂ hk₁ hk₂' (by rw [hp₁, hprio k₂, hp₂])
    subst hkk
    -- the key sets and priority lookups then split cleanly by the BST ordering
    have hmem_l : ∀ a, Mem a l₁ ↔ Mem a l₂ := by
      intro a
      constructor
      · intro ha
        have hlt : a < k₁ := hs₁.1.of_mem ha
        rcases (hkeys a).mp (Or.inl ha) with h | h | h
        · exact h
        · exact absurd h (ne_of_lt hlt)
        · exact absurd (hs₂.2.1.of_mem h) (not_lt.mpr (le_of_lt hlt))
      · intro ha
        have hlt : a < k₁ := hs₂.1.of_mem ha
        rcases (hkeys a).mpr (Or.inl ha) with h | h | h
        · exact h
        · exact absurd h (ne_of_lt hlt)
        · exact absurd (hs₁.2.1.of_mem h) (not_lt.mpr (le_of_lt hlt))
    have hmem_r : ∀ a, Mem a r₁ ↔ Mem a r₂ := by
      intro a
      constructor
      · intro ha
        have hgt : k₁ < a := hs₁.2.1.of_mem ha
        rcases (hkeys a).mp (Or.inr (Or.inr ha)) with h | h | h
        · exact absurd (hs₂.1.of_mem h) (not_lt.mpr (le_of_lt hgt))
        · exact absurd h.symm (ne_of_lt hgt)
        · exact h
      · intro ha
        have hgt : k₁ < a := hs₂.2.1.of_mem ha
        rcases (hkeys a).mpr (Or.inr (Or.inr ha)) with h | h | h
        · exact absurd (hs₁.1.of_mem h) (not_lt.mpr (le_of_lt hgt))
        · exact absurd h.symm (ne_of_lt hgt)
        · exact h
    have hprio_l : ∀ a, priorityOf a l₁ = priorityOf a l₂ := by
      intro a
      by_cases hak : a < k₁
      · rw [← priorityOf_left (l := l₁) (pr := p₂) (r := r₁) hak,
            ← priorityOf_left (l := l₂) (pr := p₂) (r := r₂) hak]
        exact hprio a
      · rw [priorityOf_eq_none_of_not_mem hs₁.2.2.1 (fun h => hak (hs₁.1.of_mem h)),
            priorityOf_eq_none_of_not_mem hs₂.2.2.1 (fun h => hak (hs₂.1.of_mem h))]
    have hprio_r : ∀ a, priorityOf a r₁ = priorityOf a r₂ := by
      intro a
      by_cases hak : k₁ < a
      · rw [← priorityOf_right (l := l₁) (pr := p₂) (r := r₁) hak,
            ← priorityOf_right (l := l₂) (pr := p₂) (r := r₂) hak]
        exact hprio a
      · rw [priorityOf_eq_none_of_not_mem hs₁.2.2.2 (fun h => hak (hs₁.2.1.of_mem h)),
            priorityOf_eq_none_of_not_mem hs₂.2.2.2 (fun h => hak (hs₂.2.1.of_mem h))]
    have hinj_l : PriorityInjective l₁ := by
      intro a b ha hb hab
      refine hinj a b (Or.inl ha) (Or.inl hb) ?_
      rw [priorityOf_left (hs₁.1.of_mem ha), priorityOf_left (hs₁.1.of_mem hb)]
      exact hab
    have hinj_r : PriorityInjective r₁ := by
      intro a b ha hb hab
      refine hinj a b (Or.inr (Or.inr ha)) (Or.inr (Or.inr hb)) ?_
      rw [priorityOf_right (hs₁.2.1.of_mem ha), priorityOf_right (hs₁.2.1.of_mem hb)]
      exact hab
    rw [ihl l₂ ⟨hs₁.2.2.1, ho₁.2.2.1⟩ ⟨hs₂.2.2.1, ho₂.2.2.1⟩ hmem_l hprio_l hinj_l,
      ihr r₂ ⟨hs₁.2.2.2, ho₁.2.2.2⟩ ⟨hs₂.2.2.2, ho₂.2.2.2⟩ hmem_r hprio_r hinj_r]

/-- **Uniqueness**: at most one valid treap represents a given
key/priority assignment. Combined with a construction this is the `∃!`; on its own it is the fact
that actually matters, since it says a treap's shape is a function of its *data*, not of the order
the data arrived in. -/
theorem eq_of_represents {t₁ t₂ : Treap α} {ps : List (α × ℕ)}
    (h₁ : Valid t₁) (h₂ : Valid t₂) (hr₁ : Represents t₁ ps) (hr₂ : Represents t₂ ps)
    (hinj : PriorityInjective t₁) : t₁ = t₂ := by
  refine eq_of_valid t₁ t₂ h₁ h₂ (fun a => (hr₁.1 a).trans (hr₂.1 a).symm) (fun a => ?_) hinj
  by_cases ha : a ∈ ps.map Prod.fst
  · obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ha
    subst hxa
    rw [hr₁.2 x.1 x.2 (by simpa using hx), hr₂.2 x.1 x.2 (by simpa using hx)]
  · rw [priorityOf_eq_none_of_not_mem h₁.1 (fun h => ha ((hr₁.1 a).mp h)),
      priorityOf_eq_none_of_not_mem h₂.1 (fun h => ha ((hr₂.1 a).mp h))]

/-! ### Existence: the construction, and the `∃!`

Insert the pairs one by one: `priorityOf_insert_other` and `priorityOf_insert_self` give every
key its priority. The latter needs the key absent, which distinct keys in the list provide. -/

/-- Build a treap by inserting each pair in turn. Any order works — that is what uniqueness
says — so the head-first fold here is a choice of convenience, not of semantics. -/
def ofList : List (α × ℕ) → Treap α
  | [] => leaf
  | x :: ps => insert x.1 x.2 (ofList ps)

theorem valid_ofList (ps : List (α × ℕ)) : Valid (ofList ps) := by
  induction ps with
  | nil => exact ⟨trivial, trivial⟩
  | cons x xs ih => exact valid_insert ih x.1 x.2

theorem mem_ofList (ps : List (α × ℕ)) (a : α) : Mem a (ofList ps) ↔ a ∈ ps.map Prod.fst := by
  induction ps with
  | nil => simp [ofList]
  | cons x xs ih =>
    rw [ofList, mem_insert, ih]
    simp

theorem priorityOf_ofList : ∀ (ps : List (α × ℕ)), (ps.map Prod.fst).Nodup →
    ∀ a n, (a, n) ∈ ps → priorityOf a (ofList ps) = some n := by
  intro ps
  induction ps with
  | nil => simp
  | cons x xs ih =>
    intro h a n hmem
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, hnd⟩ := h
    rcases List.mem_cons.mp hmem with heq | hmem'
    · rw [ofList, ← heq]
      exact priorityOf_insert_self _ _ _ (valid_ofList xs).1 (fun hc => hx (by
        rw [← heq]; rwa [mem_ofList] at hc))
    · have hne : a ≠ x.1 := by
        intro hc
        exact hx (List.mem_map.mpr ⟨(a, n), hmem', hc⟩)
      rw [ofList, priorityOf_insert_other hne _ _ (valid_ofList xs).1]
      exact ih hnd a n hmem'

theorem represents_ofList {ps : List (α × ℕ)} (h : (ps.map Prod.fst).Nodup) :
    Represents (ofList ps) ps :=
  ⟨mem_ofList ps, priorityOf_ofList ps h⟩

theorem priorityInjective_ofList : ∀ (ps : List (α × ℕ)), (ps.map Prod.fst).Nodup →
    (ps.map Prod.snd).Nodup → PriorityInjective (ofList ps) := by
  intro ps hk hp a b ha hb hab
  obtain ⟨x, hx, hxa⟩ := List.mem_map.mp ((mem_ofList ps a).mp ha)
  obtain ⟨y, hy, hyb⟩ := List.mem_map.mp ((mem_ofList ps b).mp hb)
  obtain ⟨xa, xp⟩ := x
  obtain ⟨ya, yp⟩ := y
  simp only at hxa hyb
  subst hxa; subst hyb
  rw [priorityOf_ofList ps hk _ _ hx, priorityOf_ofList ps hk _ _ hy] at hab
  have hpp : xp = yp := Option.some.inj hab
  subst hpp
  exact congrArg Prod.fst (List.inj_on_of_nodup_map hp hx hy rfl)

/-- **Exactly one valid treap holds a given key/priority assignment** — the `∃!`, for a
list with distinct keys and distinct priorities. Existence is the fold; uniqueness is
`eq_of_represents`. -/
theorem existsUnique_of_nodup {ps : List (α × ℕ)}
    (hk : (ps.map Prod.fst).Nodup) (hp : (ps.map Prod.snd).Nodup) :
    ∃! t : Treap α, Valid t ∧ Represents t ps := by
  refine ⟨ofList ps, ⟨valid_ofList ps, represents_ofList hk⟩, ?_⟩
  rintro t ⟨ht, hr⟩
  exact (eq_of_represents (valid_ofList ps) ht (represents_ofList hk) hr
    (priorityInjective_ofList ps hk hp)).symm

/-- **Insertion order does not matter.** Feeding the same key/priority pairs in any order lands on
exactly the same tree — the practical form of uniqueness, and the reason a random-priority analysis
says anything about a treap whose insertion sequence was chosen adversarially. -/
theorem ofList_eq_of_perm {ps qs : List (α × ℕ)} (hk : (ps.map Prod.fst).Nodup)
    (hp : (ps.map Prod.snd).Nodup) (h : ps.Perm qs) : ofList ps = ofList qs := by
  have hkq : (qs.map Prod.fst).Nodup := (h.map Prod.fst).nodup_iff.mp hk
  refine eq_of_represents (valid_ofList ps) (valid_ofList qs) (represents_ofList hk) ?_
    (priorityInjective_ofList ps hk hp)
  refine ⟨fun a => (mem_ofList qs a).trans ?_, fun a n hmem => ?_⟩
  · exact ⟨fun hx => (h.map Prod.fst).mem_iff.mpr hx, fun hx => (h.map Prod.fst).mem_iff.mp hx⟩
  · exact priorityOf_ofList qs hkq a n (h.mem_iff.mp hmem)

/-- **`DeleteSpec` pins the result.** On a valid tree whose keys carry distinct priorities, two
trees that both meet the deletion obligation are the same tree: they hold the same keys, the
same priorities (the deleted key has none in either), and uniqueness (`eq_of_valid`) does the
rest. So the spec says everything a deletion can say, not only which keys survive. -/
theorem eq_of_deleteSpec {a : α} {t t₁ t₂ : Treap α} (ht : Valid t) (hinj : PriorityInjective t)
    (h₁ : DeleteSpec a t t₁) (h₂ : DeleteSpec a t t₂) : t₁ = t₂ := by
  have hv₁ := h₁.2.2 ht
  have hv₂ := h₂.2.2 ht
  have hmem : ∀ b, Mem b t₁ ↔ Mem b t₂ := fun b => (h₁.1 b).trans (h₂.1 b).symm
  refine eq_of_valid t₁ t₂ hv₁ hv₂ hmem (fun b => ?_) (fun x y hx hy hxy => ?_)
  · by_cases hb : b = a
    · subst hb
      rw [priorityOf_eq_none_of_not_mem hv₁.1 (fun h => ((h₁.1 b).mp h).1 rfl),
        priorityOf_eq_none_of_not_mem hv₂.1 (fun h => ((h₂.1 b).mp h).1 rfl)]
    · rw [h₁.2.1 b hb, h₂.2.1 b hb]
  · have hx' := (h₁.1 x).mp hx
    have hy' := (h₁.1 y).mp hy
    rw [h₁.2.1 x hx'.1, h₁.2.1 y hy'.1] at hxy
    exact hinj x y hx'.2 hy'.2 hxy

/-- **Insertion admits one tree.** Two results of inserting `a` at `pr` into the same valid treap
that meet `InsertSpec` are the same tree, when their priorities are distinct. A key already present
keeps its priority, so the obligation fixes every priority after the insertion. -/
theorem eq_of_insertSpec {a : α} {pr : ℕ} {t t₁ t₂ : Treap α} (ht : Valid t)
    (hinj : PriorityInjective t₁) (h₁ : InsertSpec a pr t t₁) (h₂ : InsertSpec a pr t t₂) :
    t₁ = t₂ := by
  refine eq_of_valid t₁ t₂ (h₁.2.2.2 ht) (h₂.2.2.2 ht)
    (fun b => (h₁.1 b).trans (h₂.1 b).symm) (fun b => ?_) hinj
  by_cases hb : b ≠ a ∨ Mem a t
  · rw [h₁.2.1 b hb, h₂.2.1 b hb]
  · push Not at hb
    obtain ⟨rfl, hna⟩ := hb
    rw [h₁.2.2.1 hna, h₂.2.2.1 hna]

end Treap

end AlgoDesign.Searching
