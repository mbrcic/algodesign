/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Delete.Algorithm

/-!
# B-tree deletion: merging

The vocabulary for reasoning about a node rearranged around one child — its children lists read
elementwise, and a node read as prefix, hole, suffix — and what `mergeNodes` preserves.
-/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree

variable {α : Type} [LinearOrder α]

/-! ## Vocabulary for reasoning about a rearranged node

`bounded_hole` and `bounded_pair` describe a node with one child, or two children and the key
between them, replaced: `Bounded` is the one positional invariant. The other three are properties
of the child set, stated elementwise by the `_iff` lemmas below. -/

/-! ## Children lists, elementwise

`ChildrenKeyCountOk`, `ChildrenOneMoreChild` and `MemChildren` all walk a list one cons at a time,
which makes every proof about a *rearranged* child list an induction. They are each equivalent to a
plain statement over the list's members, and with that the rearrangements become bookkeeping. -/

omit [LinearOrder α] in
theorem childrenKeyCountOk_iff {deg : ℕ} (cs : List (BTree α)) :
    ChildrenKeyCountOk deg cs ↔ ∀ c ∈ cs, KeyCountOk deg false c := by
  induction cs with
  | nil => simp [ChildrenKeyCountOk]
  | cons c cs ih =>
      simp only [childrenKeyCountOk_cons, ih, List.mem_cons]
      exact ⟨fun ⟨h1, h2⟩ x hx => hx.elim (fun h => h ▸ h1) (h2 x),
             fun h => ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩⟩

omit [LinearOrder α] in
theorem arityChildren_iff (cs : List (BTree α)) :
    ChildrenOneMoreChild cs ↔ ∀ c ∈ cs, OneMoreChild c := by
  induction cs with
  | nil => simp [ChildrenOneMoreChild]
  | cons c cs ih =>
      simp only [arityChildren_cons, ih, List.mem_cons]
      exact ⟨fun ⟨h1, h2⟩ x hx => hx.elim (fun h => h ▸ h1) (h2 x),
             fun h => ⟨h c (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩⟩

omit [LinearOrder α] in
theorem memChildren_iff (b : α) (cs : List (BTree α)) :
    MemChildren b cs ↔ ∃ c ∈ cs, Mem b c := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      simp only [memChildren_cons, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨x, hx, hb⟩)
        · exact ⟨c, Or.inl rfl, h⟩
        · exact ⟨x, Or.inr hx, hb⟩
      · rintro ⟨x, rfl | hx, hb⟩
        · exact Or.inl hb
        · exact Or.inr ⟨x, hx, hb⟩

omit [LinearOrder α] in
theorem childrenDepth?_iff {cs : List (BTree α)} {d : ℕ} (hne : cs ≠ []) :
    childrenDepth? cs = some d ↔ ∀ c ∈ cs, depth? c = some d :=
  ⟨fun h _ hc => childrenDepth?_uniform h hc, childrenDepth?_of_forall hne⟩

/-! ## A node read as prefix, hole, suffix

`Bounded` is the one invariant that is positional — a child's legal range is set by the two keys
flanking it — so replacing one child means knowing exactly which range it had to satisfy. These
are those two keys. -/

theorem boundedKeys_cons {lo hi : Option α} {k : α} {ks : List α}
    (hlo : ∀ x ∈ lo, x < k) (hhi : ∀ y ∈ hi, k < y) (h : BoundedKeys (some k) hi ks) :
    BoundedKeys lo hi (k :: ks) := by
  refine ⟨List.pairwise_cons.mpr ⟨fun y hy => h.2.1 k rfl y hy, h.1⟩, ?_, ?_⟩
  · intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hlo x hx
    · exact lt_trans (hlo x hx) (h.2.1 k rfl y hy)
  · intro y hy z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hhi y hy
    · exact h.2.2 y hy z hz

theorem boundedKeys_tail {lo hi : Option α} {k : α} {ks : List α}
    (h : BoundedKeys lo hi (k :: ks)) : BoundedKeys lo hi ks :=
  ⟨(List.pairwise_cons.mp h.1).2,
   fun x hx y hy => h.2.1 x hx y (List.mem_cons_of_mem _ hy),
   fun y hy z hz => h.2.2 y hy z (List.mem_cons_of_mem _ hz)⟩

/-- The key immediately left of the hole, or the node's own lower bound if the hole is first. -/
def loAt (lo : Option α) (kl : List α) : Option α := kl.getLast?.or lo

/-- The key immediately right of the hole, or the node's own upper bound if the hole is last. -/
def hiAt (hi : Option α) (kr : List α) : Option α := kr.head?.or hi

omit [LinearOrder α] in
@[simp] theorem loAt_nil (lo : Option α) : loAt lo ([] : List α) = lo := rfl

omit [LinearOrder α] in
@[simp] theorem hiAt_nil (hi : Option α) : hiAt hi ([] : List α) = hi := rfl

omit [LinearOrder α] in
@[simp] theorem hiAt_cons (hi : Option α) (k : α) (kr : List α) :
    hiAt hi (k :: kr) = some k := rfl

omit [LinearOrder α] in
theorem loAt_cons (lo : Option α) (k : α) (kl : List α) :
    loAt lo (k :: kl) = loAt (some k) kl := by
  cases kl with
  | nil => rfl
  | cons k' kl' =>
      simp only [loAt, List.getLast?_cons_cons, Option.or]
      cases h : (k' :: kl').getLast? with
      | none => simp at h
      | some x => simp

/-- **Open a node at one of its children.** From the node's own `Bounded`, the child at the hole
satisfies the range its two flanking keys set — and any replacement satisfying that same range
puts the node back together. This is what makes `ensureSpare`'s rearrangements provable: each one
replaces a child (or two) and the keys around it, and nothing else has to be re-derived. -/
theorem bounded_hole : ∀ (kl : List α) (cl : List (BTree α)), cl.length = kl.length →
    ∀ (lo hi : Option α) (kr : List α) (cr : List (BTree α)) (t : BTree α),
      Bounded lo hi (node (kl ++ kr) (cl ++ t :: cr)) →
        Bounded (loAt lo kl) (hiAt hi kr) t ∧
        ∀ x : BTree α, Bounded (loAt lo kl) (hiAt hi kr) x →
          Bounded lo hi (node (kl ++ kr) (cl ++ x :: cr)) := by
  intro kl
  induction kl with
  | nil =>
      intro cl hlen lo hi kr cr t hb
      obtain rfl : cl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      obtain ⟨hk, hlen', hbc⟩ := hb
      cases kr with
      | nil =>
          simp only [List.nil_append, boundsList, BoundedChildren] at hbc
          refine ⟨hbc.1, fun x hx => ⟨hk, hlen', ?_⟩⟩
          simp only [List.nil_append, boundsList, BoundedChildren]
          exact ⟨hx, hbc.2⟩
      | cons k kr' =>
          simp only [List.nil_append, boundsList, BoundedChildren] at hbc
          refine ⟨hbc.1, fun x hx => ⟨hk, hlen', ?_⟩⟩
          simp only [List.nil_append, boundsList, BoundedChildren]
          exact ⟨hx, hbc.2⟩
  | cons k kl' ih =>
      intro cl hlen lo hi kr cr t hb
      obtain ⟨c, cl', rfl⟩ : ∃ c cl', cl = c :: cl' := by
        cases cl with
        | nil => simp at hlen
        | cons c cl' => exact ⟨c, cl', rfl⟩
      obtain ⟨hk, hlen', hbc⟩ := hb
      simp only [List.cons_append, boundsList, BoundedChildren] at hbc
      obtain ⟨hbcc, hrest⟩ := hbc
      have hinner : Bounded (some k) hi (node (kl' ++ kr) (cl' ++ t :: cr)) := by
        refine ⟨BoundedKeys.of_cons hk, ?_, hrest⟩
        simp only [List.cons_append, List.length_cons, List.length_append] at hlen' ⊢
        omega
      obtain ⟨ht, hput⟩ := ih cl' (by simpa using hlen) (some k) hi kr cr t hinner
      rw [loAt_cons]
      refine ⟨ht, fun x hx => ?_⟩
      obtain ⟨-, -, hbc'⟩ := hput x hx
      refine ⟨hk, ?_, ?_⟩
      · simp only [List.cons_append, List.length_cons, List.length_append] at hlen' ⊢
        omega
      · simp only [List.cons_append, boundsList, BoundedChildren]
        exact ⟨hbcc, hbc'⟩

/-- **Open a node at two adjacent children and the key between them.** Borrowing replaces that
triple by another; merging replaces it by a single child and drops the key. Both are covered
here, along with what the triple has to satisfy in the first place. -/
theorem bounded_pair : ∀ (kl : List α) (cl : List (BTree α)), cl.length = kl.length →
    ∀ (lo hi : Option α) (s : α) (kr : List α) (l r : BTree α) (cr : List (BTree α)),
      Bounded lo hi (node (kl ++ s :: kr) (cl ++ l :: r :: cr)) →
        (Bounded (loAt lo kl) (some s) l ∧ Bounded (some s) (hiAt hi kr) r ∧
         (∀ x ∈ loAt lo kl, x < s) ∧ (∀ y ∈ hiAt hi kr, s < y)) ∧
        (∀ (l' : BTree α) (s' : α) (r' : BTree α), Bounded (loAt lo kl) (some s') l' →
           Bounded (some s') (hiAt hi kr) r' →
           (∀ x ∈ loAt lo kl, x < s') → (∀ y ∈ hiAt hi kr, s' < y) →
           Bounded lo hi (node (kl ++ s' :: kr) (cl ++ l' :: r' :: cr))) ∧
        (∀ m : BTree α, Bounded (loAt lo kl) (hiAt hi kr) m →
           Bounded lo hi (node (kl ++ kr) (cl ++ m :: cr))) := by
  intro kl
  induction kl with
  | nil =>
      intro cl hlen lo hi s kr l r cr hb
      obtain rfl : cl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      obtain ⟨hk, hlen', hbc⟩ := hb
      simp only [List.nil_append, boundsList, BoundedChildren] at hbc
      obtain ⟨hl, hrest⟩ := hbc
      have hlo_s : ∀ x ∈ lo, x < s := fun x hx => hk.2.1 x hx s (List.mem_cons_self ..)
      cases kr with
      | nil =>
          simp only [boundsList, BoundedChildren] at hrest
          obtain ⟨hr, hcr⟩ := hrest
          obtain rfl : cr = [] := by
            cases cr with
            | nil => rfl
            | cons _ _ => simp [BoundedChildren] at hcr
          have hs_hi : ∀ y ∈ hi, s < y := fun y hy => hk.2.2 y hy s (List.mem_cons_self ..)
          refine ⟨⟨hl, hr, hlo_s, hs_hi⟩, ?_, ?_⟩
          · intro l' s' r' hl' hr' hlo' hhi'
            simp only [loAt_nil, hiAt_nil] at hl' hr' hlo' hhi'
            refine ⟨⟨by simp, ?_, ?_⟩, by simp, ?_⟩
            · intro x hx y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hlo' x hx
              · simp at hy
            · intro x hx y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hhi' x hx
              · simp at hy
            · simp only [List.nil_append, boundsList, BoundedChildren]
              exact ⟨hl', hr', trivial⟩
          · intro m hm
            simp only [loAt_nil, hiAt_nil] at hm
            refine ⟨by simp [BoundedKeys], by simp, ?_⟩
            simp only [List.nil_append, boundsList, BoundedChildren]
            exact ⟨hm, trivial⟩
      | cons k kr' =>
          simp only [boundsList, BoundedChildren] at hrest
          obtain ⟨hr, hcr⟩ := hrest
          have hsk : s < k := (List.pairwise_cons.mp hk.1).1 k (List.mem_cons_self ..)
          refine ⟨⟨hl, hr, hlo_s, by simpa using hsk⟩, ?_, ?_⟩
          · intro l' s' r' hl' hr' hlo' hhi'
            simp only [loAt_nil, hiAt_cons] at hl' hr' hlo' hhi'
            have hs'k : s' < k := hhi' k rfl
            refine ⟨⟨?_, ?_, ?_⟩, by simpa using hlen', ?_⟩
            · refine List.pairwise_cons.mpr ⟨?_, (List.pairwise_cons.mp hk.1).2⟩
              intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hs'k
              · exact lt_trans hs'k ((List.pairwise_cons.mp
                  (List.pairwise_cons.mp hk.1).2).1 y hy)
            · intro x hx y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact hlo' x hx
              · exact hk.2.1 x hx y (List.mem_cons_of_mem _ hy)
            · intro x hx y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · exact lt_trans hs'k (hk.2.2 x hx k (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
              · exact hk.2.2 x hx y (List.mem_cons_of_mem _ hy)
            · simp only [List.nil_append, boundsList, BoundedChildren]
              exact ⟨hl', hr', hcr⟩
          · intro m hm
            simp only [loAt_nil, hiAt_cons] at hm
            refine ⟨boundedKeys_tail hk, ?_, ?_⟩
            · simp at hlen' ⊢; omega
            · simp only [List.nil_append, boundsList, BoundedChildren]
              exact ⟨hm, hcr⟩
  | cons k kl' ih =>
      intro cl hlen lo hi s kr l r cr hb
      obtain ⟨c, cl', rfl⟩ : ∃ c cl', cl = c :: cl' := by
        cases cl with
        | nil => simp at hlen
        | cons c cl' => exact ⟨c, cl', rfl⟩
      obtain ⟨hk, hlen', hbc⟩ := hb
      simp only [List.cons_append, boundsList, BoundedChildren] at hbc
      obtain ⟨hbcc, hrest⟩ := hbc
      have hinner : Bounded (some k) hi (node (kl' ++ s :: kr) (cl' ++ l :: r :: cr)) := by
        refine ⟨BoundedKeys.of_cons hk, ?_, hrest⟩
        simp only [List.cons_append, List.length_cons, List.length_append] at hlen' ⊢
        omega
      obtain ⟨hget, hput, hmerge⟩ := ih cl' (by simpa using hlen) (some k) hi s kr l r cr hinner
      have hlok : ∀ x ∈ lo, x < k := fun x hx => hk.2.1 x hx k (List.mem_cons_self ..)
      have hhik : ∀ y ∈ hi, k < y := fun y hy => hk.2.2 y hy k (List.mem_cons_self ..)
      rw [loAt_cons]
      refine ⟨hget, ?_, ?_⟩
      · intro l' s' r' hl' hr' hlo' hhi'
        obtain ⟨hk'', -, hbc'⟩ := hput l' s' r' hl' hr' hlo' hhi'
        refine ⟨boundedKeys_cons hlok hhik hk'', ?_, ?_⟩
        · simp only [List.cons_append, List.length_cons, List.length_append] at hlen' ⊢
          omega
        · simp only [List.cons_append, boundsList, BoundedChildren]
          exact ⟨hbcc, hbc'⟩
      · intro m hm
        obtain ⟨hk'', -, hbc'⟩ := hmerge m hm
        refine ⟨boundedKeys_cons hlok hhik hk'', ?_, ?_⟩
        · simp only [List.cons_append, List.length_cons, List.length_append] at hlen' ⊢
          omega
        · simp only [List.cons_append, boundsList, BoundedChildren]
          exact ⟨hbcc, hbc'⟩

/-! ## Merging two siblings around their separator -/

omit [LinearOrder α] in
@[simp] theorem nodeKeys_mergeNodes {d : ℕ} {l r : BTree α} {s : α}
    (hl : depth? l = some d) (hr : depth? r = some d) :
    nodeKeys (mergeNodes l s r) = nodeKeys l ++ s :: nodeKeys r := by
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk => rfl
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hl.symm
          subst this
          simp [depth?] at hr
  | node lk lc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hr.symm
          subst this
          simp [depth?] at hl
      | node rk rc => rfl

omit [LinearOrder α] in
theorem mem_mergeNodes {d : ℕ} {l r : BTree α} {s b : α}
    (hl : depth? l = some d) (hr : depth? r = some d) :
    Mem b (mergeNodes l s r) ↔ (Mem b l ∨ b = s ∨ Mem b r) := by
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk => simp only [mergeNodes, mem_leaf, List.mem_append, List.mem_cons]
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hl.symm
          subst this; simp [depth?] at hr
  | node lk lc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hr.symm
          subst this; simp [depth?] at hl
      | node rk rc =>
          simp only [mergeNodes, mem_node, List.mem_append, List.mem_cons,
            memChildren_iff b, List.mem_append]
          constructor
          · rintro (h | ⟨c, hc | hc, hb⟩)
            · tauto
            · exact Or.inl (Or.inr ⟨c, hc, hb⟩)
            · exact Or.inr (Or.inr (Or.inr ⟨c, hc, hb⟩))
          · rintro ((h | ⟨c, hc, hb⟩) | rfl | (h | ⟨c, hc, hb⟩))
            · tauto
            · exact Or.inr ⟨c, Or.inl hc, hb⟩
            · tauto
            · tauto
            · exact Or.inr ⟨c, Or.inr hc, hb⟩

omit [LinearOrder α] in
theorem depth_mergeNodes {d : ℕ} {l r : BTree α} {s : α}
    (hl : depth? l = some d) (hr : depth? r = some d) :
    depth? (mergeNodes l s r) = some d := by
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk => simpa [mergeNodes, depth?] using hl
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hl.symm
          subst this; simp [depth?] at hr
  | node lk lc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hr.symm
          subst this; simp [depth?] at hl
      | node rk rc =>
          obtain ⟨d₁, hd₁, rfl⟩ : ∃ e, childrenDepth? lc = some e ∧ d = e + 1 := by
            simp only [depth?, Option.map_eq_some_iff] at hl
            obtain ⟨e, h₁, h₂⟩ := hl; exact ⟨e, h₁, h₂.symm⟩
          have hd₂ : childrenDepth? rc = some d₁ := by
            simp only [depth?, Option.map_eq_some_iff] at hr
            obtain ⟨e, h₁, h₂⟩ := hr
            have : e = d₁ := by omega
            exact this ▸ h₁
          have hlc : lc ≠ [] := by intro h; rw [h] at hd₁; simp [childrenDepth?] at hd₁
          have hall : ∀ c ∈ lc ++ rc, depth? c = some d₁ := by
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact childrenDepth?_uniform hd₁ hc
            · exact childrenDepth?_uniform hd₂ hc
          have : childrenDepth? (lc ++ rc) = some d₁ :=
            childrenDepth?_of_forall (by simp [hlc]) hall
          simp [mergeNodes, depth?, this]

/-! ## What the three rearrangements preserve

Merging two siblings over their separator, and borrowing from either side, each against ordering,
balance, occupancy, arity and the key set. A merge happens only when neither side has a spare key,
so it fits: `(deg - 1) + 1 + (deg - 1) = 2 * deg - 1`. -/

/-- A key list split around one key, both halves bounded by it, is bounded as a whole. -/
theorem boundedKeys_append {lo hi : Option α} {lk rk : List α} {s : α}
    (hl : BoundedKeys lo (some s) lk) (hr : BoundedKeys (some s) hi rk)
    (hlo : ∀ x ∈ lo, x < s) (hhi : ∀ y ∈ hi, s < y) :
    BoundedKeys lo hi (lk ++ s :: rk) := by
  have hlks : ∀ x ∈ lk, x < s := fun x hx => hl.2.2 s rfl x hx
  have hrks : ∀ y ∈ rk, s < y := fun y hy => hr.2.1 s rfl y hy
  refine ⟨?_, ?_, ?_⟩
  · refine List.pairwise_append.mpr ⟨hl.1, ?_, ?_⟩
    · exact List.pairwise_cons.mpr ⟨hrks, hr.1⟩
    · intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hlks x hx
      · exact lt_trans (hlks x hx) (hrks y hy)
  · intro p hp y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hl.2.1 p hp y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hlo p hp
      · exact lt_trans (hlo p hp) (hrks y hy)
  · intro q hq y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact lt_trans (hlks y hy) (hhi q hq)
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hhi q hq
      · exact hr.2.2 q hq y hy

/-! ## Merging, under the remaining invariants -/

theorem bounded_mergeNodes {d : ℕ} {lo hi : Option α} {l r : BTree α} {s : α}
    (hdl : depth? l = some d) (hdr : depth? r = some d)
    (hl : Bounded lo (some s) l) (hr : Bounded (some s) hi r)
    (hlo : ∀ x ∈ lo, x < s) (hhi : ∀ y ∈ hi, s < y) :
    Bounded lo hi (mergeNodes l s r) := by
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk => exact boundedKeys_append hl hr hlo hhi
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdl.symm
          subst this; simp [depth?] at hdr
  | node lk lc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdr.symm
          subst this; simp [depth?] at hdl
      | node rk rc =>
          obtain ⟨hlk, hllen, hlbc⟩ := hl
          obtain ⟨hrk, hrlen, hrbc⟩ := hr
          refine ⟨boundedKeys_append hlk hrk hlo hhi, ?_, ?_⟩
          · simp only [List.length_append, List.length_cons] at hllen hrlen ⊢
            omega
          · rw [boundsList_append]
            refine (boundedChildren_append ?_).mpr ⟨hlbc, hrbc⟩
            rw [boundsList_length]
            omega

omit [LinearOrder α] in
theorem arity_mergeNodes {d : ℕ} {l r : BTree α} {s : α}
    (hdl : depth? l = some d) (hdr : depth? r = some d)
    (hl : OneMoreChild l) (hr : OneMoreChild r) : OneMoreChild (mergeNodes l s r) := by
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk => trivial
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdl.symm
          subst this; simp [depth?] at hdr
  | node lk lc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdr.symm
          subst this; simp [depth?] at hdl
      | node rk rc =>
          refine ⟨?_, ?_⟩
          · simp only [List.length_append, List.length_cons]
            have := hl.1; have := hr.1
            omega
          · rw [arityChildren_iff]
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact (arityChildren_iff _).mp hl.2 c hc
            · exact (arityChildren_iff _).mp hr.2 c hc

omit [LinearOrder α] in
/-- Merging is only ever reached when neither side has a spare key, and that is exactly what
keeps the result inside the ceiling: `(deg - 1) + 1 + (deg - 1) = 2 * deg - 1`. -/
theorem keyCount_mergeNodes {deg d : ℕ} {l r : BTree α} {s : α} (hdeg : 2 ≤ deg)
    (hdl : depth? l = some d) (hdr : depth? r = some d)
    (hl : KeyCountOk deg false l) (hr : KeyCountOk deg false r)
    (hnl : hasSpare deg l = false) (hnr : hasSpare deg r = false) :
    KeyCountOk deg false (mergeNodes l s r) := by
  have hll : (nodeKeys l).length < deg := by
    simpa [hasSpare] using hnl
  have hrl : (nodeKeys r).length < deg := by
    simpa [hasSpare] using hnr
  have hkeys := nodeKeys_mergeNodes (s := s) hdl hdr
  cases l with
  | leaf lk =>
      cases r with
      | leaf rk =>
          simp only [nodeKeys_leaf] at hll hrl
          have hlm : deg - 1 ≤ lk.length := hl.1.resolve_left (by simp)
          have hrm : deg - 1 ≤ rk.length := hr.1.resolve_left (by simp)
          refine ⟨Or.inr ?_, ?_⟩ <;>
            simp only [List.length_append, List.length_cons] <;> omega
      | node rk rc =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdl.symm
          subst this; simp [depth?] at hdr
  | node lk lc =>
      cases r with
      | leaf rk =>
          exfalso
          have : d = 0 := by simpa [depth?] using hdr.symm
          subst this; simp [depth?] at hdl
      | node rk rc =>
          simp only [nodeKeys_node] at hll hrl
          have hlm : deg - 1 ≤ lk.length := hl.1
          have hrm : deg - 1 ≤ rk.length := hr.1
          refine ⟨?_, ?_, ?_⟩
          · change deg - 1 ≤ (lk ++ s :: rk).length
            simp only [List.length_append, List.length_cons]
            omega
          · simp only [List.length_append, List.length_cons]
            omega
          · rw [childrenKeyCountOk_iff]
            intro c hc
            rcases List.mem_append.mp hc with hc | hc
            · exact (childrenKeyCountOk_iff _).mp hl.2.2 c hc
            · exact (childrenKeyCountOk_iff _).mp hr.2.2 c hc

end BTree

end AlgoDesign.Searching
