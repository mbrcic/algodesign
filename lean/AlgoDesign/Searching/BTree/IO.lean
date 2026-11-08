/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.BTree.Cost
public import Mathlib.Algebra.Group.Prod

/-!
# B-tree reads and writes, counted apart (CLRS's `DISK-READ` and `DISK-WRITE`)

The cost is a pair `(reads, writes)` in `TimeM (ℕ × ℕ)`. The `IO` in `searchIO`, `insertIO` and
`deleteIO` is input and output to the disk, counted: nothing here runs in Lean's `IO` monad.

Reads: every node entered, the root included (CLRS keeps the root in memory, so its count is one
less). For search and insertion the reads are `Cost.lean`'s count (`reads_searchIO`,
`reads_insertIO`); deletion also reads the siblings it inspects before borrowing or merging,
`delRecSibReads`, at most two per level (`reads_deleteIO`).

Writes: three per split, one for the leaf an insertion lands on. For deletion, where `delRec`
changes a block: three for a borrow, two for a merge, one for replacing a key by its predecessor
or successor, one for a leaf, none for the root collapse. A branch that changes nothing is still
charged, so the deletion bound is an upper bound. -/

@[expose] public section

namespace AlgoDesign.Searching

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

namespace BTree.Node

variable {α : Type} [LinearOrder α] {deg : ℕ}

/-- `search` with the pair cost: one read per node entered, no write anywhere. -/
def searchIO (a : α) (t : Node α) : TimeM (ℕ × ℕ) Bool :=
  ⟨(searchM a t).ret, ((searchM a t).time, 0)⟩

theorem ret_searchIO (a : α) (t : Node α) : (searchIO a t).ret = search a t :=
  ret_searchM a t

/-- The read component is `searchM`'s count. -/
theorem reads_searchIO (a : α) (t : Node α) : (searchIO a t).time.1 = (searchM a t).time := rfl

/-- **A search writes nothing.** -/
theorem writes_searchIO (a : α) (t : Node α) : (searchIO a t).time.2 = 0 := rfl

/-- **Search: at most `log_deg((n+1)/2) + 1` reads, root included, and no write.** -/
theorem searchIO_le_log {deg : ℕ} {bt : Node α} (hv : RootLegal deg bt) (hsz : 1 ≤ bt.size)
    (a : α) : (searchIO a bt).time.1 ≤ Nat.log deg ((bt.size + 1) / 2) + 1
      ∧ (searchIO a bt).time.2 = 0 :=
  ⟨time_searchM_le_log hv hsz a, rfl⟩

/-- Did `prepare` split the child it hands back? Mirrors `prepare`'s branches; where `prepare`
answers `some`, this is `1` exactly when the answer came through `splitNode`. -/
def prepareSplits (deg : ℕ) (a : α) : List α → List (Node α) → ℕ
  | k :: ks, c :: cs =>
      if a < k then (if isFull deg c then 1 else 0)
      else if k < a then prepareSplits deg a ks cs
      else 0
  | [], c :: _ => if isFull deg c then 1 else 0
  | _, [] => 0

omit [LinearOrder α] in
theorem prepareSplits_le_one (deg : ℕ) (a : α) [LinearOrder α] :
    ∀ (ks : List α) (cs : List (Node α)), prepareSplits deg a ks cs ≤ 1
  | k :: ks, c :: cs => by
      simp only [prepareSplits]
      split_ifs <;> first | omega | exact prepareSplits_le_one deg a ks cs
  | [], c :: _ => by simp only [prepareSplits]; split_ifs <;> omega
  | [], [] => by simp [prepareSplits]
  | _ :: _, [] => by simp [prepareSplits]

/-- `insNonfull` with the pair cost: a read per node entered, three writes for a proactive split
(`B-TREE-SPLIT-CHILD`), one for the leaf the key lands in. -/
def insNonfullIO (deg : ℕ) (a : α) : Node α → TimeM (ℕ × ℕ) (Node α)
  | leaf ks => do
      tick (1, 1)
      pure (leaf (insKeys a ks))
  | node ks cs =>
      match _hprep : prepare deg a ks cs with
      | none => do
          tick (1, 0)
          pure (node ks cs)
      | some d => do
          tick (1, 3 * prepareSplits deg a ks cs)
          let t ← insNonfullIO deg a d.target
          pure (node d.keys (d.before ++ t :: d.after))
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height _hprep
    simp only [height_node]
    omega

/-- The pair-cost run returns what the single-count run returns, and reads what it charges. -/
theorem insNonfullIO_eq (deg : ℕ) (a : α) :
    ∀ t : Node α, (insNonfullIO deg a t).ret = (insNonfullM deg a t).ret
      ∧ (insNonfullIO deg a t).time.1 = (insNonfullM deg a t).time
  | leaf ks => by simp [insNonfullIO, insNonfullM]
  | node ks cs => by
      have ih : ∀ d : Descent α, prepare deg a ks cs = some d →
          (insNonfullIO deg a d.target).ret = (insNonfullM deg a d.target).ret
            ∧ (insNonfullIO deg a d.target).time.1 = (insNonfullM deg a d.target).time := by
        intro d hd
        exact insNonfullIO_eq deg a d.target
      rw [insNonfullIO, insNonfullM]
      split
      · rename_i hn
        split
        · simp
        · rename_i d hd
          rw [hn] at hd
          cases hd
      · rename_i d hd
        split
        · rename_i hn
          rw [hn] at hd
          cases hd
        · rename_i d' hd'
          rw [hd] at hd'
          cases hd'
          obtain ⟨h1, h2⟩ := ih d hd
          simp only [ret_bind, time_bind, time_tick, ret_pure, time_pure, Prod.fst_add]
          rw [h1, h2]
          simp
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hd
    simp only [height_node]
    omega

/-- **At most three writes per level, and one for the leaf.** -/
theorem writes_insNonfullIO_le (deg : ℕ) (a : α) :
    ∀ t : Node α, (insNonfullIO deg a t).time.2 ≤ 3 * t.height + 1
  | leaf ks => by simp [insNonfullIO, height]
  | node ks cs => by
      have ih : ∀ d : Descent α, prepare deg a ks cs = some d →
          (insNonfullIO deg a d.target).time.2 ≤ 3 * d.target.height + 1 := by
        intro d hd
        exact writes_insNonfullIO_le deg a d.target
      rw [insNonfullIO]
      split
      · simp
      · rename_i d hd
        simp only [time_bind, time_tick, time_pure, Prod.snd_add, height_node]
        have hle := prepare_target_height hd
        have := ih d hd
        have := prepareSplits_le_one deg a ks cs
        simp only [Prod.snd_zero]
        omega
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hd
    simp only [height_node]
    omega

/-- `insert` with the pair cost. A full root is split first: `B-TREE-INSERT` allocates the new root
and `B-TREE-SPLIT-CHILD` writes the two halves and the new root, three writes. -/
def insertIO (deg : ℕ) (a : α) (t : Node α) : TimeM (ℕ × ℕ) (Node α) := do
  if isFull deg t then
    match splitNode deg t with
    | none => insNonfullIO deg a t
    | some (l, m, r) => do
        tick (0, 3)
        insNonfullIO deg a (node [m] [l, r])
  else insNonfullIO deg a t

theorem ret_insertIO (deg : ℕ) (a : α) (t : Node α) :
    (insertIO deg a t).ret = insert deg a t := by
  rw [← ret_insertM, insertIO, insertM]
  split
  · split
    · rename_i heq
      simp only [heq]
      exact (insNonfullIO_eq deg a t).1
    · rename_i l m r heq
      simp only [heq, ret_bind]
      exact (insNonfullIO_eq deg a _).1
  · exact (insNonfullIO_eq deg a t).1

/-- The read component is `insertM`'s count: the root split reads nothing new. -/
theorem reads_insertIO (deg : ℕ) (a : α) (t : Node α) :
    (insertIO deg a t).time.1 = (insertM deg a t).time := by
  rw [insertIO, insertM]
  split
  · split
    · rename_i heq
      simp only [heq]
      exact (insNonfullIO_eq deg a t).2
    · rename_i l m r heq
      simp only [heq, time_bind, time_tick, Prod.fst_add]
      rw [Nat.zero_add]
      exact (insNonfullIO_eq deg a _).2
  · exact (insNonfullIO_eq deg a t).2

/-- At a fresh root over two halves that are not full, the descent splits nothing and enters one
of the halves. -/
private theorem prepare_fresh_root {deg : ℕ} {a m : α} {l r : Node α} {d : Descent α}
    (hl : isFull deg l = false) (hr : isFull deg r = false)
    (h : prepare deg a [m] [l, r] = some d) :
    prepareSplits deg a [m] [l, r] = 0 ∧ (d.target = l ∨ d.target = r) := by
  by_cases h1 : a < m
  · simp only [prepare, h1, hl, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at h
    subst h
    simp [prepareSplits, h1, hl]
  · by_cases h2 : m < a
    · simp only [prepare, h1, h2, hr, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at h
      subst h
      simp [prepareSplits, h1, h2, hr]
    · simp [prepare, h1, h2] at h

/-- **An insertion writes at most `3h + 4` blocks**, `h` the height before it: at most one split
(three writes) per level of the tree it started from, the root's included, and one write for the
leaf. The fresh root a root split creates splits nothing, its two halves being half full. -/
theorem writes_insertIO_le {deg : ℕ} (hdeg : 2 ≤ deg) (a : α) (t : Node α) :
    (insertIO deg a t).time.2 ≤ 3 * t.height + 4 := by
  rw [insertIO]
  split
  · rename_i hfull
    split
    · have := writes_insNonfullIO_le deg a t
      omega
    · rename_i l m r hsp
      have hlr := splitNode_height_le hsp
      obtain ⟨hl, hr⟩ := splitNode_not_full hdeg hfull hsp
      simp only [time_bind, time_tick, Prod.snd_add]
      rw [insNonfullIO]
      split
      · simp
      · rename_i d hd
        obtain ⟨h0, ht⟩ := prepare_fresh_root hl hr hd
        simp only [time_bind, time_tick, time_pure, Prod.snd_add, Prod.snd_zero, h0]
        have := writes_insNonfullIO_le deg a d.target
        rcases ht with ht | ht <;> rw [ht] <;> rw [ht] at this <;> omega
  · have := writes_insNonfullIO_le deg a t
    omega

mutual

/-- No node of the tree is full, and every internal node has one more child than keys: the shape
in which an insertion splits nothing. -/
def NoneFull (deg : ℕ) : Node α → Prop
  | leaf ks => isFull deg (leaf ks) = false
  | node ks cs => isFull deg (node ks cs) = false ∧ cs.length = ks.length + 1 ∧ NoneFullAux deg cs

/-- `NoneFull` for every tree of a child list. -/
def NoneFullAux (deg : ℕ) : List (Node α) → Prop
  | [] => True
  | c :: cs => NoneFull deg c ∧ NoneFullAux deg cs

end

omit [LinearOrder α] in
private theorem noneFull_of_mem {deg : ℕ} :
    ∀ {cs : List (Node α)}, NoneFullAux deg cs → ∀ {c}, c ∈ cs → NoneFull deg c
  | [], _, _, hc => by simp at hc
  | _ :: _, h, _, hc => by
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact h.1
      · exact noneFull_of_mem h.2 hc'

omit [LinearOrder α] in
private theorem not_isFull_of_noneFull {deg : ℕ} {t : Node α} (h : NoneFull deg t) :
    isFull deg t = false := by
  cases t with
  | leaf ks => exact h
  | node ks cs => exact h.1

/-- Where no child is full, `prepare` splits nothing and hands back one of the children. -/
private theorem prepare_noneFull {deg : ℕ} {a : α} :
    ∀ {ks : List α} {cs : List (Node α)} {d : Descent α}, NoneFullAux deg cs →
      prepare deg a ks cs = some d → prepareSplits deg a ks cs = 0 ∧ d.target ∈ cs
  | k :: ks, c :: cs, d, hn, h => by
      have hc := not_isFull_of_noneFull hn.1
      by_cases h1 : a < k
      · simp only [prepare, h1, hc, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at h
        subst h
        simp [prepareSplits, h1, hc]
      · by_cases h2 : k < a
        · simp only [prepare, h1, h2, ↓reduceIte] at h
          split at h
          · simp at h
          · rename_i d' hd'
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨h0, hm⟩ := prepare_noneFull hn.2 hd'
            exact ⟨by simp [prepareSplits, h1, h2, h0], List.mem_cons_of_mem _ hm⟩
        · simp [prepare, h1, h2] at h
  | [], c :: cs, d, hn, h => by
      have hc := not_isFull_of_noneFull hn.1
      simp only [prepare, hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [prepareSplits, hc]
  | _, [], d, _, h => by simp [prepare] at h

private theorem writes_insNonfullIO_noneFull (deg : ℕ) (a : α) :
    ∀ t : Node α, NoneFull deg t → (insNonfullIO deg a t).time.2 ≤ 1
  | leaf ks, _ => by simp [insNonfullIO]
  | node ks cs, hn => by
      have ih : ∀ d : Descent α, prepare deg a ks cs = some d →
          (insNonfullIO deg a d.target).time.2 ≤ 1 := by
        intro d hd
        exact writes_insNonfullIO_noneFull deg a d.target
          (noneFull_of_mem hn.2.2 (prepare_noneFull hn.2.2 hd).2)
      rw [insNonfullIO]
      split
      · simp
      · rename_i d hd
        simp only [time_bind, time_tick, time_pure, Prod.snd_add, Prod.snd_zero]
        rw [(prepare_noneFull hn.2.2 hd).1]
        have := ih d hd
        omega
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hd
    simp only [height_node]
    omega

/-- **Without a split, an insertion writes at most the one leaf it lands in** (exactly one when
the descent reaches a leaf; none when the key turns up at an internal node on the way). -/
theorem writes_insertIO_noneFull (deg : ℕ) (a : α) (t : Node α) (h : NoneFull deg t) :
    (insertIO deg a t).time.2 ≤ 1 := by
  rw [insertIO, not_isFull_of_noneFull h]
  exact writes_insNonfullIO_noneFull deg a t h

private theorem writes_insNonfullIO_fresh {deg : ℕ} (hdeg : 2 ≤ deg) (a : α) :
    ∀ t : Node α, NoneFull deg t → ¬ Mem a t → (insNonfullIO deg a t).time.2 = 1
  | leaf ks, _, _ => by simp [insNonfullIO]
  | node ks cs, hn, hm => by
      have ih : ∀ d : Descent α, prepare deg a ks cs = some d →
          (insNonfullIO deg a d.target).time.2 = 1 := by
        intro d hd
        have hin := (prepare_noneFull hn.2.2 hd).2
        exact writes_insNonfullIO_fresh hdeg a d.target (noneFull_of_mem hn.2.2 hin)
          (fun h => hm (Or.inr (memChildren_of_mem hin h)))
      rw [insNonfullIO]
      split
      · rename_i hp
        exact absurd (prepare_none_mem deg hdeg a hn.2.1 hp) hm
      · rename_i d hd
        simp only [time_bind, time_tick, time_pure, Prod.snd_add, Prod.snd_zero]
        rw [(prepare_noneFull hn.2.2 hd).1, ih d hd]
        rfl
  termination_by t => t.height
  decreasing_by
    have hle := prepare_target_height hd
    simp only [height_node]
    omega

/-- **A fresh key into a tree with no full node costs exactly one write**, the leaf it lands in. -/
theorem writes_insertIO_fresh {deg : ℕ} (hdeg : 2 ≤ deg) (a : α) (t : Node α)
    (h : NoneFull deg t) (hm : ¬ Mem a t) : (insertIO deg a t).time.2 = 1 := by
  rw [insertIO, not_isFull_of_noneFull h]
  exact writes_insNonfullIO_fresh hdeg a t h hm

/-- **Insertion, in `n` and `deg`**: at most `log_deg((n+1)/2) + 2` reads (root included) and
`3 · log_deg((n+1)/2) + 4` writes. -/
theorem insertIO_le_log {deg : ℕ} {bt : Node α} (hv : RootLegal deg bt) (hsz : 1 ≤ bt.size)
    (a : α) : (insertIO deg a bt).time.1 ≤ Nat.log deg ((bt.size + 1) / 2) + 2
      ∧ (insertIO deg a bt).time.2 ≤ 3 * Nat.log deg ((bt.size + 1) / 2) + 4 := by
  have hdeg : 2 ≤ deg := hv.2.2.2
  have hstruct : 2 * deg ^ bt.height ≤ bt.size + 1 := two_mul_pow_height_le_size_succ hv hsz
  have hdiv : deg ^ bt.height ≤ (bt.size + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hlog : bt.height ≤ Nat.log deg ((bt.size + 1) / 2) :=
    Nat.le_log_of_pow_le (by omega) hdiv
  refine ⟨by rw [reads_insertIO]; exact time_insertM_le_log hv hsz a, ?_⟩
  have := writes_insertIO_le (deg := deg) hdeg a bt
  omega

/-- The writes `ensureSpare` makes: none when the target already has a spare key, three for a
borrow (parent, target, sibling), two for a merge (parent, merged node; the sibling is freed), none
where the model's branch changes nothing. -/
def spareWrites (deg : ℕ) (sp : Spot α) : ℕ :=
  if hasSpare deg sp.target then 0
  else
    match sp.childrenL.getLast? with
    | some l =>
        if hasSpare deg l then (if (borrowLeftSpot sp).isSome then 3 else 0)
        else
          match sp.childrenR with
          | r :: _ =>
              if hasSpare deg r then (if (borrowRightSpot sp).isSome then 3 else 0)
              else (if (mergeLeftSpot sp).isSome then 2 else 0)
          | [] => if (mergeLeftSpot sp).isSome then 2 else 0
    | none =>
        match sp.childrenR with
        | r :: _ =>
            if hasSpare deg r then (if (borrowRightSpot sp).isSome then 3 else 0)
            else (if (mergeRightSpot sp).isSome then 2 else 0)
        | [] => 0

omit [LinearOrder α] in
theorem spareWrites_le (deg : ℕ) (sp : Spot α) : spareWrites deg sp ≤ 3 := by
  unfold spareWrites
  repeat' split
  all_goals omega

/-- The writes `takeMax` makes: the fix-ups on the way down and the leaf it takes the key from. -/
def takeMaxWrites (deg : ℕ) : Node α → ℕ
  | leaf ks => if ks = [] then 0 else 1
  | node ks cs =>
      match _hc : cs.getLast? with
      | none => 0
      | some c =>
          spareWrites deg ⟨ks, cs.dropLast, c, [], []⟩
            + takeMaxWrites deg (ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩).target
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast _hc
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The mirror, for the walk to the leftmost leaf. -/
def takeMinWrites (deg : ℕ) : Node α → ℕ
  | leaf ks => if ks = [] then 0 else 1
  | node _ [] => 0
  | node ks (c :: cs') =>
      spareWrites deg ⟨[], [], c, ks, cs'⟩
        + takeMinWrites deg (ensureSpare deg ⟨[], [], c, ks, cs'⟩).target
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

omit [LinearOrder α] in
theorem takeMaxWrites_le (deg : ℕ) : ∀ t : Node α, takeMaxWrites deg t ≤ 3 * t.height + 1
  | leaf _ => by simp only [takeMaxWrites]; split_ifs <;> simp [height]
  | node ks cs => by
      have ih : ∀ c : Node α, cs.getLast? = some c →
          takeMaxWrites deg (ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩).target
            ≤ 3 * (ensureSpare deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)).target.height + 1 := by
        intro c hc
        exact takeMaxWrites_le deg _
      rw [takeMaxWrites]
      split
      · simp
      · rename_i c hc
        have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
        have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
          simp only [Spot.children]
          exact dropLast_append_getLast hc
        rw [h2] at h1
        have := ih c hc
        have := spareWrites_le deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
        simp only [height_node]
        omega
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast hc
    rw [h2] at h1
    simp only [height_node]
    omega

omit [LinearOrder α] in
theorem takeMinWrites_le (deg : ℕ) : ∀ t : Node α, takeMinWrites deg t ≤ 3 * t.height + 1
  | leaf _ => by simp only [takeMinWrites]; split_ifs <;> simp [height]
  | node _ [] => by simp [takeMinWrites]
  | node ks (c :: cs') => by
      have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
      have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
        simp only [Spot.children, List.nil_append]
      rw [h2] at h1
      have := takeMinWrites_le deg (ensureSpare deg ⟨[], [], c, ks, cs'⟩).target
      have := spareWrites_le deg (⟨[], [], c, ks, cs'⟩ : Spot α)
      rw [takeMinWrites]
      simp only [height_node]
      omega
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The writes `delRec` makes, branch for branch with `delRec` and `delRecCost`: a fix-up's writes
and the child's on a descent; the node rewritten with a predecessor or successor, plus that walk;
the node and the merged child, plus the merged child's deletion; one for the leaf the key leaves. -/
def delRecWrites (deg : ℕ) (a : α) : Node α → ℕ
  | leaf ks => if a ∈ ks then 1 else 0
  | node ks cs =>
      match _hkr : ks.drop (slot a ks), _hcr : cs.drop (slot a ks) with
      | k :: kr, c :: r :: rest =>
          if a < k then
            spareWrites deg ⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩
              + delRecWrites deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                                    k :: kr, r :: rest⟩).target
          else if hasSpare deg c then takeMaxWrites deg c + 1
          else if hasSpare deg r then takeMinWrites deg r + 1
          else delRecWrites deg a (mergeNodes c k r) + 2
      | [], [c] =>
          spareWrites deg ⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩
            + delRecWrites deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                                  [], []⟩).target
      | _, _ => 0
  termination_by t => t.height
  decreasing_by
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega
    · have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      simp only [height_node]
      omega
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega

/-- **A deletion writes at most `3h + 1` blocks**: at most three per level (a borrow), and one
for the leaf the key, or its predecessor or successor, is taken from. -/
theorem delRecWrites_le (deg : ℕ) (a : α) :
    ∀ t : Node α, delRecWrites deg a t ≤ 3 * t.height + 1 := by
  intro t
  induction t using delRecCost.induct (deg := deg) (a := a) with
  | case1 ks => simp only [delRecWrites]; split_ifs <;> simp [height]
  | case2 ks cs k kr c r rest hkr hcr hlt ih =>
      have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← hcr, List.take_append_drop]
      rw [h2] at h1
      have hs := spareWrites_le deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      rw [delRecWrites]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hlt, ↓reduceIte, height_node]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case3 ks cs k kr c r rest hkr hcr hnlt hsc =>
      have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := takeMaxWrites_le deg c
      rw [delRecWrites]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hnlt, hsc, ↓reduceIte, height_node]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case4 ks cs k kr c r rest hkr hcr hnlt hnsc hsr =>
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hr
      have h2 := takeMinWrites_le deg r
      rw [delRecWrites]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hnlt, hnsc, hsr, ↓reduceIte, height_node, Bool.false_eq_true]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case5 ks cs k kr c r rest hkr hcr hnlt hnsc hnsr ih =>
      have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      rw [delRecWrites]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hnlt, hnsc, hnsr, ↓reduceIte, height_node, Bool.false_eq_true]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case6 ks cs c hkr hcr ih =>
      have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← hcr, List.take_append_drop]
      rw [h2] at h1
      have hs := spareWrites_le deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      rw [delRecWrites]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i c1 e1 e2
        rw [hcr] at e2
        simp only [List.cons.injEq, and_true] at e2
        obtain rfl := e2
        simp only [height_node]
        omega
      · rename_i e1 e2
        exact (e2 c hkr hcr).elim
  | case7 ks cs h1 h2 =>
      rw [delRecWrites]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        exact (h1 k1 kr1 c1 r1 rest1 e1 e2).elim
      · rename_i c1 e1 e2
        exact (h2 c1 e1 e2).elim
      · simp

/-- The sibling blocks `ensureSpare` reads: none when the target already has a spare key,
otherwise the left sibling, and the right one too when the left cannot spare a key. -/
def spareReads (deg : ℕ) (sp : Spot α) : ℕ :=
  if hasSpare deg sp.target then 0
  else
    match sp.childrenL.getLast? with
    | some l =>
        if hasSpare deg l then 1
        else
          match sp.childrenR with
          | _ :: _ => 2
          | [] => 1
    | none =>
        match sp.childrenR with
        | _ :: _ => 1
        | [] => 0

omit [LinearOrder α] in
theorem spareReads_le (deg : ℕ) (sp : Spot α) : spareReads deg sp ≤ 2 := by
  unfold spareReads
  repeat' split
  all_goals omega

/-- The sibling blocks `takeMax`'s fix-ups read on the way down, beyond the nodes it enters. -/
def takeMaxSibReads (deg : ℕ) : Node α → ℕ
  | leaf _ => 0
  | node ks cs =>
      match _hc : cs.getLast? with
      | none => 0
      | some c =>
          spareReads deg ⟨ks, cs.dropLast, c, [], []⟩
            + takeMaxSibReads deg (ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩).target
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast _hc
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The mirror, for the walk to the leftmost leaf. -/
def takeMinSibReads (deg : ℕ) : Node α → ℕ
  | leaf _ => 0
  | node _ [] => 0
  | node ks (c :: cs') =>
      spareReads deg ⟨[], [], c, ks, cs'⟩
        + takeMinSibReads deg (ensureSpare deg ⟨[], [], c, ks, cs'⟩).target
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

omit [LinearOrder α] in
theorem takeMaxSibReads_le (deg : ℕ) : ∀ t : Node α, takeMaxSibReads deg t ≤ 2 * t.height
  | leaf _ => by simp [takeMaxSibReads]
  | node ks cs => by
      have ih : ∀ c : Node α, cs.getLast? = some c →
          takeMaxSibReads deg (ensureSpare deg ⟨ks, cs.dropLast, c, [], []⟩).target
            ≤ 2 * (ensureSpare deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)).target.height := by
        intro c hc
        exact takeMaxSibReads_le deg _
      rw [takeMaxSibReads]
      split
      · simp
      · rename_i c hc
        have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
        have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
          simp only [Spot.children]
          exact dropLast_append_getLast hc
        rw [h2] at h1
        have := ih c hc
        have := spareReads_le deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
        simp only [height_node]
        omega
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨ks, cs.dropLast, c, [], []⟩ : Spot α)
    have h2 : (⟨ks, cs.dropLast, c, [], []⟩ : Spot α).children = cs := by
      simp only [Spot.children]
      exact dropLast_append_getLast hc
    rw [h2] at h1
    simp only [height_node]
    omega

omit [LinearOrder α] in
theorem takeMinSibReads_le (deg : ℕ) : ∀ t : Node α, takeMinSibReads deg t ≤ 2 * t.height
  | leaf _ => by simp [takeMinSibReads]
  | node _ [] => by simp [takeMinSibReads]
  | node ks (c :: cs') => by
      have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
      have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
        simp only [Spot.children, List.nil_append]
      rw [h2] at h1
      have := takeMinSibReads_le deg (ensureSpare deg ⟨[], [], c, ks, cs'⟩).target
      have := spareReads_le deg (⟨[], [], c, ks, cs'⟩ : Spot α)
      rw [takeMinSibReads]
      simp only [height_node]
      omega
  termination_by t => t.height
  decreasing_by
    have h1 := ensureSpare_target_height deg (⟨[], [], c, ks, cs'⟩ : Spot α)
    have h2 : (⟨[], [], c, ks, cs'⟩ : Spot α).children = c :: cs' := by
      simp only [Spot.children, List.nil_append]
    rw [h2] at h1
    simp only [height_node]
    omega

/-- The blocks `delRec` reads beyond the nodes it enters (`delRecCost`): the siblings each fix-up
inspects, the left child `c` a successor branch inspects before walking the right one, and, in the
merge branch, the second of the two children merged (the merged node is entered once). -/
def delRecSibReads (deg : ℕ) (a : α) : Node α → ℕ
  | leaf _ => 0
  | node ks cs =>
      match _hkr : ks.drop (slot a ks), _hcr : cs.drop (slot a ks) with
      | k :: kr, c :: r :: rest =>
          if a < k then
            spareReads deg ⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩
              + delRecSibReads deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                                    k :: kr, r :: rest⟩).target
          else if hasSpare deg c then takeMaxSibReads deg c
          else if hasSpare deg r then takeMinSibReads deg r + 1
          else delRecSibReads deg a (mergeNodes c k r) + 1
      | [], [c] =>
          spareReads deg ⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩
            + delRecSibReads deg a (ensureSpare deg ⟨ks.take (slot a ks), cs.take (slot a ks), c,
                                                  [], []⟩).target
      | _, _ => 0
  termination_by t => t.height
  decreasing_by
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega
    · have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, _hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      simp only [height_node]
      omega
    · have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← _hcr, List.take_append_drop]
      rw [h2] at h1
      simp only [height_node]
      omega

/-- **At most two extra reads per level**: a fix-up inspects at most both siblings. -/
theorem delRecSibReads_le (deg : ℕ) (a : α) :
    ∀ t : Node α, delRecSibReads deg a t ≤ 2 * t.height := by
  intro t
  induction t using delRecCost.induct (deg := deg) (a := a) with
  | case1 ks => simp [delRecSibReads]
  | case2 ks cs k kr c r rest hkr hcr hlt ih =>
      have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ :
          Spot α).children = cs := by
        simp only [Spot.children, ← hcr, List.take_append_drop]
      rw [h2] at h1
      have hs := spareReads_le deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, k :: kr, r :: rest⟩ : Spot α)
      rw [delRecSibReads]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hlt, ↓reduceIte, height_node]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case3 ks cs k kr c r rest hkr hcr hnlt hsc =>
      have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := takeMaxSibReads_le deg c
      rw [delRecSibReads]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hnlt, hsc, ↓reduceIte, height_node]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case4 ks cs k kr c r rest hkr hcr hnlt hnsc hsr =>
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hr
      have h2 := takeMinSibReads_le deg r
      rw [delRecSibReads]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hnlt, hnsc, hsr, ↓reduceIte, height_node, Bool.false_eq_true]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case5 ks cs k kr c r rest hkr hcr hnlt hnsc hnsr ih =>
      have hc : c ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have hr : r ∈ cs := by rw [← List.take_append_drop (slot a ks) cs, hcr]; simp
      have h1 := height_le_childrenHeight_of_mem hc
      have h2 := height_le_childrenHeight_of_mem hr
      have h3 := mergeNodes_height c k r
      rw [delRecSibReads]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        rw [hcr] at e2
        simp only [List.cons.injEq] at e1 e2
        obtain ⟨rfl, rfl⟩ := e1
        obtain ⟨rfl, rfl, rfl⟩ := e2
        simp only [hnlt, hnsc, hnsr, ↓reduceIte, height_node, Bool.false_eq_true]
        omega
      · rename_i c1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i e1 e2
        exact (e1 k kr c r rest hkr hcr).elim
  | case6 ks cs c hkr hcr ih =>
      have h1 := ensureSpare_target_height deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      have h2 : (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α).children = cs := by
        simp only [Spot.children, ← hcr, List.take_append_drop]
      rw [h2] at h1
      have hs := spareReads_le deg
        (⟨ks.take (slot a ks), cs.take (slot a ks), c, [], []⟩ : Spot α)
      rw [delRecSibReads]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        rw [hkr] at e1
        simp at e1
      · rename_i c1 e1 e2
        rw [hcr] at e2
        simp only [List.cons.injEq, and_true] at e2
        obtain rfl := e2
        simp only [height_node]
        omega
      · rename_i e1 e2
        exact (e2 c hkr hcr).elim
  | case7 ks cs h1 h2 =>
      rw [delRecSibReads]
      split
      · rename_i k1 kr1 c1 r1 rest1 e1 e2
        exact (h1 k1 kr1 c1 r1 rest1 e1 e2).elim
      · rename_i c1 e1 e2
        exact (h2 c1 e1 e2).elim
      · simp

/-- `delete` with the pair cost. Reads: the nodes entered (`delRecCost`) plus the sibling blocks
inspected (`delRecSibReads`). Writes: `delRecWrites`; the root collapse frees a block and writes
none. -/
def deleteIO (deg : ℕ) (a : α) (t : Node α) : TimeM (ℕ × ℕ) (Node α × Bool) :=
  ⟨delete deg a t, (delRecCost deg a t + delRecSibReads deg a t, delRecWrites deg a t)⟩

theorem ret_deleteIO (deg : ℕ) (a : α) (t : Node α) :
    (deleteIO deg a t).ret = delete deg a t := rfl

/-- The read component is `deleteM`'s count of nodes entered plus the siblings inspected. -/
theorem reads_deleteIO (deg : ℕ) (a : α) (t : Node α) :
    (deleteIO deg a t).time.1 = (deleteM deg a t).time + delRecSibReads deg a t := rfl

/-- **Deletion, in `h`**: at most `3h + 2` reads (`h + 2` nodes entered, root included, and two
siblings per level) and `3h + 1` writes. -/
theorem deleteIO_le (deg : ℕ) (a : α) (t : Node α) :
    (deleteIO deg a t).time.1 ≤ 3 * t.height + 2 ∧
      (deleteIO deg a t).time.2 ≤ 3 * t.height + 1 := by
  have h1 := delRecCost_le deg a t
  have h2 := delRecSibReads_le deg a t
  have h3 := delRecWrites_le deg a t
  simp only [deleteIO]
  omega

/-- **Deletion, in `n` and `deg`**: at most `3 · log_deg((n+1)/2) + 2` reads (root included) and
`3 · log_deg((n+1)/2) + 1` writes. -/
theorem deleteIO_le_log {deg : ℕ} {bt : Node α} (hv : RootLegal deg bt) (hsz : 1 ≤ bt.size)
    (a : α) : (deleteIO deg a bt).time.1 ≤ 3 * Nat.log deg ((bt.size + 1) / 2) + 2
      ∧ (deleteIO deg a bt).time.2 ≤ 3 * Nat.log deg ((bt.size + 1) / 2) + 1 := by
  have hdeg : 2 ≤ deg := hv.2.2.2
  have hstruct : 2 * deg ^ bt.height ≤ bt.size + 1 := two_mul_pow_height_le_size_succ hv hsz
  have hdiv : deg ^ bt.height ≤ (bt.size + 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hlog : bt.height ≤ Nat.log deg ((bt.size + 1) / 2) :=
    Nat.le_log_of_pow_le (by omega) hdiv
  have := deleteIO_le deg a bt
  omega

end BTree.Node

end AlgoDesign.Searching
