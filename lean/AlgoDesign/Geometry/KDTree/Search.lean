/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.KDTree.Prune
public import AlgoDesign.Geometry.Scan
public import Mathlib.Data.List.Sort

/-!
# Best-first search: nothing closer is skipped

Samet §4.1 (`INCNEAREST`), the book's procedure, which queues both children of every inner
node, as the Python's `KDTree.k_nearest_with_stats` runs it. The Rust's
`KdTree::k_nearest_with_stats` instead walks down the nearer sides to a leaf and queues the
farther ones (Arya et al. 1998). It opens regions of the same bounds and measures the same points,
and a separate check compares it with this file's `search`, the points measured and the final
queue as multisets.

Regions wait in a queue, each with per-axis **offsets**: how far the query is from the region along
each axis. A region's lower bound is the sum of its squared offsets. The search takes the region
with the least bound (the first queued on a tie); a leaf measures its point; an inner node queues
its far child, with the offset on the cut's axis replaced by `split - q[axis]`, and then its near
child, with the parent's offsets. The search stops when the least bound is **strictly** greater than
the `k`-th best distance measured, so a point tied with the `k`-th best is still measured. Asked for
no neighbors (`k = 0`), the search opens nothing, as the Rust and the Python answer nothing.

Box invariant 3 is `NothingCloserSkipped` (stated in `Spec.lean` on a `Run`: the tree, the query
and the search's state; the three pieces not in the box are stated here): every stored point is
already measured, or sits in a queued region whose bound is at most its squared distance to the
query. Two of those pieces give it on their own
(`nothingCloserSkipped_of_offsetsBound_eachPointOnce`). `valid_start` and `valid_visit` show the
search keeps it, whichever region it opens; `answer` reads it on stopping: every stored point left
unmeasured is strictly farther than the `k`-th best. `stopped_run` shows the loop stops within
`size t` steps. For one neighbor, `nearest_answer` and `search_nearest` give the scan's answer,
the squared distance of `Scan.lean`'s `scanNearest`; for `k`, `kNearest_eq_scan` and
`search_kNearest_eq_scan`: the `k` least distances measured are the `k` least of all stored
points, so no stored point outside the result is strictly closer than its `k`-th member. Three
further pieces ride along in `Valid`, because the far child's new bound needs them:
`QueuedCutsSeparate`, `OffsetsBound` and `EachPointOnce`.

The Lean leaf holds one point, so this is the search on the tree built with a bucket of 1, and it
measures points, not ids: the tie rule of the Rust and the Python, by the lowest id, is outside this
model, and `answer` is what that rule rests on (every point tied with the `k`-th best is measured).
The search keeps every measured point where the Rust keeps only the best `k`; the result is the
first `k` of them by distance.

The queries the contract names close the file: `KDTree.kNearest` and `KDTree.nearest`, the first
`k` (or one) of the measured points by distance, with `KDTree.kNearest_spec`; and `head?_dists`,
which reads the first of the scan's ranking `dists` as the distance of the point `scanNearest`
picks.
-/

@[expose] public section

namespace AlgoDesign.Geometry.KDTree.BestFirst

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-- Not in the box: every queued region's cuts separate its points. -/
def QueuedCutsSeparate (r : Run d α) : Prop :=
  ∀ g ∈ r.state.queue, CutsSeparate g.tree

/-- Not in the box: every queued region's offsets are at most each of its points' distances
from the query, axis by axis. -/
def OffsetsBound (r : Run d α) : Prop :=
  ∀ g ∈ r.state.queue, ∀ x ∈ points g.tree, ∀ i, g.offsets i ^ 2 ≤ (x i - r.query i) ^ 2

/-- Not in the box: the measured points and the queued regions' points are the stored points,
each once. -/
def EachPointOnce (r : Run d α) : Prop :=
  (r.state.measured ++ r.state.queue.flatMap (fun g => points g.tree)).Perm (points r.tree)

/-- **The search's invariant**, on a run: box invariant 3, then the three pieces not in the
box. -/
def Valid (r : Run d α) : Prop :=
  NothingCloserSkipped r ∧ QueuedCutsSeparate r ∧ OffsetsBound r ∧ EachPointOnce r

/-- The search starts with nothing measured and the whole tree queued, at offsets zero. -/
def start (t : KDTree d α) : State d α := ⟨[], [⟨0, t⟩]⟩

/-- Take a region with the least bound out of the queue, the first queued on a tie. -/
def popLeast : List (Region d α) → Option (Region d α × List (Region d α))
  | [] => none
  | r :: rs =>
    match popLeast rs with
    | none => some (r, [])
    | some (m, rest) => if m.bound < r.bound then some (m, r :: rest) else some (r, rs)

/-- Open a region: a leaf gives its point to measure; an inner node gives its far child, the
offset on its axis replaced by `split - q[axis]`, and then its near child, at the same offsets. -/
def expand (q : Point d α) (r : Region d α) : List (Point d α) × List (Region d α) :=
  match r.tree with
  | .leaf p => ([p], [])
  | .node a s l rt =>
    if q a ≤ s then ([], [⟨Function.update r.offsets a (s - q a), rt⟩, ⟨r.offsets, l⟩])
    else ([], [⟨Function.update r.offsets a (s - q a), l⟩, ⟨r.offsets, rt⟩])

/-- One step, after `r` was taken out of the queue and `rest` is left: measure what `r` gives,
queue what it gives. -/
def visit (q : Point d α) (r : Region d α) (rest : List (Region d α)) (st : State d α) :
    State d α :=
  ⟨st.measured ++ (expand q r).1, rest ++ (expand q r).2⟩

/-- The `k`-th best squared distance measured so far (`k ≥ 1`), once `k` points are measured. -/
def kthBest (k : ℕ) (q : Point d α) (st : State d α) : Option α :=
  ((st.measured.map (sqDist · q)).insertionSort (· ≤ ·))[k - 1]?

/-- The search loop, with `fuel` steps at most: stop when the queue is empty, or when `k` points
are measured and the least bound is strictly greater than the `k`-th best. -/
def run (k : ℕ) (q : Point d α) : ℕ → State d α → State d α
  | 0, st => st
  | fuel + 1, st =>
    match popLeast st.queue with
    | none => st
    | some (r, rest) =>
      match kthBest k q st with
      | some w => if w < r.bound then st else run k q fuel (visit q r rest st)
      | none => run k q fuel (visit q r rest st)

/-- The number of nodes and leaves: no search opens more regions. -/
def size : KDTree d α → ℕ
  | .leaf _ => 1
  | .node _ _ l r => 1 + size l + size r

/-- Best-first search for the `k` nearest stored points to `q`. Asked for none (`k = 0`), it opens
nothing and measures nothing, as the Rust and the Python answer nothing. -/
def search (k : ℕ) (q : Point d α) (t : KDTree d α) : State d α :=
  if k = 0 then start t else run k q (size t) (start t)

/-- The search has stopped: the queue is empty, or `k` points are measured and every queued bound
is strictly greater than the `k`-th best. -/
def Stopped (k : ℕ) (q : Point d α) (st : State d α) : Prop :=
  st.queue = [] ∨ ∃ w, kthBest k q st = some w ∧ ∀ r ∈ st.queue, w < r.bound

instance (k : ℕ) (q : Point d α) (st : State d α) : Decidable (Stopped k q st) :=
  inferInstanceAs (Decidable
    (st.queue = [] ∨ ∃ w, kthBest k q st = some w ∧ ∀ r ∈ st.queue, w < r.bound))

/-! ### The queue -/

omit [IsStrictOrderedRing α] in
theorem popLeast_eq_none : ∀ {l : List (Region d α)}, popLeast l = none → l = []
  | [], _ => rfl
  | r :: rs, h => by
    simp only [popLeast] at h
    split at h
    · simp at h
    · split_ifs at h

omit [IsStrictOrderedRing α] in
theorem popLeast_perm : ∀ {l : List (Region d α)} {m : Region d α} {rest : List (Region d α)},
    popLeast l = some (m, rest) → (m :: rest).Perm l
  | [], _, _, h => by simp [popLeast] at h
  | r :: rs, m, rest, h => by
    simp only [popLeast] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rename_i hn
      rw [popLeast_eq_none hn]
    · rename_i m' rest' hs
      have ih := popLeast_perm hs
      split_ifs at h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact (List.Perm.swap _ _ _).trans (ih.cons r)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact List.Perm.refl _

omit [IsStrictOrderedRing α] in
theorem popLeast_le : ∀ {l : List (Region d α)} {m : Region d α} {rest : List (Region d α)},
    popLeast l = some (m, rest) → ∀ x ∈ l, m.bound ≤ x.bound
  | [], _, _, h => by simp [popLeast] at h
  | r :: rs, m, rest, h => by
    simp only [popLeast] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      rename_i hn
      simp [popLeast_eq_none hn]
    · rename_i m' rest' hs
      have ih := popLeast_le hs
      split_ifs at h with hlt
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hlt.le
        · exact ih x hx
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_rfl
        · exact (not_lt.1 hlt).trans (ih x hx)

/-! ### The bound -/

/-- A region's bound is at most the squared distance of a point its offsets bound. -/
theorem bound_le {r : Region d α} {x q : Point d α} (h : ∀ i, r.offsets i ^ 2 ≤ (x i - q i) ^ 2) :
    r.bound ≤ sqDist x q :=
  Finset.sum_le_sum fun i _ => h i

/-- On the far side of a cut, the new offset bounds the point on the cut's axis. -/
theorem far_offset_le {q x : Point d α} {a : Fin d} {s : α}
    (h : (q a ≤ s ∧ s ≤ x a) ∨ (s < q a ∧ x a ≤ s)) : (s - q a) ^ 2 ≤ (x a - q a) ^ 2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> nlinarith

/-- **Box invariant 3 from two pieces not in the box.** A run whose queued regions'
offsets bound their points (`OffsetsBound`) and that holds every stored point once, measured or
queued (`EachPointOnce`), skips nothing closer (`NothingCloserSkipped`). -/
theorem nothingCloserSkipped_of_offsetsBound_eachPointOnce {r : Run d α} (ho : OffsetsBound r)
    (he : EachPointOnce r) : NothingCloserSkipped r := by
  intro x hx
  rcases List.mem_append.1 (he.mem_iff.2 hx) with hm | hq
  · exact Or.inl hm
  · obtain ⟨g, hg, hxg⟩ := List.mem_flatMap.1 hq
    exact Or.inr ⟨g, hg, hxg, bound_le (ho g hg x hxg)⟩

/-! ### Box invariant 3 is kept -/

theorem valid_start {t : KDTree d α} (h : CutsSeparate t) (q : Point d α) :
    Valid ⟨t, q, start t⟩ := by
  have h0 : ∀ x : Point d α, ∀ i, (0 : Point d α) i ^ 2 ≤ (x i - q i) ^ 2 := fun x i => by
    simp only [Pi.zero_apply]; nlinarith [sq_nonneg (x i - q i)]
  refine ⟨fun x hx => Or.inr ⟨(⟨0, t⟩ : Region d α), by simp [start], hx, bound_le (h0 x)⟩,
    ?_, ?_, ?_⟩
  · intro r hr
    simp only [start, List.mem_singleton] at hr
    subst hr
    exact h
  · intro r hr
    simp only [start, List.mem_singleton] at hr
    subst hr
    exact fun x _ => h0 x
  · simp [start, EachPointOnce]

/-- Opening a region hands on its points, each once: measured, or in a child region whose cuts
separate and whose offsets bound its points. -/
theorem expand_spec (q : Point d α) {r : Region d α} (hcs : CutsSeparate r.tree)
    (hoff : ∀ x ∈ points r.tree, ∀ i, r.offsets i ^ 2 ≤ (x i - q i) ^ 2) :
    ((expand q r).1 ++ (expand q r).2.flatMap (fun c => points c.tree)).Perm (points r.tree) ∧
      ∀ c ∈ (expand q r).2,
        CutsSeparate c.tree ∧ ∀ x ∈ points c.tree, ∀ i, c.offsets i ^ 2 ≤ (x i - q i) ^ 2 := by
  obtain ⟨off, tree⟩ := r
  cases tree with
  | leaf p => simp [expand, points]
  | node a s l rt =>
    obtain ⟨hl, hr, hcl, hcr⟩ := hcs
    simp only [points, List.mem_append] at hoff
    have upd : ∀ x : Point d α, (s - q a) ^ 2 ≤ (x a - q a) ^ 2 →
        (∀ i, off i ^ 2 ≤ (x i - q i) ^ 2) →
        ∀ i, Function.update off a (s - q a) i ^ 2 ≤ (x i - q i) ^ 2 := by
      intro x ha ho i
      by_cases hi : i = a
      · subst hi; simpa using ha
      · simpa [Function.update_of_ne hi] using ho i
    by_cases hq : q a ≤ s
    · simp only [expand, hq, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append, points]
      refine ⟨List.perm_append_comm, ?_⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨hcr, fun x hx => upd x (far_offset_le (Or.inl ⟨hq, hr x hx⟩))
          (hoff x (Or.inr hx))⟩
      · exact ⟨hcl, fun x hx => hoff x (Or.inl hx)⟩
    · simp only [expand, hq, ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.nil_append, points]
      refine ⟨List.Perm.refl _, ?_⟩
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨hcl, fun x hx => upd x (far_offset_le (Or.inr ⟨not_le.1 hq, hl x hx⟩))
          (hoff x (Or.inl hx))⟩
      · exact ⟨hcr, fun x hx => hoff x (Or.inr hx)⟩

/-- **One step keeps it**, whichever queued region `r` the step opens. -/
theorem valid_visit {t : KDTree d α} {q : Point d α} {st : State d α} {r : Region d α}
    {rest : List (Region d α)} (hv : Valid ⟨t, q, st⟩) (hp : (r :: rest).Perm st.queue) :
    Valid ⟨t, q, visit q r rest st⟩ := by
  obtain ⟨hn, hc, ho, he⟩ := hv
  have hmem : ∀ c, c ∈ st.queue ↔ c = r ∨ c ∈ rest := fun c => by
    rw [← hp.mem_iff, List.mem_cons]
  obtain ⟨hperm, hkids⟩ :=
    expand_spec q (hc r ((hmem r).2 (Or.inl rfl))) (ho r ((hmem r).2 (Or.inl rfl)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases hn x hx with hm | ⟨c, hc, hxc, hb⟩
    · exact Or.inl (List.mem_append_left _ hm)
    rcases (hmem c).1 hc with rfl | hc
    · have := hperm.mem_iff.2 hxc
      rcases List.mem_append.1 this with h1 | h2
      · exact Or.inl (List.mem_append_right _ h1)
      · obtain ⟨c', hc', hxc'⟩ := List.mem_flatMap.1 h2
        exact Or.inr ⟨c', List.mem_append_right _ hc', hxc', bound_le ((hkids c' hc').2 x hxc')⟩
    · exact Or.inr ⟨c, List.mem_append_left _ hc, hxc, hb⟩
  · intro c hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · exact hc c ((hmem c).2 (Or.inr hc'))
    · exact (hkids c hc').1
  · intro c hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · exact ho c ((hmem c).2 (Or.inr hc'))
    · exact (hkids c hc').2
  · have hq := hp.flatMap_right (fun c => points c.tree)
    simp only [EachPointOnce, visit, List.flatMap_append, List.flatMap_cons] at he hq ⊢
    rw [← Multiset.coe_eq_coe] at he hq hperm ⊢
    simp only [← Multiset.coe_add] at he hq hperm ⊢
    rw [← he, ← hq, ← hperm]
    ac_rfl

theorem valid_run {t : KDTree d α} {q : Point d α} (k : ℕ) :
    ∀ (fuel : ℕ) {st : State d α}, Valid ⟨t, q, st⟩ → Valid ⟨t, q, run k q fuel st⟩
  | 0, _, hv => hv
  | fuel + 1, st, hv => by
    simp only [run]
    split
    · exact hv
    · rename_i r rest hpop
      have hv' := valid_visit hv (popLeast_perm hpop)
      split
      · split_ifs
        · exact hv
        · exact valid_run k fuel hv'
      · exact valid_run k fuel hv'

/-- How much is left to open: the sizes of the queued regions' subtrees. -/
def left (st : State d α) : ℕ := (st.queue.map (fun r => size r.tree)).sum

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
theorem size_pos (t : KDTree d α) : 0 < size t := by
  cases t <;> simp [size]

omit [IsStrictOrderedRing α] in
theorem left_visit (q : Point d α) {st : State d α} {r : Region d α} {rest : List (Region d α)}
    (hp : (r :: rest).Perm st.queue) : left (visit q r rest st) + 1 = left st := by
  have hs := (hp.map (fun r => size r.tree)).sum_eq
  simp only [left, visit, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at hs ⊢
  rw [← hs]
  obtain ⟨off, tree⟩ := r
  cases tree with
  | leaf p => simp [expand, size]; omega
  | node a s l rt =>
    by_cases hq : q a ≤ s <;> simp [expand, hq, size] <;> omega

omit [IsStrictOrderedRing α] in
/-- **The search stops** within as many steps as there is left to open. -/
theorem stopped_run {q : Point d α} (k : ℕ) :
    ∀ (fuel : ℕ) {st : State d α}, left st ≤ fuel → Stopped k q (run k q fuel st)
  | 0, st, h => by
    change Stopped k q st
    left
    cases hq : st.queue with
    | nil => rfl
    | cons r rs =>
      have := size_pos r.tree
      simp [left, hq] at h
      omega
  | fuel + 1, st, h => by
    simp only [run]
    split
    · rename_i hpop
      exact Or.inl (popLeast_eq_none hpop)
    · rename_i r rest hpop
      have hl := left_visit q (popLeast_perm hpop)
      split
      · rename_i w hw
        split_ifs with hlt
        · exact Or.inr ⟨w, hw, fun c hc => hlt.trans_le (popLeast_le hpop c hc)⟩
        · exact stopped_run k fuel (by omega)
      · exact stopped_run k fuel (by omega)

/-! ### The answer -/

omit [IsStrictOrderedRing α] in
/-- **The answer.** On stopping, every stored point left unmeasured is strictly farther than the
`k`-th best measured: so every point at most as far as the `k`-th best has been measured. -/
theorem answer {t : KDTree d α} {q : Point d α} {st : State d α} {k : ℕ} (hv : Valid ⟨t, q, st⟩)
    (hs : Stopped k q st) {x : Point d α} (hx : x ∈ points t) (hm : x ∉ st.measured) :
    ∃ w, kthBest k q st = some w ∧ w < sqDist x q := by
  rcases hv.1 x hx with h | ⟨r, hr, -, hb⟩
  · exact absurd h hm
  rcases hs with h | ⟨w, hw, hlt⟩
  · simp [h] at hr
  · exact ⟨w, hw, (hlt r hr).trans_le hb⟩

omit [IsStrictOrderedRing α] in
theorem measured_subperm {t : KDTree d α} {q : Point d α} {st : State d α} (hv : Valid ⟨t, q, st⟩) :
    st.measured.Subperm (points t) :=
  (List.sublist_append_left _ _).subperm.trans hv.2.2.2.subperm

omit [IsStrictOrderedRing α] in
theorem kthBest_mem {k : ℕ} {q : Point d α} {st : State d α} {w : α}
    (h : kthBest k q st = some w) : ∃ p ∈ st.measured, sqDist p q = w := by
  have := (List.perm_insertionSort _ _).mem_iff.1 (List.mem_of_getElem? h)
  simpa using this

omit [IsStrictOrderedRing α] in
theorem kthBest_one_le {q : Point d α} {st : State d α} {w : α} (h : kthBest 1 q st = some w) :
    ∀ p ∈ st.measured, w ≤ sqDist p q := by
  intro p hp
  have hs := List.pairwise_insertionSort (fun a b : α => a ≤ b) (st.measured.map (sqDist · q))
  have hm : sqDist p q ∈ (st.measured.map (sqDist · q)).insertionSort (· ≤ ·) :=
    (List.perm_insertionSort _ _).mem_iff.2 (List.mem_map_of_mem hp)
  unfold kthBest at h
  generalize (st.measured.map (sqDist · q)).insertionSort (· ≤ ·) = L at hs hm h
  cases L with
  | nil => simp at h
  | cons b L =>
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.1 hm with h | h
    · exact h.symm.le
    · exact List.rel_of_pairwise_cons hs h

omit [IsStrictOrderedRing α] in
theorem kthBest_one_isSome {q : Point d α} {st : State d α} (h : st.measured ≠ []) :
    ∃ w, kthBest 1 q st = some w := by
  unfold kthBest
  have hl := (List.perm_insertionSort (fun a b : α => a ≤ b)
    (st.measured.map (sqDist · q))).length_eq
  cases hL : (st.measured.map (sqDist · q)).insertionSort (· ≤ ·) with
  | nil =>
    rw [hL] at hl
    simp at hl
    exact absurd (List.length_eq_zero_iff.1 hl.symm) h
  | cons b L => exact ⟨b, rfl⟩

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
theorem points_ne_nil (t : KDTree d α) : points t ≠ [] := by
  induction t with
  | leaf p => simp [points]
  | node _ _ l r ihl _ => simp [points, ihl]

omit [IsStrictOrderedRing α] in
/-- **The nearest point.** On stopping with `k = 1`, the best measured is the least squared
distance of any stored point, and a stored point attains it. -/
theorem nearest_answer {t : KDTree d α} {q : Point d α} {st : State d α} (hv : Valid ⟨t, q, st⟩)
    (hs : Stopped 1 q st) :
    ∃ w, kthBest 1 q st = some w ∧ (∀ x ∈ points t, w ≤ sqDist x q) ∧
      ∃ p ∈ points t, sqDist p q = w := by
  obtain ⟨w, hw⟩ : ∃ w, kthBest 1 q st = some w := by
    rcases hs with h | ⟨w, hw, -⟩
    · apply kthBest_one_isSome
      intro hm
      have := hv.2.2.2
      simp only [EachPointOnce, hm, h, List.flatMap_nil, List.append_nil] at this
      exact points_ne_nil t (List.Perm.nil_eq this).symm
    · exact ⟨w, hw⟩
  refine ⟨w, hw, fun x hx => ?_, ?_⟩
  · by_cases hm : x ∈ st.measured
    · exact kthBest_one_le hw x hm
    · obtain ⟨w', hw', hlt⟩ := answer hv hs hx hm
      rw [hw] at hw'
      cases hw'
      exact hlt.le
  · obtain ⟨p, hp, rfl⟩ := kthBest_mem hw
    exact ⟨p, (measured_subperm hv).subset hp, rfl⟩

/-- The search keeps its invariant, from the start on, for every `k`. -/
theorem valid_search {t : KDTree d α} (h : CutsSeparate t) (k : ℕ) (q : Point d α) :
    Valid ⟨t, q, search k q t⟩ := by
  unfold search
  split_ifs
  · exact valid_start h q
  · exact valid_run k (size t) (valid_start h q)

omit [IsStrictOrderedRing α] in
/-- Asked for at least one neighbor, the search stops. -/
theorem stopped_search (k : ℕ) (q : Point d α) (t : KDTree d α) (hk : 0 < k) :
    Stopped k q (search k q t) := by
  simp only [search, Nat.pos_iff_ne_zero.1 hk, ↓reduceIte]
  exact stopped_run k (size t) (by simp [left, start])

/-- **The search answers as the scan does**: started on a tree whose cuts separate its points,
best-first search for one neighbor ends with the squared distance of `Scan.lean`'s `scanNearest`. -/
theorem search_nearest {t : KDTree d α} (h : CutsSeparate t) (q : Point d α) :
    ∃ w, kthBest 1 q (search 1 q t) = some w ∧ (∀ x ∈ points t, w ≤ sqDist x q) ∧
      ∀ i, scanNearest (points t) q = some i → sqDist (points t)[i]! q = w := by
  have hv := valid_search h 1 q
  have hs : Stopped 1 q (search 1 q t) := stopped_search 1 q t one_pos
  obtain ⟨w, hw, hle, p, hp, hpw⟩ := nearest_answer hv hs
  refine ⟨w, hw, hle, fun i hi => le_antisymm ?_ ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    have := scanNearest_le hi j hj
    rw [getElem!_pos (points t) j hj] at this
    exact hpw ▸ this
  · have hi' := scanNearest_mem hi
    rw [getElem!_pos (points t) i hi']
    exact hle _ (List.getElem_mem hi')

omit [IsStrictOrderedRing α] in
/-- **The `k` nearest.** On stopping, the measured points are stored points, each at most as often
as stored, and every stored point left unmeasured is strictly farther than the `k`-th best
measured. So the `k` best measured are `k` nearest stored points, and every point tied with the
`k`-th best is among the measured. -/
theorem kNearest_answer {t : KDTree d α} {q : Point d α} {st : State d α} {k : ℕ}
    (hv : Valid ⟨t, q, st⟩) (hs : Stopped k q st) :
    st.measured.Subperm (points t) ∧
      ∀ x ∈ points t, x ∉ st.measured → ∃ w, kthBest k q st = some w ∧ w < sqDist x q :=
  ⟨measured_subperm hv, fun _ hx hm => answer hv hs hx hm⟩

/-- `kNearest_answer` for the whole search, started on a tree whose cuts separate its points and
asked for at least one neighbor (for none, it measures nothing). -/
theorem search_kNearest {t : KDTree d α} (h : CutsSeparate t) (k : ℕ) (q : Point d α) (hk : 0 < k) :
    (search k q t).measured.Subperm (points t) ∧
      ∀ x ∈ points t, x ∉ (search k q t).measured →
        ∃ w, kthBest k q (search k q t) = some w ∧ w < sqDist x q :=
  kNearest_answer (valid_search h k q) (stopped_search k q t hk)

/-! ### The `k` nearest, as the scan ranks them -/

omit [CommRing α] [IsStrictOrderedRing α] in
/-- Two lists holding the same values, each once, sort to the same list. -/
theorem sort_eq_of_perm {A B : List α} (h : A.Perm B) :
    A.insertionSort (· ≤ ·) = B.insertionSort (· ≤ ·) :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)
    (((List.perm_insertionSort _ _).trans h).trans (List.perm_insertionSort _ _).symm)

omit [CommRing α] [IsStrictOrderedRing α] in
/-- Adding values strictly above the `k`-th of a sorted list leaves its first `k` in place. -/
theorem sort_take_of_above {A R : List α} {k : ℕ} {w : α} (hA : A.Pairwise (· ≤ ·)) (hk : 0 < k)
    (hw : A[k - 1]? = some w) (hR : ∀ b ∈ R, w < b) :
    ((A ++ R).insertionSort (· ≤ ·)).take k = A.take k := by
  obtain ⟨hkl, hwA⟩ := List.getElem?_eq_some_iff.1 hw
  have hrel : ∀ i j (hi : i < A.length) (hj : j < A.length), i ≤ j → A[i] ≤ A[j] := by
    intro i j hi hj hij
    rcases hij.lt_or_eq with h | rfl
    · exact List.pairwise_iff_getElem.1 hA i j hi hj h
    · exact le_rfl
  have hle : ∀ a ∈ A.take k, a ≤ w := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    rw [List.getElem_take, ← hwA]
    simp only [List.length_take] at hi
    exact hrel _ _ _ _ (by omega)
  have hge : ∀ b ∈ A.drop k ++ R, w ≤ b := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hb
      rw [List.getElem_drop, ← hwA]
      simp only [List.length_drop] at hi
      exact hrel _ _ _ _ (by omega)
    · exact (hR b hb).le
  have key : (A ++ R).insertionSort (· ≤ ·) =
      A.take k ++ (A.drop k ++ R).insertionSort (· ≤ ·) := by
    refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
      (List.pairwise_insertionSort _ _) ?_ ?_
    · refine List.pairwise_append.2 ⟨hA.sublist (List.take_sublist _ _),
        List.pairwise_insertionSort _ _, fun a ha b hb => (hle a ha).trans (hge b ?_)⟩
      exact (List.perm_insertionSort _ _).mem_iff.1 hb
    · refine (List.perm_insertionSort _ _).trans ?_
      have hs : A ++ R = A.take k ++ (A.drop k ++ R) := by
        rw [← List.append_assoc, List.take_append_drop]
      rw [hs]
      exact (List.perm_insertionSort _ _).symm.append_left _
  rw [key, List.take_left' (by simp; omega)]

/-- **The `k` nearest are the scan's.** On stopping, the `k` least squared distances measured are
the `k` least of all the stored points, in order: no stored point outside the result is strictly
closer than its `k`-th member. -/
theorem kNearest_eq_scan {t : KDTree d α} {q : Point d α} {st : State d α} {k : ℕ}
    (hv : Valid ⟨t, q, st⟩) (hs : Stopped k q st) :
    (dists q st.measured).take k = (dists q (points t)).take k := by
  obtain ⟨-, -, ho, he⟩ := hv
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rcases hs with hq | ⟨w, hw, hlt⟩
  · simp only [EachPointOnce, hq, List.flatMap_nil, List.append_nil] at he
    unfold dists
    rw [sort_eq_of_perm (he.map _)]
  · set R := (st.queue.flatMap (fun r => points r.tree)).map (sqDist · q)
    have hS : dists q (points t) = (dists q st.measured ++ R).insertionSort (· ≤ ·) := by
      unfold dists
      apply sort_eq_of_perm
      refine (he.map _).symm.trans ?_
      rw [List.map_append]
      exact (List.perm_insertionSort _ _).symm.append_right _
    rw [hS]
    refine (sort_take_of_above (A := dists q st.measured) (List.pairwise_insertionSort _ _) hk
      hw ?_).symm
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
    exact (hlt r hr).trans_le (bound_le (ho r hr x hxr))

/-- `kNearest_eq_scan` for the whole search, started on a tree whose cuts separate its points. -/
theorem search_kNearest_eq_scan {t : KDTree d α} (h : CutsSeparate t) (k : ℕ) (q : Point d α) :
    (dists q (search k q t).measured).take k = (dists q (points t)).take k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact kNearest_eq_scan (valid_search h k q) (stopped_search k q t hk)

end AlgoDesign.Geometry.KDTree.BestFirst

/-! ### The queries the contract names -/

namespace AlgoDesign.Geometry

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

omit [IsStrictOrderedRing α] in
/-- The first of the scan's ranking is the squared distance of the point `scanNearest` picks, and
there is none for no points: a bridge from `Nearest.Answers.nearest_scan` to `Scan.lean`'s answer
by id. -/
theorem head?_dists (q : Point d α) (pts : List (Point d α)) :
    (dists q pts).head? = (scanNearest pts q).bind fun i => pts[i]?.map (sqDist · q) := by
  have hperm := List.perm_insertionSort (fun a b : α => a ≤ b) (pts.map (sqDist · q))
  have hsort := List.pairwise_insertionSort (fun a b : α => a ≤ b) (pts.map (sqDist · q))
  unfold dists
  cases hn : scanNearest pts q with
  | none =>
    have : pts = [] := by
      by_contra hne
      have := (scanNearest_isSome_iff pts q).2 hne
      simp [hn] at this
    subst this
    simp
  | some i =>
    have hi := scanNearest_mem hn
    have hmem : sqDist pts[i] q ∈ (pts.map (sqDist · q)).insertionSort (· ≤ ·) :=
      hperm.mem_iff.2 (List.mem_map.2 ⟨pts[i], List.getElem_mem hi, rfl⟩)
    rw [Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some]
    generalize (pts.map (sqDist · q)).insertionSort (· ≤ ·) = L at hperm hsort hmem
    cases L with
    | nil => simp at hmem
    | cons b L =>
      simp only [List.head?_cons, Option.some.injEq]
      apply le_antisymm
      · rcases List.mem_cons.1 hmem with h | h
        · exact h.symm.le
        · exact List.rel_of_pairwise_cons hsort h
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 (List.mem_cons_self))
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        have := scanNearest_le hn j hj
        rwa [getElem!_pos pts i hi, getElem!_pos pts j hj] at this

namespace KDTree

/-- The `k` nearest stored points to `q`: best-first search's measured points, nearest first, the
first `k` of them. -/
def kNearest (k : ℕ) (q : Point d α) (t : KDTree d α) : List (Point d α) :=
  ((BestFirst.search k q t).measured.insertionSort (fun x y => sqDist x q ≤ sqDist y q)).take k

/-- The nearest stored point to `q`: the first of the `k` nearest for `k = 1`. -/
def nearest (q : Point d α) (t : KDTree d α) : Option (Point d α) := (kNearest 1 q t).head?

omit [IsStrictOrderedRing α] in
/-- Sorting points by distance, then reading the distances, ranks the distances. -/
theorem map_insertionSort_dist (q : Point d α) (l : List (Point d α)) :
    (l.insertionSort (fun x y => sqDist x q ≤ sqDist y q)).map (sqDist · q) = dists q l := by
  have : Std.Total (fun x y : Point d α => sqDist x q ≤ sqDist y q) :=
    ⟨fun x y => le_total _ _⟩
  have : IsTrans (Point d α) (fun x y => sqDist x q ≤ sqDist y q) := ⟨fun _ _ _ => le_trans⟩
  unfold dists
  refine List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) ?_
    (List.pairwise_insertionSort _ _) ?_
  · rw [List.pairwise_map]
    exact List.pairwise_insertionSort _ _
  · exact ((List.perm_insertionSort _ _).map _).trans (List.perm_insertionSort _ _).symm

/-- **The `k` nearest, as the scan ranks them**: on a tree whose cuts separate its points, holding
the points `ps` in some order, the `k` nearest answered have the `k` least squared distances of
`ps`, in order, and are points of `ps`, each at most as often as stored. -/
theorem kNearest_spec {t : KDTree d α} {ps : List (Point d α)} (h : CutsSeparate t)
    (hp : t.points.Perm ps) (k : ℕ) (q : Point d α) :
    (kNearest k q t).map (sqDist · q) = (dists q ps).take k ∧ (kNearest k q t).Subperm ps := by
  refine ⟨?_, ?_⟩
  · rw [kNearest, List.map_take, map_insertionSort_dist, BestFirst.search_kNearest_eq_scan h k q]
    unfold dists
    rw [BestFirst.sort_eq_of_perm (hp.map _)]
  · exact ((List.take_sublist _ _).subperm.trans (List.perm_insertionSort _ _).subperm).trans
      ((BestFirst.measured_subperm (BestFirst.valid_search h k q)).trans hp.subperm)

end KDTree

end AlgoDesign.Geometry
