/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.Scan

/-!
# LSH: the re-rank, with buckets computed on the fly

A table is its hash function. A query's candidates are the stored points that share its key in
some table, and the answer is the nearest of them, measured exactly. The theorems hold for
**any** hash family:
- the answer is a candidate (`lshQuery_mem`) at least as close as every candidate
  (`lshQuery_le_candidates`);
- **if the scan's answer is a candidate, LSH returns exactly it**, the tie rule included
  (`lshQuery_eq_scanNearest`), and at the true minimum distance (`lshQuery_exact_of_collision`).

This form hashes every stored point at query time. The index the library keeps stores its
buckets instead (`LSH.Index`, `Spec.lean`); `LSH.nearest_eq_lshQuery` (`Query.lean`) shows that,
on a valid index, reading the stored buckets gives this answer.
-/

@[expose] public section

namespace AlgoDesign.Geometry.LSH

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

/-- Indices of stored points that share `q`'s key in at least one table. A table is its hash
function: `simKey rs` for SimHash, `pStableKey`s for p-stable LSH, or any other family. -/
def candidates (tables : List (Point d α → κ)) (pts : List (Point d α)) (q : Point d α) :
    List ℕ :=
  (List.range pts.length).filter fun i => tables.any fun h => decide (h pts[i]! = h q)

/-- Re-rank the candidates exactly, with the scan's tie rule. Returns the id of a point of `pts`. -/
def lshQuery (tables : List (Point d α → κ)) (pts : List (Point d α)) (q : Point d α) : Option ℕ :=
  let cs := candidates tables pts q
  (scanNearest (cs.map (pts[·]!)) q).map (cs[·]!)

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem lt_of_mem_candidates {tables : List (Point d α → κ)} {pts : List (Point d α)}
    {q : Point d α} {j : ℕ} (hj : j ∈ candidates tables pts q) : j < pts.length := by
  unfold candidates at hj
  exact List.mem_range.mp (List.mem_of_mem_filter hj)

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- Reading the re-ranked list at position `k` reads `pts` at the `k`-th candidate. -/
theorem map_getElem!_eq {cs : List ℕ} {pts : List (Point d α)} {k : ℕ} (hk : k < cs.length) :
    (cs.map (pts[·]!))[k]! = pts[cs[k]!]! := by
  simp [hk]

omit [IsStrictOrderedRing α] in
/-- The answer is itself a candidate. -/
theorem lshQuery_mem {tables : List (Point d α → κ)} {pts : List (Point d α)} {q : Point d α}
    {i : ℕ} (h : lshQuery tables pts q = some i) : i ∈ candidates tables pts q := by
  unfold lshQuery at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  have hlt : k < (candidates tables pts q).length := by
    simpa using scanNearest_mem hk
  simp [hlt]

omit [IsStrictOrderedRing α] in
/-- The answer is at least as close as every candidate. -/
theorem lshQuery_le_candidates {tables : List (Point d α → κ)} {pts : List (Point d α)}
    {q : Point d α} {i : ℕ} (h : lshQuery tables pts q = some i)
    (j : ℕ) (hj : j ∈ candidates tables pts q) : sqDist pts[i]! q ≤ sqDist pts[j]! q := by
  unfold lshQuery at h
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hj
  have hlt : k < (candidates tables pts q).length := by
    simpa using scanNearest_mem hk
  have hle := scanNearest_le hk m (by simpa using hm)
  rw [map_getElem!_eq hlt, map_getElem!_eq hm] at hle
  simpa [hm] using hle

omit [IsStrictOrderedRing α] in
/-- **Exact on a collision.** If a true nearest neighbor is among the candidates, LSH returns a
point at the true minimum distance. -/
theorem lshQuery_exact_of_collision {tables : List (Point d α → κ)} {pts : List (Point d α)}
    {q : Point d α} {i n : ℕ} (hn : scanNearest pts q = some n) (hc : n ∈ candidates tables pts q)
    (h : lshQuery tables pts q = some i) : sqDist pts[i]! q = sqDist pts[n]! q :=
  le_antisymm (lshQuery_le_candidates h n hc)
    (scanNearest_le hn i (lt_of_mem_candidates (lshQuery_mem h)))

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem candidates_sorted (tables : List (Point d α → κ)) (pts : List (Point d α)) (q : Point d α) :
    (candidates tables pts q).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

omit [IsStrictOrderedRing α] in
/-- **Exact on a collision, and the same answer as the scan.** If the scan's answer is among the
candidates, LSH returns exactly it, the tie rule included. -/
theorem lshQuery_eq_scanNearest {tables : List (Point d α → κ)} {pts : List (Point d α)}
    {q : Point d α} {n : ℕ} (hn : scanNearest pts q = some n) (hc : n ∈ candidates tables pts q) :
    lshQuery tables pts q = some n := by
  have hsorted := candidates_sorted tables pts q
  have hne : (candidates tables pts q).map (pts[·]!) ≠ [] := by
    simpa using List.ne_nil_of_mem hc
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp ((scanNearest_isSome_iff _ q).mpr hne)
  have hkl : k < (candidates tables pts q).length := by simpa using scanNearest_mem hk
  have hlq : lshQuery tables pts q = some (candidates tables pts q)[k] := by
    unfold lshQuery
    dsimp only
    rw [hk, Option.map_some, getElem!_pos _ k hkl]
  rw [hlq]
  congr 1
  obtain ⟨m, hm, hmn⟩ := List.mem_iff_getElem.mp hc
  have h1 := lshQuery_le_candidates hlq n hc
  have h2 := scanNearest_le hn _ (lt_of_mem_candidates (List.getElem_mem hkl))
  rcases lt_trichotomy (candidates tables pts q)[k] n with h | h | h
  · exact absurd (scanNearest_lowest hn _ h) (not_lt.mpr h1)
  · exact h
  · have hmk : m < k := by
      rcases lt_trichotomy m k with hmk | rfl | hkm
      · exact hmk
      · exact absurd hmn (ne_of_gt h)
      · exact absurd (hmn ▸ List.pairwise_iff_getElem.mp hsorted k m hkl hm hkm) (not_lt.mpr h.le)
    have hlow := scanNearest_lowest hk m (by simpa using hmk)
    rw [map_getElem!_eq hkl, map_getElem!_eq hm] at hlow
    simp only [getElem!_pos (candidates tables pts q) k hkl,
      getElem!_pos (candidates tables pts q) m hm, hmn] at hlow
    exact absurd hlow (not_lt.mpr h2)

end AlgoDesign.Geometry.LSH
