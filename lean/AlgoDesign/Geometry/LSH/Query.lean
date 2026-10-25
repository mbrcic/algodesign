/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.LSH.Build
public import AlgoDesign.Geometry.LSH.Rerank

/-!
# LSH: the query, read from the stored buckets

`nearest` reads the candidates from the stored buckets (`Index.candidates`: one key and one bucket
per table) and returns the nearest of them, measured exactly, with the scan's tie rule; `kNearest`
returns the `k` nearest, ranked by a stable insertion sort, so ties keep the one stored first.

- `nearest_eq_lshQuery`: on a valid index, the stored-bucket query is the on-the-fly re-rank of
  `Rerank.lean`, so its theorems carry over; `nearest_eq_scanNearest` is
  `lshQuery_eq_scanNearest` on every valid index.
- `measuredExactly_nearest`, `measuredExactly_kNearest`: box invariant 2 for both queries;
  `nearestFirst_kNearest`: the `k` nearest come nearest first.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace LSH

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

/-- **The query**: the nearest candidate, measured exactly, the one stored first on ties. -/
def nearest (x : Index d α κ) (q : Point d α) : Option ℕ :=
  let cs := x.candidates q
  (scanNearest (cs.map (x.points[·]!)) q).map (cs[·]!)

/-- The `k` nearest candidates, nearest first, the one stored first on ties. -/
def kNearest (x : Index d α κ) (q : Point d α) (k : ℕ) : List ℕ :=
  ((x.candidates q).insertionSort fun a b => sqDist x.points[a]! q ≤ sqDist x.points[b]! q).take k

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- On a valid index, a stored id is in a table's bucket for `key` exactly when it names a
stored point with that key. -/
theorem mem_bucketOf_iff {x : Index d α κ} (hv : Valid x) {t : Table d α κ} (ht : t ∈ x.tables)
    (key : κ) (j : ℕ) :
    j ∈ bucketOf key t.buckets ↔ j < x.points.length ∧ t.hash x.points[j]! = key := by
  obtain ⟨h1, h2⟩ := hv t ht
  constructor
  · intro hj
    obtain ⟨b, hb, rfl, hjb⟩ := mem_bucketOf hj
    obtain ⟨hlt, hkey⟩ := h1 b hb j hjb
    exact ⟨hlt, by rw [getElem!_pos x.points j hlt]; exact hkey⟩
  · rintro ⟨hj, rfl⟩
    rw [getElem!_pos x.points j hj]
    exact h2 j hj

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem mem_candidates_iff (hs : List (Point d α → κ)) (pts : List (Point d α)) (q : Point d α)
    (j : ℕ) : j ∈ candidates hs pts q ↔ j < pts.length ∧ ∃ h ∈ hs, h pts[j]! = h q := by
  simp [candidates]

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- On a valid index, the candidates read from the stored buckets are those computed on the
fly. -/
theorem candidates_eq {x : Index d α κ} (hv : Valid x) (q : Point d α) :
    x.candidates q = candidates (x.tables.map Table.hash) x.points q := by
  have hmem : ∀ j, j ∈ x.candidates q ↔ j ∈ candidates (x.tables.map Table.hash) x.points q := by
    intro j
    rw [mem_candidates_iff]
    simp only [Index.candidates, List.mem_dedup, List.mem_insertionSort, List.mem_flatMap,
      List.mem_map]
    constructor
    · rintro ⟨t, ht, hj⟩
      obtain ⟨hlt, hkey⟩ := (mem_bucketOf_iff hv ht _ j).mp hj
      exact ⟨hlt, t.hash, ⟨t, ht, rfl⟩, hkey⟩
    · rintro ⟨hlt, _, ⟨t, ht, rfl⟩, hkey⟩
      exact ⟨t, ht, (mem_bucketOf_iff hv ht _ j).mpr ⟨hlt, hkey⟩⟩
  have hperm := (List.perm_ext_iff_of_nodup (List.nodup_dedup _)
    ((candidates_sorted _ _ q).imp Nat.ne_of_lt)).mpr hmem
  refine hperm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    ((List.pairwise_insertionSort _ _).sublist (List.dedup_sublist _))
    ((candidates_sorted _ _ q).imp Nat.le_of_lt)

omit [IsStrictOrderedRing α] in
/-- **The stored-bucket query is the on-the-fly re-rank**, on a valid index. -/
theorem nearest_eq_lshQuery {x : Index d α κ} (hv : Valid x) (q : Point d α) :
    nearest x q = lshQuery (x.tables.map Table.hash) x.points q := by
  simp only [nearest, lshQuery, candidates_eq hv]

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
/-- The build stores the points it is given, and one table per hash function. -/
theorem build_stores (hs : List (Point d α → κ)) (pts : List (Point d α)) :
    (build hs pts).points = pts ∧ (build hs pts).tables.map Table.hash = hs := by
  simp [build, Table.build, Function.comp_def]

omit [IsStrictOrderedRing α] in
/-- **Exact on a collision**: on a valid index, if the scan's answer shares a key with the query
in some table, the query returns exactly it. -/
theorem nearest_eq_scanNearest {x : Index d α κ} {q : Point d α} {n : ℕ}
    (hlt : n < x.points.length) (hv : Valid x) (hn : scanNearest x.points q = some n)
    (hc : ∃ t ∈ x.tables, t.hash x.points[n] = t.hash q) : nearest x q = some n := by
  rw [nearest_eq_lshQuery hv]
  obtain ⟨t, ht, he⟩ := hc
  refine lshQuery_eq_scanNearest hn ((mem_candidates_iff _ _ q n).mpr ⟨hlt, t.hash,
    List.mem_map_of_mem ht, ?_⟩)
  rw [getElem!_pos x.points n hlt]
  exact he

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- On a valid index, every candidate names a stored point. -/
theorem lt_of_mem_index_candidates {x : Index d α κ} (hv : Valid x) {q : Point d α} {c : ℕ}
    (hc : c ∈ x.candidates q) : c < x.points.length := by
  rw [candidates_eq hv, mem_candidates_iff] at hc
  exact hc.1

omit [IsStrictOrderedRing α] in
/-- **Box invariant 2, the nearest**: on a valid index, the answer is the nearest candidate,
measured exactly. -/
theorem measuredExactly_nearest {x : Index d α κ} (hv : Valid x) (q : Point d α) :
    MeasuredExactly ⟨x, q, 1, (nearest x q).toList⟩ := by
  refine ⟨fun c hc => lt_of_mem_index_candidates hv hc, ?_⟩
  simp only [Answer.candidates]
  rw [nearest_eq_lshQuery hv, candidates_eq hv]
  cases hq : lshQuery (x.tables.map Table.hash) x.points q with
  | none =>
    have hempty : candidates (x.tables.map Table.hash) x.points q = [] := by
      unfold lshQuery at hq
      have := (scanNearest_isSome_iff
        ((candidates (x.tables.map Table.hash) x.points q).map (x.points[·]!)) q).not
      simp only [Option.map_eq_none_iff] at hq
      have h2 := this.mp (by rw [hq]; simp)
      simpa using h2
    simp [hempty]
  | some i =>
    have hi := lshQuery_mem hq
    have hne : candidates (x.tables.map Table.hash) x.points q ≠ [] := List.ne_nil_of_mem hi
    refine ⟨by simp, ?_, by simpa using hi, ?_⟩
    · simp only [Option.toList_some, List.length_singleton]
      have := List.length_pos_iff.mpr hne
      omega
    · intro r hr c hc _ hrl hcl
      simp only [Option.toList_some, List.mem_singleton] at hr
      subst hr
      have := lshQuery_le_candidates hq c hc
      rwa [getElem!_pos x.points r hrl, getElem!_pos x.points c hcl] at this

omit [IsStrictOrderedRing α] in
/-- **Box invariant 2, the `k` nearest**: on a valid index, the answer is `min k` of the
candidates, each once, none farther than a candidate left out: `kNearest` ranks exactly the
candidates the index reads, and a valid index stores only ids of stored points. -/
theorem measuredExactly_kNearest {x : Index d α κ} (hv : Valid x) (q : Point d α) (k : ℕ) :
    MeasuredExactly ⟨x, q, k, kNearest x q k⟩ := by
  set r : ℕ → ℕ → Prop := fun a b => sqDist x.points[a]! q ≤ sqDist x.points[b]! q with hr
  have : Std.Total r := ⟨fun a b => le_total _ _⟩
  have : IsTrans ℕ r := ⟨fun a b c h1 h2 => le_trans h1 h2⟩
  have hperm := List.perm_insertionSort r (x.candidates q)
  have hsorted := List.pairwise_insertionSort r (x.candidates q)
  have hnodup : (List.insertionSort r (x.candidates q)).Nodup :=
    hperm.nodup_iff.mpr (List.nodup_dedup _)
  unfold kNearest
  refine ⟨fun c hc => lt_of_mem_index_candidates hv hc,
    hnodup.sublist (List.take_sublist _ _), by simp, ?_, ?_⟩
  · intro a ha
    exact hperm.subset (List.mem_of_mem_take ha)
  · intro a ha c hc hout hal hcl
    have hsplit := List.take_append_drop k (List.insertionSort r (x.candidates q))
    have hc' : c ∈ List.drop k (List.insertionSort r (x.candidates q)) := by
      have := hperm.symm.subset hc
      rw [← hsplit, List.mem_append] at this
      exact this.resolve_left hout
    rw [← hsplit] at hsorted
    have := (List.pairwise_append.mp hsorted).2.2 a ha c hc'
    simp only [hr] at this
    rwa [getElem!_pos x.points a hal, getElem!_pos x.points c hcl] at this

/-- Promise, for the `k` nearest: nearest first, the exact squared distances of the ids reported
never decreasing. -/
def NearestFirst (a : Answer d α κ) : Prop :=
  (a.result.filterMap fun r => a.index.points[r]?.map (sqDist · a.query)).Pairwise (· ≤ ·)

instance (a : Answer d α κ) : Decidable (NearestFirst a) := by
  unfold NearestFirst; infer_instance

omit [IsStrictOrderedRing α] in
/-- **The `k` nearest come nearest first**: `kNearest` sorts the candidates by exact distance
before it keeps `k`. -/
theorem nearestFirst_kNearest (x : Index d α κ) (q : Point d α) (k : ℕ) :
    NearestFirst ⟨x, q, k, kNearest x q k⟩ := by
  set r : ℕ → ℕ → Prop := fun a b => sqDist x.points[a]! q ≤ sqDist x.points[b]! q
  have : Std.Total r := ⟨fun a b => le_total _ _⟩
  have : IsTrans ℕ r := ⟨fun a b c h1 h2 => le_trans h1 h2⟩
  have hsorted := (List.pairwise_insertionSort r (x.candidates q)).sublist
    (List.take_sublist k _)
  unfold NearestFirst kNearest
  refine List.Pairwise.filterMap _ (fun a b hab da hda db hdb => ?_) hsorted
  simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff] at hda hdb
  obtain ⟨_, ⟨ha, rfl⟩, rfl⟩ := hda
  obtain ⟨_, ⟨hb, rfl⟩, rfl⟩ := hdb
  simpa only [r, getElem!_pos x.points a ha, getElem!_pos x.points b hb] using hab

end LSH

end AlgoDesign.Geometry
