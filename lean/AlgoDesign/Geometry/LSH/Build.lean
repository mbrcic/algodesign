/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.LSH.Spec

/-!
# LSH: the build

The Rust's procedure: per table, walk the points in order and append each id to the bucket its
key names, opening the bucket if the key is new. `valid_build`: every index the build makes keeps
`InItsBucket`, `OneBucketPerKey` and `EachPointOncePerTable`. `entries_length`: a valid index
holds one entry per point per table, the box's memory cost.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace LSH

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
variable {κ : Type} [DecidableEq κ]

/-- Append id `i` to the bucket with key `key`, or open that bucket at the end. -/
def addTo (key : κ) (i : ℕ) : List (Bucket κ) → List (Bucket κ)
  | [] => [⟨key, [i]⟩]
  | b :: rest =>
    if b.key = key then ⟨b.key, b.ids ++ [i]⟩ :: rest else b :: addTo key i rest

/-- Store the points `ps`, numbered from `i`, under their keys. -/
def fill (h : Point d α → κ) : List (Point d α) → ℕ → List (Bucket κ) → List (Bucket κ)
  | [], _, bs => bs
  | p :: ps, i, bs => fill h ps (i + 1) (addTo (h p) i bs)

/-- One table: its hash function, and every point stored under its key, in order. -/
def Table.build (h : Point d α → κ) (pts : List (Point d α)) : Table d α κ :=
  ⟨h, fill h pts 0 []⟩

/-- **The build**: the points, and one table per hash function. -/
def build (hs : List (Point d α → κ)) (pts : List (Point d α)) : Index d α κ :=
  ⟨pts, hs.map (Table.build · pts)⟩

theorem mem_bucketOf {key : κ} {bs : List (Bucket κ)} {j : ℕ} (h : j ∈ bucketOf key bs) :
    ∃ b ∈ bs, b.key = key ∧ j ∈ b.ids := by
  induction bs with
  | nil => simp [bucketOf] at h
  | cons b rest ih =>
    obtain ⟨k, ids⟩ := b
    unfold bucketOf at h
    split_ifs at h with hk
    · exact ⟨⟨k, ids⟩, by simp, hk, h⟩
    · obtain ⟨b, hb, h1, h2⟩ := ih h
      exact ⟨b, by simp [hb], h1, h2⟩

theorem bucketOf_addTo (key key' : κ) (i : ℕ) (bs : List (Bucket κ)) :
    bucketOf key' (addTo key i bs) =
      if key = key' then bucketOf key' bs ++ [i] else bucketOf key' bs := by
  induction bs with
  | nil => simp [addTo, bucketOf]
  | cons b rest ih =>
    obtain ⟨k, ids⟩ := b
    by_cases hk : k = key
    · subst hk; by_cases h' : k = key' <;> simp [addTo, bucketOf, h']
    · simp only [addTo, hk, ite_false, bucketOf, ih]
      by_cases h' : k = key'
      · subst h'; simp [Ne.symm hk]
      · simp [h']

theorem entries_addTo (key : κ) (i : ℕ) (bs : List (Bucket κ)) :
    ((addTo key i bs).flatMap Bucket.ids).Perm (bs.flatMap Bucket.ids ++ [i]) := by
  induction bs with
  | nil => simp [addTo]
  | cons b rest ih =>
    obtain ⟨k, ids⟩ := b
    unfold addTo
    split_ifs
    · simpa using List.Perm.append_left ids (List.perm_append_singleton _ _).symm
    · simpa using List.Perm.append_left ids ih

theorem mem_addTo {key : κ} {i j : ℕ} {bs : List (Bucket κ)} {b : Bucket κ}
    (hb : b ∈ addTo key i bs) (hj : j ∈ b.ids) :
    (j = i ∧ b.key = key) ∨ ∃ b' ∈ bs, b'.key = b.key ∧ j ∈ b'.ids := by
  induction bs with
  | nil => simp_all [addTo]
  | cons c rest ih =>
    obtain ⟨k, ids⟩ := c
    unfold addTo at hb
    split_ifs at hb with hk
    · rcases List.mem_cons.mp hb with rfl | hb
      · rcases List.mem_append.mp hj with hj | hj
        · exact Or.inr ⟨⟨k, ids⟩, by simp, rfl, hj⟩
        · simp_all
      · exact Or.inr ⟨b, by simp [hb], rfl, hj⟩
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inr ⟨⟨k, ids⟩, by simp, rfl, hj⟩
      · rcases ih hb with h | ⟨b', hb', h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨b', by simp [hb'], h1, h2⟩

/-- What the build has made after storing the first `m` points of `pts` in `bs`. -/
def Filled (h : Point d α → κ) (pts : List (Point d α)) (m : ℕ) (bs : List (Bucket κ)) :
    Prop :=
  (∀ b ∈ bs, ∀ j ∈ b.ids, j < m ∧ h pts[j]! = b.key) ∧
    (∀ j, (bs.flatMap Bucket.ids).count j = if j < m then 1 else 0) ∧
    ∀ j < m, j ∈ bucketOf (h pts[j]!) bs

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem filled_addTo {h : Point d α → κ} {pts : List (Point d α)} {m : ℕ}
    {bs : List (Bucket κ)} (hf : Filled h pts m bs) :
    Filled h pts (m + 1) (addTo (h pts[m]!) m bs) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨fun b hb j hj => ?_, fun j => ?_, fun j hj => ?_⟩
  · rcases mem_addTo hb hj with ⟨rfl, hk⟩ | ⟨b', hb', hk, hj'⟩
    · exact ⟨by omega, hk.symm⟩
    · obtain ⟨hlt, hkey⟩ := h1 b' hb' j hj'
      exact ⟨by omega, hkey.trans hk⟩
  · rw [(entries_addTo _ _ _).count_eq, List.count_append, h2]
    by_cases hjm : j = m
    · subst hjm; simp
    · have h0 : List.count j [m] = 0 := List.count_eq_zero.mpr (by simp [hjm])
      rw [h0]
      split_ifs <;> omega
  · rw [bucketOf_addTo]
    by_cases hjm : j = m
    · subst hjm; simp
    · have := h3 j (by omega)
      split_ifs <;> simp only [List.mem_append, this, true_or]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem filled_fill {h : Point d α → κ} {pts : List (Point d α)} :
    ∀ (ps : List (Point d α)) (m : ℕ) (bs : List (Bucket κ)),
      m + ps.length = pts.length → pts.drop m = ps → Filled h pts m bs →
        Filled h pts pts.length (fill h ps m bs)
  | [], m, bs, hm, _, hf => by simpa [fill, ← hm] using hf
  | p :: ps, m, bs, hm, hd, hf => by
    have hlt : m < pts.length := by simp at hm; omega
    rw [List.drop_eq_getElem_cons hlt] at hd
    obtain ⟨hp, hd⟩ := List.cons.inj hd
    have hp' : pts[m]! = p := by rw [getElem!_pos pts m hlt]; exact hp
    exact filled_fill ps (m + 1) _ (by simp at hm; omega) hd (hp' ▸ filled_addTo hf)

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem filled_build (h : Point d α → κ) (pts : List (Point d α)) :
    Filled h pts pts.length (Table.build h pts).buckets :=
  filled_fill pts 0 [] (by simp) (by simp) ⟨by simp, by simp, by simp⟩

/-- Adding to a bucket keeps the keys as they were, and opens a key at the end only if it is new. -/
theorem keys_addTo (key : κ) (i : ℕ) (bs : List (Bucket κ)) :
    (addTo key i bs).map Bucket.key =
      if key ∈ bs.map Bucket.key then bs.map Bucket.key else bs.map Bucket.key ++ [key] := by
  induction bs with
  | nil => simp [addTo]
  | cons b rest ih =>
    obtain ⟨k, ids⟩ := b
    by_cases hk : k = key
    · subst hk; simp [addTo]
    · by_cases hm : key ∈ rest.map Bucket.key <;>
        simp_all [addTo, Ne.symm hk]

/-- Adding to a bucket keeps one bucket per key, none empty. -/
theorem oneBucket_addTo (key : κ) (i : ℕ) {bs : List (Bucket κ)}
    (h : (bs.map Bucket.key).Nodup ∧ ∀ b ∈ bs, b.ids ≠ []) :
    ((addTo key i bs).map Bucket.key).Nodup ∧ ∀ b ∈ addTo key i bs, b.ids ≠ [] := by
  refine ⟨?_, ?_⟩
  · rw [keys_addTo]
    split_ifs with hm
    · exact h.1
    · exact h.1.append (List.nodup_singleton key) (by simpa using fun hk => hm hk)
  · obtain ⟨-, hne⟩ := h
    induction bs with
    | nil => simp [addTo]
    | cons c rest ih =>
      obtain ⟨k, ids⟩ := c
      intro b hb
      unfold addTo at hb
      split_ifs at hb with hk
      · rcases List.mem_cons.mp hb with rfl | hb
        · simp
        · exact hne b (List.mem_cons_of_mem _ hb)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact hne _ List.mem_cons_self
        · exact ih (fun b' hb' => hne b' (List.mem_cons_of_mem _ hb')) b hb

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
theorem oneBucket_fill (h : Point d α → κ) :
    ∀ (ps : List (Point d α)) (m : ℕ) (bs : List (Bucket κ)),
      (bs.map Bucket.key).Nodup ∧ (∀ b ∈ bs, b.ids ≠ []) →
        ((fill h ps m bs).map Bucket.key).Nodup ∧ ∀ b ∈ fill h ps m bs, b.ids ≠ []
  | [], _, _, hb => hb
  | p :: ps, m, _, hb => oneBucket_fill h ps (m + 1) _ (oneBucket_addTo (h p) m hb)

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- **The build is valid**: every point of every table sits in the bucket its key names, and
only there; each table holds one bucket per key, none empty. -/
theorem valid_build (hs : List (Point d α → κ)) (pts : List (Point d α)) :
    Valid (build hs pts) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩ <;>
    obtain ⟨h, -, rfl⟩ := List.mem_map.mp ht <;>
    obtain ⟨h1, h2, h3⟩ := filled_build (κ := κ) h pts <;>
    try simp only [build]
  · refine ⟨fun b hb j hj => ?_, fun i hi => ?_⟩
    · obtain ⟨hlt, hkey⟩ := h1 b hb j hj
      exact ⟨hlt, by rw [← getElem!_pos pts j hlt]; exact hkey⟩
    · rw [← getElem!_pos pts i hi]
      exact h3 i hi
  · exact oneBucket_fill h pts 0 [] (by simp)
  · intro i hi
    unfold Table.entries
    exact (h2 i).trans (by simp [hi])

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
/-- **Memory, one entry per point per table**: a valid index stores, in each table, exactly as
many ids as it has points. -/
theorem entries_length {x : Index d α κ} (hv : Valid x) {t : Table d α κ} (ht : t ∈ x.tables) :
    t.entries.length = x.points.length := by
  obtain ⟨h1, -⟩ := hv.1 t ht
  have hperm : t.entries.Perm (List.range x.points.length) := by
    rw [List.perm_iff_count]
    intro a
    rw [List.count_range]
    split_ifs with ha
    · exact hv.2.2 t ht a ha
    · rw [List.count_eq_zero]
      intro hm
      obtain ⟨b, hb, hab⟩ := List.mem_flatMap.mp hm
      exact ha (h1 b hb a hab).1
  simpa using hperm.length_eq

end LSH

end AlgoDesign.Geometry
