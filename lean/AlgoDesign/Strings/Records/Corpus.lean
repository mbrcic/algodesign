/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Strings.Records.Quote
public import AlgoDesign.Strings.FMIndex.Search

/-!
# The corpus: from a fragment to the quotes that hold it

`find` locates the fragment's hits, turns each into a record with `recordOf`, and keeps each record
number once, ascending. `findObligation` and `quoteObligation` discharge `FindSpec` and
`QuoteSpec`, record by record (`block` is one record's start bits): the joined text is
terminated (`terminated_text`), no match straddles a record (`prefix_append_cons_iff`), hits and
containing records correspond (`hits_iff`), and the fold is ordered (`foldl_insertId`).
-/

@[expose] public section

namespace AlgoDesign.Strings

namespace Corpus

/-- Insert a record number into an ascending list without repeating it. -/
def insertId (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => if x < y then x :: y :: l else if x = y then y :: l else y :: insertId x l

/-- `Corpus.find` as record numbers: every record for the empty fragment, none for one holding a
reserved byte, otherwise each hit's `recordOf`, once each, in order. -/
def find (sep s : Nat) (rs : List (List Nat)) (p : List Nat) : List Nat :=
  if p = [] then List.range rs.length
  else if s ∈ p ∨ sep ∈ p then []
  else
    let t := text sep s rs
    ((fmLocate t (suffixArray t) p).map (recordOf (starts rs))).foldl
      (fun ids id => insertId id ids) []

/-- On every well-formed corpus `find` meets `FindSpec`. -/
def FindObligation : Prop :=
  ∀ sep s rs, WellFormed sep s rs → FindSpec rs (find sep s rs)

/-- On every corpus the joined text and the bounds `starts` gives meet `QuoteSpec`: quoting needs
no well-formed corpus, only the layout. -/
def QuoteObligation : Prop :=
  ∀ sep s rs, QuoteSpec rs (text sep s rs) (recordBounds (starts rs))

/-! ### The proofs, record by record -/

/-- The start bits one record of length `L` contributes. -/
def block (r : List Nat) : List Bool := true :: List.replicate r.length false

/-- A record of length `L` spans `L + 1` start bits. -/
theorem length_block (r : List Nat) : (block r).length = r.length + 1 := by simp [block]

/-- The last record's start bits are its block alone. -/
theorem starts_singleton (r : List Nat) : starts [r] = block r ++ [] := by simp [starts, block]

/-- A record that is not the last contributes its block, and the rest follow. -/
theorem starts_cons_cons (r r' : List Nat) (rs : List (List Nat)) :
    starts (r :: r' :: rs) = block r ++ starts (r' :: rs) := rfl

/-- The last record is closed by the sentinel. -/
theorem text_singleton (sep s : Nat) (r : List Nat) : text sep s [r] = r ++ s :: [] := rfl

/-- A record that is not the last is closed by the separator, and the rest follow. -/
theorem text_cons_cons (sep s : Nat) (r r' : List Nat) (rs : List (List Nat)) :
    text sep s (r :: r' :: rs) = r ++ sep :: text sep s (r' :: rs) := by
  simp [text]

/-- Inside the first record's span, one start has been seen: its own. -/
theorem rank_block_le (r : List Nat) (S : List Bool) (i : Nat) (hi : i ≤ r.length) :
    rank (block r ++ S) (i + 1) = 1 := by
  simp only [rank, block, List.cons_append, List.take_succ_cons, List.take_append,
    List.length_replicate, Nat.sub_eq_zero_of_le hi, List.take_zero, List.append_nil,
    List.take_replicate]
  simp

/-- Past the first record's span, `rank` is one more than the rest of the vector's. -/
theorem rank_block_add (r : List Nat) (S : List Bool) (j : Nat) :
    rank (block r ++ S) (r.length + 1 + j) = 1 + rank S j := by
  have h := @List.take_append _ (block r) S (r.length + 1 + j)
  rw [length_block, List.take_of_length_le (l := block r) (by rw [length_block]; omega),
    Nat.add_sub_cancel_left] at h
  simp only [rank, h, List.filter_append, List.length_append]
  simp [block, Nat.add_comm]

/-- Past the first record's span, the bits are the rest of the vector's. -/
theorem getElem!_block_add (r : List Nat) (S : List Bool) (j : Nat) :
    (block r ++ S)[r.length + 1 + j]! = S[j]! := by
  rw [← length_block r]
  simp only [getElem!_def, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- A position inside the first record's span names record 0. -/
theorem recordOf_block_le (r : List Nat) (S : List Bool) (i : Nat) (hi : i ≤ r.length) :
    recordOf (block r ++ S) i = 0 := by
  rw [recordOf, rank_block_le r S i hi]

/-- A position past the first record's span names one more than it does in the rest of the
vector, when the rest begins with a start. -/
theorem recordOf_block_add (r : List Nat) (S : List Bool) (j : Nat) (hS : S[0]! = true) :
    recordOf (block r ++ S) (r.length + 1 + j) = recordOf S j + 1 := by
  have hpos := rank_pos_of_head S j hS
  change rank _ (r.length + 1 + (j + 1)) - 1 = rank S (j + 1) - 1 + 1
  rw [rank_block_add]
  omega

/-- No straddle: a `c`-free pattern that begins `u ++ c :: T` lies inside `u`. -/
theorem prefix_append_cons_iff {p u T : List Nat} {c : Nat} (hc : c ∉ p) :
    p <+: u ++ c :: T ↔ p <+: u := by
  constructor
  · intro h
    by_cases hle : p.length ≤ u.length
    · exact List.prefix_of_prefix_length_le h (List.prefix_append u _) hle
    · have hlt : u.length < p.length := by omega
      exfalso
      apply hc
      have hget := h.getElem (i := u.length) hlt
      rw [List.getElem_append_right (Nat.le_refl _)] at hget
      simp only [Nat.sub_self, List.getElem_cons_zero] at hget
      exact hget ▸ List.getElem_mem hlt
  · exact fun h => h.trans (List.prefix_append u _)

/-- An infix is a prefix of some suffix, read as a position. -/
theorem infix_iff_exists_prefix_drop {p r : List Nat} :
    p <:+: r ↔ ∃ i, i ≤ r.length ∧ p <+: r.drop i := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨a.length, by simp, ?_⟩
    simp only [List.append_assoc, List.drop_left]
    exact List.prefix_append p b
  · rintro ⟨i, -, h⟩
    exact h.isInfix.trans (List.drop_suffix i r).isInfix

/-- Past a record and the byte that closes it, the text is the rest. -/
theorem drop_record_add (r T : List Nat) (c j : Nat) :
    (r ++ c :: T).drop (r.length + 1 + j) = T.drop j := by
  rw [show r ++ c :: T = (r ++ [c]) ++ T by simp,
    show r.length + 1 + j = (r ++ [c]).length + j by simp]
  exact List.drop_length_add_append j

/-- A hit of a `c`-free pattern in `r ++ c :: T` lies inside `r` (record 0) or wholly in `T`. -/
theorem hits_cons (r T : List Nat) (c : Nat) (S : List Bool) (p : List Nat) (hc : c ∉ p)
    (id : Nat) :
    (∃ i, i < (r ++ c :: T).length ∧ p <+: (r ++ c :: T).drop i ∧ recordOf (block r ++ S) i = id) ↔
      ((id = 0 ∧ p <:+: r) ∨
        ∃ j, j < T.length ∧ p <+: T.drop j ∧ recordOf (block r ++ S) (r.length + 1 + j) = id) := by
  constructor
  · rintro ⟨i, hi, hp, hq⟩
    by_cases hle : i ≤ r.length
    · left
      rw [List.drop_append_of_le_length hle, prefix_append_cons_iff hc] at hp
      refine ⟨by rw [← hq, recordOf_block_le r S i hle], ?_⟩
      exact infix_iff_exists_prefix_drop.mpr ⟨i, hle, hp⟩
    · right
      obtain ⟨j, rfl⟩ : ∃ j, i = r.length + 1 + j := ⟨i - (r.length + 1), by omega⟩
      refine ⟨j, by simp at hi; omega, ?_, hq⟩
      rwa [drop_record_add] at hp
  · rintro (⟨rfl, hin⟩ | ⟨j, hj, hp, hq⟩)
    · obtain ⟨i, hle, hp⟩ := infix_iff_exists_prefix_drop.mp hin
      refine ⟨i, by simp; omega, ?_, recordOf_block_le r S i hle⟩
      rw [List.drop_append_of_le_length hle]
      exact hp.trans (List.prefix_append _ _)
    · refine ⟨r.length + 1 + j, by simp; omega, ?_, hq⟩
      rwa [drop_record_add]

/-- A non-empty corpus starts a record at position 0. -/
theorem starts_head (r : List Nat) (rs : List (List Nat)) : (starts (r :: rs))[0]! = true := by
  cases rs <;> simp [starts]

/-- A hit of a pattern free of reserved bytes names a record containing it, and every such record
is named by some hit. -/
theorem hits_iff (sep s : Nat) (p : List Nat) (hp : p ≠ []) (hs : s ∉ p) (hsep : sep ∉ p) :
    ∀ (rs : List (List Nat)) (id : Nat),
      (∃ i, i < (text sep s rs).length ∧ p <+: (text sep s rs).drop i ∧
          recordOf (starts rs) i = id) ↔ (id < rs.length ∧ p <:+: rs[id]!) := by
  intro rs
  induction rs with
  | nil =>
      intro id
      simp only [List.length_nil, Nat.not_lt_zero, false_and, iff_false]
      rintro ⟨i, hi, hpre, -⟩
      have : i = 0 := by simp [text] at hi; omega
      subst this
      have := (prefix_append_cons_iff (u := []) (T := []) hs).mp (by simpa [text] using hpre)
      exact hp (List.prefix_nil.mp this)
  | cons r rs ih =>
      intro id
      cases rs with
      | nil =>
          rw [text_singleton, starts_singleton, hits_cons r [] s [] p hs id]
          cases id <;> simp
      | cons r' rs' =>
          rw [text_cons_cons, starts_cons_cons, hits_cons r _ sep _ p hsep id]
          have hshift : ∀ j, recordOf (block r ++ starts (r' :: rs')) (r.length + 1 + j)
              = recordOf (starts (r' :: rs')) j + 1 :=
            fun j => recordOf_block_add r _ j (starts_head r' rs')
          simp only [hshift]
          cases id with
          | zero => simp
          | succ k =>
              have := ih k
              simp only [Nat.add_right_cancel_iff, Nat.add_one_ne_zero, false_and, false_or,
                List.length_cons, Nat.add_lt_add_iff_right, List.getElem!_cons_succ]
              exact this

/-- The joined text is a body closed by the sentinel, and every byte of the body is a record's
byte or the separator. -/
theorem text_eq_append (sep s : Nat) : ∀ rs : List (List Nat), ∃ body,
    text sep s rs = body ++ [s] ∧ ∀ c ∈ body, c = sep ∨ ∃ r ∈ rs, c ∈ r
  | [] => ⟨[], rfl, by simp⟩
  | [r] => ⟨r, rfl, fun c hc => Or.inr ⟨r, by simp, hc⟩⟩
  | r :: r' :: rs => by
      obtain ⟨body, hb, hmem⟩ := text_eq_append sep s (r' :: rs)
      refine ⟨r ++ sep :: body, by rw [text_cons_cons, hb]; simp, fun c hc => ?_⟩
      simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | rfl | hc
      · exact Or.inr ⟨r, by simp, hc⟩
      · exact Or.inl rfl
      · rcases hmem c hc with h | ⟨q, hq, hcq⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hcq⟩

/-- The joined text of a well-formed corpus is terminated. -/
theorem terminated_text (sep s : Nat) (rs : List (List Nat)) (h : WellFormed sep s rs) :
    Terminated (text sep s rs) s := by
  obtain ⟨body, hb, hmem⟩ := text_eq_append sep s rs
  rw [hb]
  refine ⟨by simp, ?_⟩
  rw [List.dropLast_concat]
  intro c hc
  rcases hmem c hc with rfl | ⟨r, hr, hcr⟩
  · exact h.1
  · exact h.2.1 r hr c hcr

/-- `insertId` adds its number to the list and nothing else. -/
theorem mem_insertId (x y : Nat) (l : List Nat) : x ∈ insertId y l ↔ x = y ∨ x ∈ l := by
  induction l with
  | nil => simp [insertId]
  | cons z l ih =>
      simp only [insertId]
      split_ifs with h1 h2
      · simp
      · subst h2; simp
      · simp only [List.mem_cons, ih]; tauto

/-- `insertId` keeps a strictly ascending list strictly ascending. -/
theorem pairwise_insertId (y : Nat) (l : List Nat) (hl : l.Pairwise (· < ·)) :
    (insertId y l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertId]
  | cons z l ih =>
      rw [List.pairwise_cons] at hl
      simp only [insertId]
      split_ifs with h1 h2
      · refine List.Pairwise.cons (fun w hw => ?_) (List.pairwise_cons.mpr hl)
        rcases List.mem_cons.mp hw with rfl | hw
        · exact h1
        · exact Nat.lt_trans h1 (hl.1 w hw)
      · exact List.pairwise_cons.mpr hl
      · refine List.Pairwise.cons (fun w hw => ?_) (ih hl.2)
        rcases (mem_insertId w y l).mp hw with rfl | hw
        · omega
        · exact hl.1 w hw

/-- Folding `insertId` leaves the numbers held and the list's own, strictly ascending, each once. -/
theorem foldl_insertId (L acc : List Nat) (hacc : acc.Pairwise (· < ·)) :
    (L.foldl (fun ids id => insertId id ids) acc).Pairwise (· < ·) ∧
      ∀ x, x ∈ L.foldl (fun ids id => insertId id ids) acc ↔ x ∈ acc ∨ x ∈ L := by
  induction L generalizing acc with
  | nil => simpa using hacc
  | cons y L ih =>
      obtain ⟨h1, h2⟩ := ih (insertId y acc) (pairwise_insertId y acc hacc)
      refine ⟨h1, fun x => ?_⟩
      simp only [List.foldl_cons, h2, mem_insertId, List.mem_cons]
      tauto

/-- `FindObligation` holds. -/
theorem findObligation : FindObligation := by
  intro sep s rs hwf p
  unfold find
  split_ifs with hnil hres
  · subst hnil
    exact (List.filter_eq_self.mpr (fun id hid => by simpa using hid)).symm
  · symm
    refine List.filter_eq_nil_iff.mpr (fun id _ => ?_)
    simp only [decide_eq_true_eq]
    rintro ⟨hidl, hin⟩
    have hmem : rs[id] ∈ rs := List.getElem_mem hidl
    rcases hres with hx | hx
    · exact Nat.lt_irrefl _ (hwf.2.1 _ hmem s (hin.subset hx))
    · exact hwf.2.2 _ hmem sep (hin.subset hx) rfl
  · simp only [not_or] at hres
    obtain ⟨hs, hsep⟩ := hres
    set t := text sep s rs
    have hperm := fmLocate_perm t s (terminated_text sep s rs hwf) (suffixArray t)
      (valid_suffixArray t) p (fun h => hs ((List.dropLast_sublist p).subset h))
    obtain ⟨hpw, hmemf⟩ := foldl_insertId
      ((fmLocate t (suffixArray t) p).map (recordOf (starts rs))) [] List.Pairwise.nil
    refine List.Perm.eq_of_pairwise
      (fun a b _ _ h₁ h₂ => absurd (Nat.lt_trans h₁ h₂) (Nat.lt_irrefl _)) hpw
      ((List.pairwise_lt_range).filter _) ?_
    refine (List.perm_ext_iff_of_nodup (hpw.imp Nat.ne_of_lt)
      (((List.pairwise_lt_range).filter _).imp Nat.ne_of_lt)).mpr (fun x => ?_)
    have hread : (x < rs.length ∧ ∃ h : x < rs.length, p <:+: rs[x]) ↔
        (x < rs.length ∧ p <:+: rs[x]!) :=
      ⟨fun ⟨h, _, h'⟩ => ⟨h, by rwa [getElem!_pos rs x h]⟩,
        fun ⟨h, h'⟩ => ⟨h, h, by rwa [getElem!_pos rs x h] at h'⟩⟩
    rw [hmemf, List.mem_filter, List.mem_range, decide_eq_true_eq, hread,
      ← hits_iff sep s p hnil hs hsep rs x]
    simp only [List.not_mem_nil, false_or, List.mem_map, hperm.mem_iff, List.mem_filter,
      List.mem_range, suffix]
    constructor
    · rintro ⟨i, ⟨hi, hpi⟩, hq⟩; exact ⟨i, hi, of_decide_eq_true hpi, hq⟩
    · rintro ⟨i, hi, hpi, hq⟩; exact ⟨i, ⟨hi, decide_eq_true hpi⟩, hq⟩

/-- The first record starts at position 0. -/
theorem select_block_zero (r : List Nat) (S : List Bool) : select (block r ++ S) 0 = some 0 :=
  (select_eq_some_iff _ 0 0).mpr ⟨by simp [block], by simp [block], by simp [rank]⟩

/-- Past the first record, `select` reads the rest of the vector, shifted by the record's span. -/
theorem select_block_succ (r : List Nat) (S : List Bool) (k : Nat) :
    select (block r ++ S) (k + 1) = (select S k).map (· + (r.length + 1)) := by
  cases hk : select S k with
  | some i =>
      obtain ⟨h1, h2, h3⟩ := (select_eq_some_iff S k i).mp hk
      refine (select_eq_some_iff _ _ _).mpr ⟨?_, ?_, ?_⟩
      · simp [length_block]; omega
      · change (block r ++ S)[i + (r.length + 1)]! = true
        rw [Nat.add_comm i, getElem!_block_add]; exact h2
      · change rank (block r ++ S) (i + (r.length + 1)) = k + 1
        rw [Nat.add_comm i, rank_block_add, h3, Nat.add_comm]
  | none =>
      simp only [Option.map_none]
      cases hm : select (block r ++ S) (k + 1) with
      | none => rfl
      | some m =>
          exfalso
          obtain ⟨h1, h2, h3⟩ := (select_eq_some_iff _ _ _).mp hm
          by_cases hle : m ≤ r.length
          · have hstep := rank_succ (block r ++ S) m
            simp only [h2, ite_true, rank_block_le r S m hle] at hstep
            omega
          · obtain ⟨i, rfl⟩ : ∃ i, m = r.length + 1 + i := ⟨m - (r.length + 1), by omega⟩
            rw [getElem!_block_add] at h2
            rw [rank_block_add] at h3
            have : select S k = some i :=
              (select_eq_some_iff S k i).mpr ⟨by simp [length_block] at h1; omega, h2, by omega⟩
            rw [hk] at this
            cases this

/-- Every record has a start. -/
theorem select_starts_isSome : ∀ (rs : List (List Nat)) (k : Nat), k < rs.length →
    (select (starts rs) k).isSome
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | [r], k, h => by
      obtain rfl : k = 0 := by simpa using h
      rw [starts_singleton, select_block_zero]; rfl
  | r :: r' :: rs, 0, _ => by rw [starts_cons_cons, select_block_zero]; rfl
  | r :: r' :: rs, k + 1, h => by
      rw [starts_cons_cons, select_block_succ, Option.isSome_map]
      exact select_starts_isSome (r' :: rs) k (by simpa using h)

/-- `QuoteObligation` holds: the layout alone puts each record between its start and the next. -/
theorem quoteObligation : QuoteObligation := by
  intro sep s rs
  induction rs with
  | nil => intro id h; exact absurd h (Nat.not_lt_zero _)
  | cons r rs ih =>
      intro id hid
      cases rs with
      | nil =>
          obtain rfl : id = 0 := by simpa using hid
          rw [text_singleton, starts_singleton]
          have h1 : select (block r ++ []) 1 = none := by rw [select_block_succ]; simp [select]
          simp only [recordBounds, select_block_zero, h1, Option.getD_some, Option.getD_none,
            List.length_append, length_block, List.length_nil, List.extract]
          simp
      | cons r' rs' =>
          rw [text_cons_cons, starts_cons_cons]
          set S := starts (r' :: rs')
          cases id with
          | zero =>
              have hS0 : select S 0 = some 0 := by
                cases rs' <;> simp only [S, starts_cons_cons, starts_singleton, select_block_zero]
              simp only [recordBounds, select_block_zero, Nat.zero_add, select_block_succ, hS0,
                Option.map_some, Option.getD_some, List.extract]
              simp
          | succ k =>
              have hk : k < (r' :: rs').length := by simpa using hid
              have ihk := ih k hk
              obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (select_starts_isSome _ k hk)
              simp only [recordBounds] at ihk ⊢
              rw [select_block_succ, select_block_succ, ha]
              rw [ha] at ihk
              simp only [Option.map_some, Option.getD_some, List.getElem_cons_succ]
              rw [← ihk]
              have hT : ∀ x, (r ++ sep :: text sep s (r' :: rs')).drop (x + (r.length + 1))
                  = (text sep s (r' :: rs')).drop x := by
                intro x
                rw [Nat.add_comm]
                exact drop_record_add r _ sep x
              cases hk1 : select S (k + 1) with
              | some e =>
                  simp only [Option.map_some, Option.getD_some, List.extract, hT]
                  congr 1
                  omega
              | none =>
                  simp only [Option.map_none, Option.getD_none, Option.getD_some, List.extract,
                    List.length_append, length_block]
                  rw [hT]
                  congr 1
                  omega

end Corpus

end AlgoDesign.Strings
