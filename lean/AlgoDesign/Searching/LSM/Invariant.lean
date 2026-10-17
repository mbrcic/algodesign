/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Flush

/-!
# LSM-tree: the store stays valid

Every store the API builds is `Store.Valid` (`Store.valid_flush`, `Store.valid_write`,
`Store.valid_compactFully`, `Store.valid_of_reachable`). The cascade runs on a fuel proved enough
(`Store.cascadeFrom_enough`, `Store.flush_fuel_add`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace LSM

variable {α β : Type} [LinearOrder α]

namespace Store

omit [LinearOrder α] in
@[simp] theorem entries_nil : entries ([] : List (Run α β)) = 0 := rfl

omit [LinearOrder α] in
@[simp] theorem entries_cons (r : Run α β) (rs : List (Run α β)) :
    entries (r :: rs) = r.length + entries rs := rfl

omit [LinearOrder α] in
theorem entries_append (xs ys : List (Run α β)) : entries (xs ++ ys) = entries xs + entries ys := by
  simp [entries]

omit [LinearOrder α] in
theorem length_getLast?_getD_le (m : List (Run α β)) :
    (m.getLast?.getD []).length ≤ entries m := by
  induction m with
  | nil => simp
  | cons r m ih =>
      cases m with
      | nil => simp
      | cons r' m =>
          rw [List.getLast?_cons_cons, entries_cons]
          omega

omit [LinearOrder α] in
theorem entries_slot (r : Run α β) : entries (slot r) = r.length := by
  unfold slot
  split_ifs with he
  · simp [List.isEmpty_iff.mp he]
  · simp

theorem entries_pushInto_le (newer : Run α β) (m : List (Run α β)) (d : Bool) :
    entries (pushInto newer m d) ≤ newer.length + entries m := by
  have h1 := Run.length_mergeRuns_le newer (m.getLast?.getD [])
  have h2 := length_getLast?_getD_le m
  cases d
  · simp only [pushInto, Bool.false_eq_true, ↓reduceIte, entries_slot]; omega
  · have := Run.length_dropTombstones_le (Run.mergeRuns newer (m.getLast?.getD []))
    simp only [pushInto, ↓reduceIte, entries_slot]; omega

omit [LinearOrder α] in
/-- The cascade's test against the contract: a level is not over its budget exactly when its run
holds at most `budget i` entries. -/
theorem over_eq_false_iff {sh : Shape} {i : Nat} {l : List (Run α β)} :
    over sh i l = false ↔ ∀ r ∈ l.head?, r.length ≤ sh.budget i := by
  cases l <;> simp [over]

omit [LinearOrder α] in
theorem withinBudgetFrom_cons {sh : Shape} {i : Nat} {l : List (Run α β)}
    {ls : List (List (Run α β))} (h : over sh i l = false) (hs : WithinBudgetFrom sh (i + 1) ls) :
    WithinBudgetFrom sh i (l :: ls) := by
  cases ls with
  | nil => trivial
  | cons m rest => exact ⟨over_eq_false_iff.mp h, hs⟩

omit [LinearOrder α] in
theorem over_nil (sh : Shape) (i : Nat) : over sh i ([] : List (Run α β)) = false := rfl

theorem cascadeFrom_nil (sh : Shape) : ∀ (fuel i : Nat),
    cascadeFrom sh fuel i ([] : List (List (Run α β))) = []
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem cascadeFrom_over_nil {sh : Shape} {fuel i : Nat} {l : List (Run α β)}
    (h : over sh i l = true) : cascadeFrom sh (fuel + 1) i [l] =
      l.dropLast :: cascadeFrom sh fuel (i + 1) [pushInto (l.getLast?.getD []) [] true] := by
  simp only [cascadeFrom, h, ↓reduceIte]

theorem cascadeFrom_over_cons {sh : Shape} {fuel i : Nat} {l m : List (Run α β)}
    {post : List (List (Run α β))} (h : over sh i l = true) :
    cascadeFrom sh (fuel + 1) i (l :: m :: post) =
      l.dropLast ::
        cascadeFrom sh fuel (i + 1)
          (pushInto (l.getLast?.getD []) m (post.all List.isEmpty) :: post) := by
  simp only [cascadeFrom, h, ↓reduceIte]

theorem cascadeFrom_not_over {sh : Shape} {fuel i : Nat} {l : List (Run α β)}
    {rest : List (List (Run α β))} (h : over sh i l = false) :
    cascadeFrom sh (fuel + 1) i (l :: rest) = l :: cascadeFrom sh fuel (i + 1) rest := by
  cases rest <;> simp only [cascadeFrom, h, Bool.false_eq_true, ↓reduceIte]

/-- **The cascade's fuel is enough.** With every level at one run at most and at most `N` entries
between them, a cascade from level `i` given `ls.length + (N - i)` steps settles every level but
the deepest within its budget, and one more step would change nothing. The count: a level that
is not over budget is passed and not revisited; a level over budget holds more than
`budget i > i` entries, so it lies above level `N`, and only there can the cascade add a level. -/
theorem cascadeFrom_enough (sh : Shape) (hc : 1 ≤ sh.capacity) (hr : 2 ≤ sh.ratio) (N : Nat) :
    ∀ (fuel i : Nat) (ls : List (List (Run α β))), (∀ l ∈ ls, l.length ≤ 1) →
      entries ls.flatten ≤ N → ls.length + (N - i) ≤ fuel →
      WithinBudgetFrom sh i (cascadeFrom sh fuel i ls) ∧
        cascadeFrom sh (fuel + 1) i ls = cascadeFrom sh fuel i ls
  | 0, i, ls, _, _, hf => by
      have : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨trivial, rfl⟩
  | fuel + 1, i, [], _, _, _ => ⟨by simp [cascadeFrom, WithinBudgetFrom], rfl⟩
  | fuel + 1, i, l :: rest, h1, hN, hf => by
      have hl : l.length ≤ 1 := h1 l (by simp)
      have hrest : ∀ l' ∈ rest, l'.length ≤ 1 := fun l' hl' => h1 l' (by simp [hl'])
      simp only [List.flatten_cons, entries_append, List.length_cons] at hN hf
      by_cases ho : over sh i l = true
      · obtain ⟨r, rfl⟩ : ∃ r, l = [r] := by
          match l, hl, ho with
          | [r], _, _ => exact ⟨r, rfl⟩
        have hbud : sh.budget i < r.length := by simpa [over] using ho
        have hlt := Shape.lt_budget hc hr i
        simp only [entries_cons, entries_nil] at hN
        match rest, hrest, hN, hf with
        | [], _, hN, hf =>
            have hp := entries_pushInto_le r ([] : List (Run α β)) true
            have ih := cascadeFrom_enough sh hc hr N fuel (i + 1) [pushInto r [] true]
              (by simp [length_pushInto_le]) (by simp at hp ⊢; omega) (by simp; omega)
            refine ⟨?_, ?_⟩
            · simp only [cascadeFrom, ho, ↓reduceIte, List.dropLast_singleton,
                List.getLast?_singleton,
                Option.getD_some]
              exact withinBudgetFrom_cons (over_nil sh i) ih.1
            · rw [cascadeFrom_over_nil ho, cascadeFrom_over_nil ho]
              simp only [List.getLast?_singleton, Option.getD_some, ih.2]
        | m :: post, hrest', hN, hf =>
            have hm : m.length ≤ 1 := hrest' m (by simp)
            have hp := entries_pushInto_le r m (post.all List.isEmpty)
            have ih := cascadeFrom_enough sh hc hr N fuel (i + 1)
              (pushInto r m (post.all List.isEmpty) :: post)
              (by
                intro l' hl'
                rcases List.mem_cons.mp hl' with rfl | hl'
                · exact length_slot_le _
                · exact hrest' l' (by simp [hl']))
              (by simp only [List.flatten_cons, entries_append] at hN ⊢; omega)
              (by simp only [List.length_cons] at hf ⊢; omega)
            refine ⟨?_, ?_⟩
            · simp only [cascadeFrom, ho, ↓reduceIte, List.dropLast_singleton,
                List.getLast?_singleton, Option.getD_some]
              exact withinBudgetFrom_cons (over_nil sh i) ih.1
            · rw [cascadeFrom_over_cons ho, cascadeFrom_over_cons ho]
              simp only [List.getLast?_singleton, Option.getD_some, ih.2]
      · have ho' : over sh i l = false := by simpa using ho
        have ih := cascadeFrom_enough sh hc hr N fuel (i + 1) rest hrest (by omega) (by omega)
        refine ⟨?_, ?_⟩
        · simp only [cascadeFrom, ho', Bool.false_eq_true, ↓reduceIte]
          exact withinBudgetFrom_cons ho' ih.1
        · rw [cascadeFrom_not_over ho', cascadeFrom_not_over ho', ih.2]

/-- More fuel than `cascadeFrom_enough` asks for changes nothing. -/
theorem cascadeFrom_fuel_add (sh : Shape) (hc : 1 ≤ sh.capacity) (hr : 2 ≤ sh.ratio) (N : Nat)
    {fuel i : Nat} {ls : List (List (Run α β))} (h1 : ∀ l ∈ ls, l.length ≤ 1)
    (hN : entries ls.flatten ≤ N) (hf : ls.length + (N - i) ≤ fuel) :
    ∀ k, cascadeFrom sh (fuel + k) i ls = cascadeFrom sh fuel i ls
  | 0 => rfl
  | k + 1 => by
      rw [← Nat.add_assoc, (cascadeFrom_enough sh hc hr N (fuel + k) i ls h1 hN (by omega)).2,
        cascadeFrom_fuel_add sh hc hr N h1 hN hf k]

omit [LinearOrder α] in
theorem withinBudgetFrom_tail {sh : Shape} : ∀ {i : Nat} {ls : List (List (Run α β))},
    WithinBudgetFrom sh i ls → WithinBudgetFrom sh (i + 1) ls.tail
  | _, [], _ => trivial
  | _, [_], _ => trivial
  | _, _ :: _ :: _, h => h.2

/-- The oldest of these runs, if there is one, holds no tombstone: `OldestRunClean` on any list of
runs, the form the proofs carry through a cascade. -/
def OldestClean (rs : List (Run α β)) : Prop := ∀ r ∈ rs.getLast?, Run.Clean r

omit [LinearOrder α] in
omit [LinearOrder α] in
theorem OldestClean.of_append {xs ys : List (Run α β)} (h : OldestClean (xs ++ ys)) :
    OldestClean ys := by
  intro r hr
  apply h r
  rw [List.getLast?_append, Option.mem_def.mp hr]
  rfl

omit [LinearOrder α] in
theorem OldestClean.append {xs ys : List (Run α β)} (h : OldestClean ys) (hy : ys ≠ []) :
    OldestClean (xs ++ ys) := by
  have hr := List.getLast?_eq_some_getLast hy
  intro q hq
  rw [List.getLast?_append, hr] at hq
  exact h q (by simpa [hr] using hq)

omit [LinearOrder α] in
theorem oldestClean_cons {x : Run α β} {ys : List (Run α β)} (h : OldestClean ys)
    (hx : ys = [] → Run.Clean x) : OldestClean (x :: ys) := by
  cases ys with
  | nil => simpa [OldestClean] using hx rfl
  | cons y ys => exact h.append (xs := [x]) (List.cons_ne_nil _ _)

/-- **A push leaves the oldest run clean.** With something below, the oldest run is still below;
with nothing below, the merge has lost its tombstones, or cancelled out to an empty slot. -/
theorem oldestClean_pushInto (newer : Run α β) (m : List (Run α β))
    {post : List (List (Run α β))} (h : OldestClean post.flatten) :
    OldestClean (pushInto newer m (post.all List.isEmpty) ++ post.flatten) := by
  cases hpost : post.all List.isEmpty
  · exact h.append (fun hnil => by simp [all_isEmpty_iff.mpr hnil] at hpost)
  · rw [all_isEmpty_iff.mp hpost, List.append_nil]
    intro q hq
    have := mem_slot (List.mem_of_getLast? hq)
    simp only [↓reduceIte] at this
    rw [this.1]
    exact Run.clean_dropTombstones _

theorem pushInto_clean {r : Run α β} (hc : Run.Clean r) (hr : r ≠ []) :
    pushInto r [] true = [r] := by
  have hd : Run.dropTombstones r = r := List.filter_eq_self.mpr
    (fun p hp => Option.isSome_iff_ne_none.mpr (hc p hp))
  simp only [pushInto, ↓reduceIte, List.getLast?_nil, Option.getD_none,
    Run.mergeRuns_nil_right, hd, slot, List.isEmpty_iff, hr]

/-- **The cascade leaves the oldest run clean**, for any fuel. A push that cancels out exposes the
runs above it, which must then be clean too; that holds since a push down from a level happens
only when every level above it has been pushed down already (`above = []`), or when the level is
the deepest, whose run is the oldest and so pushes down whole. Hence the hypotheses: every level
within budget before the cascade (`WithinBudgetFrom`), as a flush finds it. -/
theorem oldestClean_cascadeFrom (sh : Shape) : ∀ (fuel i : Nat) (above : List (Run α β))
    (ls : List (List (Run α β))), (∀ l ∈ ls, l.length ≤ 1) →
    (above = [] ∨ WithinBudgetFrom sh i ls) → WithinBudgetFrom sh (i + 1) ls.tail →
    OldestClean (above ++ ls.flatten) →
    OldestClean (above ++ (cascadeFrom sh fuel i ls).flatten)
  | 0, _, _, _, _, _, _, h => h
  | _ + 1, _, _, [], _, _, _, h => by rwa [cascadeFrom_nil]
  | fuel + 1, i, above, l :: rest, h1, hab, hs, h => by
      have hl : l.length ≤ 1 := h1 l (by simp)
      have hrest : ∀ l' ∈ rest, l'.length ≤ 1 := fun l' hl' => h1 l' (by simp [hl'])
      by_cases ho : over sh i l = true
      · obtain ⟨r, rfl⟩ : ∃ r, l = [r] := by
          match l, hl, ho with
          | [r], _, _ => exact ⟨r, rfl⟩
        have hr : r ≠ [] := by rintro rfl; simp [over] at ho
        match rest, hrest, hab, hs, h with
        | [], _, _, _, h =>
            rw [cascadeFrom_over_nil ho]
            simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at h
            have hc : Run.Clean r := h r (by simp)
            have ih := oldestClean_cascadeFrom sh fuel (i + 1) above [[r]] (by simp)
              (Or.inr trivial) trivial (by simpa using h)
            simpa [pushInto_clean hc hr] using ih
        | m :: post, hrest', hab, hs, h =>
            have habove : above = [] := by
              rcases hab with hab | hab
              · exact hab
              · have hle := hab.1 r (by simp)
                simp [over] at ho
                omega
            subst habove
            rw [cascadeFrom_over_cons ho]
            have hpost : OldestClean post.flatten :=
              OldestClean.of_append (xs := [r] ++ m) (by simpa using h)
            have ih := oldestClean_cascadeFrom sh fuel (i + 1) []
              (pushInto (([r] : List (Run α β)).getLast?.getD []) m (post.all List.isEmpty) :: post)
              (by
                intro l' hl'
                rcases List.mem_cons.mp hl' with rfl | hl'
                · exact length_pushInto_le _ _ _
                · exact hrest' l' (by simp [hl']))
              (Or.inl rfl) (withinBudgetFrom_tail (ls := m :: post) hs)
              (by simpa using oldestClean_pushInto _ m hpost)
            simpa using ih
      · rw [cascadeFrom_not_over (by simpa using ho)]
        have ih := oldestClean_cascadeFrom sh fuel (i + 1) (above ++ l) rest hrest (Or.inr hs)
          (withinBudgetFrom_tail hs) (by simpa using h)
        simpa using ih

/-- The cascade files no empty run: a push that cancels out leaves an empty slot. -/
theorem nonempty_cascadeFrom (sh : Shape) : ∀ (fuel i : Nat) (ls : List (List (Run α β))),
    (∀ r ∈ ls.flatten, r ≠ []) → ∀ r ∈ (cascadeFrom sh fuel i ls).flatten, r ≠ []
  | 0, _, _, h => h
  | _ + 1, _, [], h => by rw [cascadeFrom_nil]; exact h
  | fuel + 1, i, l :: rest, h => by
      have hrest : ∀ r ∈ rest.flatten, r ≠ [] := fun r hr => h r (by
        rw [List.flatten_cons]; exact List.mem_append.mpr (Or.inr hr))
      by_cases ho : over sh i l = true
      · match rest, hrest with
        | [], _ =>
            rw [cascadeFrom_over_nil ho]
            intro r hr
            simp only [List.flatten_cons, List.mem_append] at hr
            rcases hr with hr | hr
            · exact h r (by
                rw [List.flatten_cons]
                exact List.mem_append.mpr (Or.inl ((List.dropLast_sublist _).subset hr)))
            · exact nonempty_cascadeFrom sh fuel (i + 1) _
                (fun q hq => ne_nil_of_mem_pushInto (by simpa using hq)) r hr
        | m :: post, hrest' =>
            rw [cascadeFrom_over_cons ho]
            intro r hr
            simp only [List.flatten_cons, List.mem_append] at hr
            rcases hr with hr | hr
            · exact h r (by
                rw [List.flatten_cons]
                exact List.mem_append.mpr (Or.inl ((List.dropLast_sublist _).subset hr)))
            · refine nonempty_cascadeFrom sh fuel (i + 1) _ (fun q hq => ?_) r hr
              simp only [List.flatten_cons, List.mem_append] at hq
              rcases hq with hq | hq
              · exact ne_nil_of_mem_pushInto hq
              · exact hrest' q (by
                  rw [List.flatten_cons]; exact List.mem_append.mpr (Or.inr hq))
      · rw [cascadeFrom_not_over (by simpa using ho)]
        intro r hr
        simp only [List.flatten_cons, List.mem_append] at hr
        rcases hr with hr | hr
        · exact h r (by rw [List.flatten_cons]; exact List.mem_append.mpr (Or.inl hr))
        · exact nonempty_cascadeFrom sh fuel (i + 1) rest hrest r hr

theorem length_foldl_mergeRuns_le : ∀ (rs : List (Run α β)) (acc : Run α β),
    (rs.foldl Run.mergeRuns acc).length ≤ acc.length + entries rs
  | [], _ => by simp
  | r :: rs, acc => by
      have := length_foldl_mergeRuns_le rs (Run.mergeRuns acc r)
      have := Run.length_mergeRuns_le acc r
      simp only [List.foldl_cons, entries_cons]
      omega

theorem length_mergeLevel0_le : ∀ (l0 : List (Run α β)), (mergeLevel0 l0).length ≤ entries l0
  | [] => by simp [mergeLevel0]
  | r :: rs => by simpa [mergeLevel0] using length_foldl_mergeRuns_le rs r

/-- **Filing a sealed run, and the spill and cascade it may set off, finishes the job** when the
fuel covers the levels and the entries: no run is empty, every level below 0 but the deepest ends
within budget (`WithinBudgetFrom`), the oldest run below level 0 holds no tombstone, and more
fuel would change nothing. -/
theorem fileRun_ok (sh : Shape) (hc : 1 ≤ sh.capacity) (hr : 2 ≤ sh.ratio) (fuel : Nat)
    {fresh : Run α β} {l0 : List (Run α β)} {deeper : List (List (Run α β))}
    (hd : ∀ l ∈ deeper, l.length ≤ 1) (hs : WithinBudgetFrom sh 1 deeper)
    (hne : ∀ r ∈ l0 ++ deeper.flatten, r ≠ [])
    (hold : OldestClean deeper.flatten)
    (hfuel : deeper.length + 1 + (fresh.length + entries l0 + entries deeper.flatten) ≤ fuel) :
    (∀ r ∈ (fileRun sh fuel fresh l0 deeper).flatten, r ≠ []) ∧
      WithinBudgetFrom sh 1 (fileRun sh fuel fresh l0 deeper).tail ∧
      OldestClean (fileRun sh fuel fresh l0 deeper).tail.flatten ∧
      ∀ k, fileRun sh (fuel + k) fresh l0 deeper = fileRun sh fuel fresh l0 deeper := by
  set l0' := if fresh.isEmpty then l0 else fresh :: l0 with hl0'
  have he0 : entries l0' ≤ fresh.length + entries l0 := by
    rw [hl0']
    split_ifs <;> simp
  have hne' : ∀ r ∈ l0' ++ deeper.flatten, r ≠ [] := by
    intro r hr
    rw [hl0'] at hr
    split_ifs at hr with hfe
    · exact hne r hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact fun h => by simp [h] at hfe
      · exact hne r hr
  have hm0 := length_mergeLevel0_le l0'
  unfold fileRun
  simp only [← hl0']
  split_ifs with hle
  · exact ⟨by simpa using hne', hs, by simpa using hold, fun _ => rfl⟩
  · match deeper, hd, hs, hold, hfuel, hne' with
    | [], _, _, _, hfuel, _ =>
        simp only [spill, cascade, List.flatten_cons, List.nil_append, List.tail_cons]
        have hp := entries_pushInto_le (mergeLevel0 l0') ([] : List (Run α β)) true
        have hfu : [pushInto (mergeLevel0 l0') [] true].length +
            (entries [pushInto (mergeLevel0 l0') [] true].flatten - 1) ≤ fuel := by
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
            List.length_nil, entries_nil] at hp hfuel ⊢
          omega
        have h1 : ∀ l ∈ [pushInto (mergeLevel0 l0') [] true], l.length ≤ 1 := by
          simp [length_pushInto_le]
        refine ⟨nonempty_cascadeFrom sh fuel 1 _
            (fun q hq => ne_nil_of_mem_pushInto (by simpa using hq)),
          (cascadeFrom_enough sh hc hr _ fuel 1 _ h1 (Nat.le_refl _) hfu).1, ?_, fun k => ?_⟩
        · have := oldestClean_cascadeFrom sh fuel 1 [] [pushInto (mergeLevel0 l0') [] true] h1
            (Or.inl rfl) trivial
            (by simpa using
              oldestClean_pushInto (mergeLevel0 l0') [] (post := []) (by simp [OldestClean]))
          simpa using this
        · rw [cascadeFrom_fuel_add sh hc hr _ h1 (Nat.le_refl _) hfu k]
    | m :: post, hd', hs', hold', hfuel, hne'' =>
        simp only [spill, cascade, List.flatten_cons, List.nil_append, List.tail_cons]
        have hm : m.length ≤ 1 := hd' m (by simp)
        have hp := entries_pushInto_le (mergeLevel0 l0') m (post.all List.isEmpty)
        have h1 : ∀ l ∈ pushInto (mergeLevel0 l0') m (post.all List.isEmpty) :: post,
            l.length ≤ 1 := by
          intro l' hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact length_slot_le _
          · exact hd' l' (by simp [hl'])
        have hfu : (pushInto (mergeLevel0 l0') m (post.all List.isEmpty) :: post).length +
            (entries (pushInto (mergeLevel0 l0') m (post.all List.isEmpty) :: post).flatten - 1)
              ≤ fuel := by
          simp only [List.flatten_cons, entries_append, List.length_cons] at hp hfuel ⊢
          omega
        refine ⟨nonempty_cascadeFrom sh fuel 1 _ (fun q hq => ?_),
          (cascadeFrom_enough sh hc hr _ fuel 1 _ h1 (Nat.le_refl _) hfu).1, ?_, fun k => ?_⟩
        · simp only [List.flatten_cons, List.mem_append] at hq
          rcases hq with hq | hq
          · exact ne_nil_of_mem_pushInto hq
          · exact hne'' q (by
              rw [List.flatten_cons]
              exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hq))))
        · have hpost : OldestClean post.flatten :=
            OldestClean.of_append (xs := m) (by simpa using hold')
          have := oldestClean_cascadeFrom sh fuel 1 []
            (pushInto (mergeLevel0 l0') m (post.all List.isEmpty) :: post) h1 (Or.inl rfl)
            (withinBudgetFrom_tail (ls := m :: post) hs')
            (by simpa using oldestClean_pushInto (mergeLevel0 l0') m hpost)
          simpa using this
        · rw [cascadeFrom_fuel_add sh hc hr _ h1 (Nat.le_refl _) hfu k]

/-- **The empty store is valid** at every usable shape. -/
theorem valid_empty {sh : Shape} (hsh : sh.Usable) : Valid (empty sh : Store α β) :=
  ⟨runsSorted_empty sh, ⟨fewRuns_empty sh, trivial⟩, by simp [empty, RunsNonEmpty],
    by simp [empty, OldestRunClean], hsh⟩

/-- The flush of a valid store meets `fileRun_ok`'s hypotheses: `fuel` covers the levels and the
entries. -/
theorem fileRun_ok_flush {s : Store α β} (h : Valid s) :
    let out := fileRun s.shape s.fuel s.memtable (s.levels.headD []) s.levels.tail
    (∀ r ∈ out.flatten, r ≠ []) ∧ WithinBudgetFrom s.shape 1 out.tail ∧
      OldestClean out.tail.flatten ∧
      ∀ k, fileRun s.shape (s.fuel + k) s.memtable (s.levels.headD []) s.levels.tail = out := by
  have hflat := headD_append_flatten_tail s.levels
  have hfuel : s.levels.tail.length + 1 +
      (s.memtable.length + entries (s.levels.headD []) + entries s.levels.tail.flatten) ≤
        s.fuel := by
    have h2 : entries (s.levels.headD []) + entries s.levels.tail.flatten =
        entries s.levels.flatten := by
      rw [← entries_append, headD_append_flatten_tail]
    have h3 : s.levels.tail.length ≤ s.levels.length := by simp
    have h4 : s.fuel = s.levels.length + (s.memtable.length + entries s.levels.flatten) + 3 := rfl
    omega
  obtain ⟨_, ⟨hfew, hbud⟩, hne, hold, hc, hr, _⟩ := h
  exact fileRun_ok s.shape hc hr s.fuel hfew.2 hbud (by rw [hflat]; exact hne) hold hfuel

/-- **A flush keeps the store valid**, `is_valid` in full: its cascade runs to the end on `fuel`,
leaving every level but the deepest within budget, no empty run, and the oldest run below level
0 clean. -/
theorem valid_flush {s : Store α β} (h : Valid s) : Valid (flush s) := by
  have hf := fileRun_ok_flush h
  obtain ⟨hs, ⟨hfew, hbud⟩, hne, hold, hsh⟩ := h
  refine ⟨runsSorted_flush hs hfew, ⟨fewRuns_flush hs hfew, ?_⟩, ?_⟩
  · unfold LevelsWithinBudget flush
    cases he : s.memtable.isEmpty
    · exact hf.2.1
    · exact hbud
  · unfold flush
    cases he : s.memtable.isEmpty
    · exact ⟨hf.1, hf.2.2.1, hsh⟩
    · exact ⟨hne, hold, hsh⟩

/-- **`fuel` is enough**: a flush given any more fuel files and cascades to the same levels. -/
theorem flush_fuel_add {s : Store α β} (h : Valid s) (k : Nat) :
    fileRun s.shape (s.fuel + k) s.memtable (s.levels.headD []) s.levels.tail =
      fileRun s.shape s.fuel s.memtable (s.levels.headD []) s.levels.tail :=
  (fileRun_ok_flush h).2.2.2 k

theorem valid_flushIfFull {s : Store α β} (h : Valid s) : Valid (flushIfFull s) := by
  unfold flushIfFull
  split_ifs
  · exact valid_flush h
  · exact h

/-- **A write keeps the store valid**, flush or no flush. -/
theorem valid_write {s : Store α β} (h : Valid s) (a : α) (v : Option β) :
    Valid (write a v s) :=
  valid_flushIfFull ⟨runsSorted_write_memtable h.1 a v, h.2⟩

/-- **A delete keeps the store valid**: it is a write of a tombstone. -/
theorem valid_delete {s : Store α β} (h : Valid s) (a : α) : Valid (delete a s) :=
  valid_write h a none

/-- **A full compaction keeps the store valid**: one clean, non-empty run in level 0, or
nothing. Needs `level0Runs ≥ 1`, from `ShapeUsable`, for level 0 to hold that one run. -/
theorem valid_compactFully {s : Store α β} (h : Valid s) : Valid (compactFully s) := by
  have hv := (preservesGet_compactFully h.1 h.2.1.1).2
  have hmt := memtable_flush s
  have hsh := h.2.2.2.2
  have hvl : LSM.EachSorted (compactFully s).levels.flatten := fun q hq =>
    hv q (List.mem_cons_of_mem _ hq)
  unfold compactFully at hvl ⊢
  dsimp only at hvl ⊢
  split_ifs at hvl ⊢ with he
  · exact ⟨⟨by simp [hmt], by simp⟩, ⟨⟨by simp, by simp⟩, trivial⟩, by simp [RunsNonEmpty],
      by simp [OldestRunClean], by simpa [ShapeUsable] using hsh⟩
  · refine ⟨⟨by simp [hmt], hvl⟩, ⟨⟨by simpa using hsh.2.2, by simp⟩, trivial⟩, ?_, ?_,
      by simpa [ShapeUsable] using hsh⟩
    · simp only [RunsNonEmpty, diskRuns, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_singleton]
      rintro r rfl hr
      exact he (List.isEmpty_iff.mpr hr)
    · simp [OldestRunClean]

/-- The stores the public API builds: from an empty store at a usable shape, by `write` (and so
`delete`), `flush` and `compactFully`. Rust and Python refuse an unusable shape. -/
inductive Reachable : Store α β → Prop where
  /-- The empty store, at a usable shape. -/
  | empty {sh : Shape} : sh.Usable → Reachable (empty sh)
  /-- A write or a delete. -/
  | write {s : Store α β} (a : α) (v : Option β) : Reachable s → Reachable (write a v s)
  /-- A flush. -/
  | flush {s : Store α β} : Reachable s → Reachable (flush s)
  /-- A full compaction. -/
  | compactFully {s : Store α β} : Reachable s → Reachable (compactFully s)

/-- Every store the API builds is `Valid`. -/
theorem valid_of_reachable {s : Store α β} (h : Reachable s) : Valid s := by
  induction h with
  | empty hsh => exact valid_empty hsh
  | write a v _ ih => exact valid_write ih a v
  | flush _ ih => exact valid_flush ih
  | compactFully _ ih => exact valid_compactFully ih

/-- The usable-shape premise is satisfiable: the smallest usable shape. -/
example : (⟨1, 2, 1⟩ : Shape).Usable := by decide

end Store

end LSM

end AlgoDesign.Searching
