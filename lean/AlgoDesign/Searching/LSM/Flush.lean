/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.LSM.Compact

/-!
# LSM-tree: the store and its flush

The store's policy, a model of `lsm.rs` function for function: `Store.write` fills the memtable
and flushes it when full; `Store.flush` files it in front of level 0 and cascades every level over
its budget into the next. A flush keeps every `get` (`Store.preservesGet_flush`), so a write is
visible at once and disturbs no other key (`Store.get_write_self`, `Store.get_write_other`), and
so does `Store.compactFully`; the store's runs stay sorted and few (`Store.runsSorted_flush`,
`Store.fewRuns_flush`, `Store.runsSorted_write`, `Store.fewRuns_write`).
-/

@[expose] public section

namespace AlgoDesign.Searching

namespace LSM

variable {α β : Type} [LinearOrder α]

/-! ## The policy

* `write` puts one entry into the memtable, the newer winning, and flushes when the memtable
  reaches `capacity`. `write a none` is a delete.
* `flush` files the memtable as a sealed run in front of level 0; when level 0 reaches
  `level0Runs` runs it merges them into level 1 (`spill`), and `cascade` pushes each level over its
  budget into the next, adding a level below the deepest if needed.
* `pushInto` merges a run into a level's one run, collecting tombstones only when every level
  below is empty, and leaves an empty slot when the merge cancels out.
* `compactFully` flushes, merges every run into one, and collects its tombstones.

The cascade recurses on `fuel`, proved enough under `capacity ≥ 1` and `ratio ≥ 2`
(`cascadeFrom_enough`, `flush_fuel_add`). -/

theorem Shape.lt_budget {sh : Shape} (hc : 1 ≤ sh.capacity) (hr : 2 ≤ sh.ratio) (i : Nat) :
    i < sh.budget i :=
  calc i < 2 ^ i := Nat.lt_two_pow_self
    _ ≤ sh.ratio ^ i := Nat.pow_le_pow_left hr i
    _ ≤ sh.capacity * sh.ratio ^ i := Nat.le_mul_of_pos_left _ hc

namespace Store

/-- How many entries a list of runs holds. -/
def entries (rs : List (Run α β)) : Nat := (rs.map List.length).sum

/-- The level's first run is over the budget of level `i`. The cascade's test; Rust:
`level.first().is_some_and(|r| r.len() > self.budget(i))`. -/
def over (sh : Shape) (i : Nat) : List (Run α β) → Bool
  | [] => false
  | r :: _ => decide (sh.budget i < r.length)

/-- The empty store at shape `sh`. -/
def empty (sh : Shape) : Store α β := ⟨sh, [], []⟩

/-- A level holding the one run `r`, or an empty slot if `r` holds nothing. -/
def slot (r : Run α β) : List (Run α β) := if r.isEmpty then [] else [r]

/-- Merge `newer` into the level's run, newer winning a tied key, and collect tombstones if
nothing lies below (`nothingBelow`). A merge that cancels out leaves an empty slot. Rust:
`push_down`. -/
def pushInto (newer : Run α β) (level : List (Run α β)) (nothingBelow : Bool) :
    List (Run α β) :=
  slot (if nothingBelow then Run.dropTombstones (Run.mergeRuns newer (level.getLast?.getD []))
    else Run.mergeRuns newer (level.getLast?.getD []))

/-- `cascade`'s loop from level `i` down: a level over its budget gives up its run to the next,
a new level being added below the deepest if needed, and the level that received it is checked
next. `fuel` bounds the number of levels visited; `cascadeFrom_enough` says how much is enough. -/
def cascadeFrom (sh : Shape) : Nat → Nat → List (List (Run α β)) → List (List (Run α β))
  | 0, _, ls => ls
  | _ + 1, _, [] => []
  | fuel + 1, i, l :: rest =>
      if over sh i l then
        match rest with
        | [] => l.dropLast :: cascadeFrom sh fuel (i + 1) [pushInto (l.getLast?.getD []) [] true]
        | m :: post =>
            l.dropLast ::
              cascadeFrom sh fuel (i + 1)
                (pushInto (l.getLast?.getD []) m (post.all List.isEmpty) :: post)
      else l :: cascadeFrom sh fuel (i + 1) rest

/-- `cascade`: every level from 1 down that is over budget is pushed into the next. -/
def cascade (sh : Shape) (fuel : Nat) : List (List (Run α β)) → List (List (Run α β))
  | [] => []
  | l0 :: deeper => l0 :: cascadeFrom sh fuel 1 deeper

/-- Level 0's runs merged into one, each older run losing a tied key. -/
def mergeLevel0 : List (Run α β) → Run α β
  | [] => []
  | r :: rs => rs.foldl Run.mergeRuns r

/-- Level 0 over its run count: merge its runs and push the result into level 1, adding level 1
if there is none. Level 0 is left empty. -/
def spill (l0 : List (Run α β)) : List (List (Run α β)) → List (List (Run α β))
  | [] => [[], pushInto (mergeLevel0 l0) [] true]
  | l1 :: post => [] :: pushInto (mergeLevel0 l0) l1 (post.all List.isEmpty) :: post

/-- File a sealed run in front of level 0 (unless it is empty, which `flush` never passes), and if
that brings level 0 to its run count, spill it and cascade. -/
def fileRun (sh : Shape) (fuel : Nat) (fresh : Run α β) (l0 : List (Run α β))
    (deeper : List (List (Run α β))) : List (List (Run α β)) :=
  let l0' := if fresh.isEmpty then l0 else fresh :: l0
  if l0'.length < sh.level0Runs then l0' :: deeper else cascade sh fuel (spill l0' deeper)

/-- More levels than any cascade from this store can visit (`flush_fuel_add`). -/
def fuel (s : Store α β) : Nat := s.levels.length + (s.runs.map List.length).sum + 3

/-- `flush`: file the memtable, tombstones and all, as a sealed run in front of level 0, and push
down whatever that overfills. A no-op on an empty memtable. A flush drops no tombstone. -/
def flush (s : Store α β) : Store α β :=
  if s.memtable.isEmpty then s
  else { s with memtable := [],
                levels := fileRun s.shape s.fuel s.memtable (s.levels.headD []) s.levels.tail }

/-- `flush_if_full`. -/
def flushIfFull (s : Store α β) : Store α β :=
  if s.shape.capacity ≤ s.memtable.length then flush s else s

/-- `write` (`v = some _`) and `delete` (`v = none`): record the entry in the memtable, replacing
any entry for the same key, and flush if that fills it. -/
def write (a : α) (v : Option β) (s : Store α β) : Store α β :=
  flushIfFull { s with memtable := Run.mergeRuns [(a, v)] s.memtable }

/-- `delete`: a write of a tombstone. -/
def delete (a : α) (s : Store α β) : Store α β := write a none s

/-- `compact_fully`: flush, merge every run into one, oldest first and each newer run winning a
tied key, and collect its tombstones; the result is level 0's one run, or no level at all. -/
def compactFully (s : Store α β) : Store α β :=
  let s' := flush s
  let cleaned := Run.dropTombstones
    (s'.levels.flatten.reverse.foldl (fun older newer => Run.mergeRuns newer older) [])
  { s' with levels := if cleaned.isEmpty then [] else [[cleaned]] }

omit [LinearOrder α] in
@[simp] theorem shape_empty (sh : Shape) : (empty sh : Store α β).shape = sh := rfl

@[simp] theorem shape_flush (s : Store α β) : (flush s).shape = s.shape := by
  unfold flush; split <;> rfl

@[simp] theorem shape_flushIfFull (s : Store α β) : (flushIfFull s).shape = s.shape := by
  unfold flushIfFull; split <;> simp

@[simp] theorem shape_write (a : α) (v : Option β) (s : Store α β) :
    (write a v s).shape = s.shape := by
  simp [write]

@[simp] theorem shape_compactFully (s : Store α β) : (compactFully s).shape = s.shape := by
  simp [compactFully]

/-- **Nothing until written:** the empty store answers nothing for every key. -/
theorem get_empty (sh : Shape) (a : α) : get a (empty sh : Store α β) = none := rfl

theorem runsSorted_empty (sh : Shape) : RunsSorted (empty sh : Store α β) := by
  simp [RunsSorted, empty]

omit [LinearOrder α] in
theorem fewRuns_empty (sh : Shape) : FewRuns (empty sh : Store α β) := by
  simp [FewRuns, empty]

theorem eachSorted_runs {s : Store α β} (h : RunsSorted s) : LSM.EachSorted s.runs := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.1
  · exact h.2 r hr

omit [LinearOrder α] in
/-- Every slot below is empty exactly when nothing lies below. -/
theorem all_isEmpty_iff {post : List (List (Run α β))} :
    post.all List.isEmpty = true ↔ post.flatten = [] := by
  simp [List.all_eq_true, List.flatten_eq_nil_iff]

omit [LinearOrder α] in
theorem mem_slot {r q : Run α β} (h : q ∈ slot r) : q = r ∧ r ≠ [] := by
  unfold slot at h
  split_ifs at h with he
  · simp at h
  · exact ⟨List.mem_singleton.mp h, fun h' => by simp [h'] at he⟩

omit [LinearOrder α] in
theorem length_slot_le (r : Run α β) : (slot r).length ≤ 1 := by
  unfold slot; split_ifs <;> simp

/-- An empty slot answers as the empty run it replaces: nothing. -/
theorem preservesLookup_slot (r : Run α β) (t : List (Run α β)) :
    PreservesLookup (r :: t) (slot r ++ t) := by
  unfold slot
  split_ifs with he
  · rw [List.isEmpty_iff.mp he]
    exact fun a => (preservesLookup_nil_cons t a).symm
  · exact PreservesLookup.rfl

omit [LinearOrder α] in
theorem ne_nil_of_mem_slot {r q : Run α β} (h : q ∈ slot r) : q ≠ [] :=
  (mem_slot h).1 ▸ (mem_slot h).2

theorem ne_nil_of_mem_pushInto {newer : Run α β} {m : List (Run α β)} {b : Bool} {q : Run α β}
    (h : q ∈ pushInto newer m b) : q ≠ [] :=
  ne_nil_of_mem_slot h

theorem length_pushInto_le (newer : Run α β) (m : List (Run α β)) (b : Bool) :
    (pushInto newer m b).length ≤ 1 :=
  length_slot_le _

theorem runsSorted_slot {r : Run α β} {t : List (Run α β)} (hr : Run.Sorted r)
    (ht : LSM.EachSorted t) :
    LSM.EachSorted (slot r ++ t) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact (mem_slot hq).1 ▸ hr
  · exact ht q hq

/-- **A push loses nothing a client can see.** Merging `newer` into the level below keeps every
answer (`preservesLookup_mergeAt`); collecting its tombstones when nothing lies below keeps every
value (`preservesGet_dropBottom`); and an empty slot answers as the empty run would. -/
theorem preservesGet_pushInto {newer : Run α β} {m : List (Run α β)}
    {post : List (List (Run α β))} (hm : m.length ≤ 1) (hn : Run.Sorted newer)
    (hv : LSM.EachSorted (m ++ post.flatten)) :
    PreservesGet (newer :: (m ++ post.flatten))
        (pushInto newer m (post.all List.isEmpty) ++ post.flatten) ∧
      LSM.EachSorted (pushInto newer m (post.all List.isEmpty) ++ post.flatten) := by
  have ho : Run.Sorted (m.getLast?.getD []) ∧
      PreservesLookup (newer :: (m ++ post.flatten))
        (newer :: m.getLast?.getD [] :: post.flatten) ∧ LSM.EachSorted post.flatten := by
    match m, hm with
    | [], _ =>
        exact ⟨Run.sorted_nil, fun a => rfl, by simpa using hv⟩
    | [o], _ =>
        exact ⟨hv o (by simp), PreservesLookup.rfl,
          fun q hq => hv q (List.mem_append_right _ hq)⟩
  obtain ⟨ho, hl, hp⟩ := ho
  have hv' : LSM.EachSorted (newer :: m.getLast?.getD [] :: post.flatten) := by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact hn
    · exact ho
    · exact hp q hq
  have hmerge : PreservesLookup (newer :: m.getLast?.getD [] :: post.flatten)
      (Run.mergeRuns newer (m.getLast?.getD []) :: post.flatten) :=
    preservesLookup_mergeAt 0 hv'
  have hs := Run.sorted_mergeRuns hn ho
  cases hpost : post.all List.isEmpty
  · simp only [pushInto, Bool.false_eq_true, ↓reduceIte]
    exact ⟨((hl.trans hmerge).trans (preservesLookup_slot _ _)).preservesGet, runsSorted_slot hs hp⟩
  · have hnil : post.flatten = [] := all_isEmpty_iff.mp hpost
    simp only [pushInto, ↓reduceIte]
    rw [hnil] at hl hmerge ⊢
    refine ⟨((hl.trans hmerge).preservesGet.trans ?_).trans
      (preservesLookup_slot _ _).preservesGet,
      runsSorted_slot (Run.sorted_dropTombstones hs) (by simp)⟩
    exact preservesGet_dropBottom (t := [Run.mergeRuns newer (m.getLast?.getD [])])
      (by simpa using hs)

/-- **The cascade loses nothing a client can see**, keeps every run sorted and every level at one
run at most — for any `fuel`. -/
theorem cascadeFrom_spec (sh : Shape) : ∀ (fuel i : Nat) (ls : List (List (Run α β))),
    (∀ l ∈ ls, l.length ≤ 1) → LSM.EachSorted ls.flatten →
    PreservesGet ls.flatten (cascadeFrom sh fuel i ls).flatten ∧
      (∀ l ∈ cascadeFrom sh fuel i ls, l.length ≤ 1) ∧
        LSM.EachSorted (cascadeFrom sh fuel i ls).flatten
  | 0, _, ls, h1, hv => ⟨PreservesGet.rfl, h1, hv⟩
  | _ + 1, _, [], _, _ => ⟨PreservesGet.rfl, by simp [cascadeFrom], by simp [cascadeFrom]⟩
  | fuel + 1, i, l :: rest, h1, hv => by
      have hl : l.length ≤ 1 := h1 l (by simp)
      have hrest : ∀ l' ∈ rest, l'.length ≤ 1 := fun l' hl' => h1 l' (by simp [hl'])
      have hvl : LSM.EachSorted l := fun q hq => hv q (by simp [hq])
      have hvr : LSM.EachSorted rest.flatten := fun q hq => hv q (by
        simp only [List.flatten_cons]; exact List.mem_append_right _ hq)
      by_cases ho : over sh i l = true
      · -- Over budget, so the level holds exactly one run.
        obtain ⟨r, rfl⟩ : ∃ r, l = [r] := by
          match l, hl, ho with
          | [r], _, _ => exact ⟨r, rfl⟩
        have hr : Run.Sorted r := hvl r (by simp)
        simp only [cascadeFrom, ho, ↓reduceIte]
        match rest, hrest, hvr with
        | [], _, _ =>
            have hp := preservesGet_pushInto (newer := r) (m := []) (post := [])
              (by simp) hr (by simp)
            have ih := cascadeFrom_spec sh fuel (i + 1) [pushInto r [] true]
              (by simp [length_pushInto_le]) (by simpa using hp.2)
            refine ⟨?_, ?_, ?_⟩
            · simpa using hp.1.trans (by simpa using ih.1)
            · intro l' hl'
              rcases List.mem_cons.mp hl' with rfl | hl'
              · simp
              · exact ih.2.1 l' hl'
            · simpa using ih.2.2
        | m :: post, hrest', hvr' =>
            have hm : m.length ≤ 1 := hrest' m (by simp)
            have hp := preservesGet_pushInto (newer := r) (m := m) (post := post) hm hr
              (by simpa using hvr')
            have ih := cascadeFrom_spec sh fuel (i + 1)
              (pushInto r m (post.all List.isEmpty) :: post)
              (by
                intro l' hl'
                rcases List.mem_cons.mp hl' with rfl | hl'
                · exact length_slot_le _
                · exact hrest' l' (by simp [hl']))
              (by simpa using hp.2)
            refine ⟨?_, ?_, ?_⟩
            · simpa using hp.1.trans (by simpa using ih.1)
            · intro l' hl'
              rcases List.mem_cons.mp hl' with rfl | hl'
              · simp
              · exact ih.2.1 l' hl'
            · simpa using ih.2.2
      · have ih := cascadeFrom_spec sh fuel (i + 1) rest hrest hvr
        simp only [cascadeFrom, ho, ↓reduceIte, Bool.false_eq_true]
        refine ⟨?_, ?_, ?_⟩
        · simpa using PreservesGet.append_left l ih.1
        · intro l' hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact hl
          · exact ih.2.1 l' hl'
        · intro q hq
          simp only [List.flatten_cons, List.mem_append] at hq
          rcases hq with hq | hq
          · exact hvl q hq
          · exact ih.2.2 q hq

/-- Level 0's merge answers as level 0 did. -/
theorem preservesLookup_mergeLevel0 : ∀ {l0 : List (Run α β)}, LSM.EachSorted l0 →
    PreservesLookup l0 [mergeLevel0 l0] ∧ Run.Sorted (mergeLevel0 l0)
  | [], _ => ⟨fun _ => rfl, Run.sorted_nil⟩
  | r :: rs, hv => preservesLookup_foldl_mergeRuns rs (hv r (by simp))
      (fun q hq => hv q (List.mem_cons_of_mem _ hq))

/-- **Filing a sealed run, and whatever spill and cascade it sets off, loses nothing a client
can see** and keeps the levels' shape. -/
theorem fileRun_spec (sh : Shape) (fuel : Nat) {fresh : Run α β} {l0 : List (Run α β)}
    {deeper : List (List (Run α β))} (hf : Run.Sorted fresh)
    (hv : LSM.EachSorted (l0 ++ deeper.flatten))
    (hd : ∀ l ∈ deeper, l.length ≤ 1) :
    PreservesGet (fresh :: (l0 ++ deeper.flatten)) (fileRun sh fuel fresh l0 deeper).flatten ∧
      LSM.EachSorted (fileRun sh fuel fresh l0 deeper).flatten ∧
      ((fileRun sh fuel fresh l0 deeper).headD []).length ≤ sh.level0Runs ∧
      ∀ l ∈ (fileRun sh fuel fresh l0 deeper).tail, l.length ≤ 1 := by
  -- Filing: the fresh run in front of level 0, or nothing if it is empty.
  set l0' := if fresh.isEmpty then l0 else fresh :: l0 with hl0'
  have hfile : PreservesLookup (fresh :: (l0 ++ deeper.flatten)) (l0' ++ deeper.flatten) ∧
      LSM.EachSorted (l0' ++ deeper.flatten) := by
    cases hfe : fresh.isEmpty
    · simp only [hl0', hfe, Bool.false_eq_true, ↓reduceIte, List.cons_append]
      refine ⟨PreservesLookup.rfl, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hf
      · exact hv q hq
    · have : fresh = [] := List.isEmpty_iff.mp hfe
      subst this
      simp only [hl0', hfe, ↓reduceIte]
      exact ⟨fun _ => rfl, hv⟩
  obtain ⟨hfl, hfv⟩ := hfile
  have hvl0 : LSM.EachSorted l0' := fun q hq => hfv q (List.mem_append_left _ hq)
  have hvd : LSM.EachSorted deeper.flatten := fun q hq => hfv q (List.mem_append_right _ hq)
  unfold fileRun
  simp only [← hl0']
  split_ifs with hle
  · refine ⟨hfl.preservesGet.trans (by simp only [List.flatten_cons]; exact PreservesGet.rfl),
      by simpa using hfv, by simpa using Nat.le_of_lt hle, ?_⟩
    simpa using hd
  · -- Spill level 0 into level 1, then cascade from level 1.
    obtain ⟨hm0, hs0⟩ := preservesLookup_mergeLevel0 hvl0
    have hstep : PreservesGet (fresh :: (l0 ++ deeper.flatten))
        (mergeLevel0 l0' :: deeper.flatten) :=
      (hfl.trans (by simpa using hm0.append_right deeper.flatten)).preservesGet
    -- The level list after the spill, below level 0.
    obtain ⟨rest, hrest, hpr, h1, hvr⟩ : ∃ rest, spill l0' deeper = [] :: rest ∧
        PreservesGet (mergeLevel0 l0' :: deeper.flatten) rest.flatten ∧
        (∀ l ∈ rest, l.length ≤ 1) ∧ LSM.EachSorted rest.flatten := by
      match deeper, hd, hvd with
      | [], _, _ =>
          have hp := preservesGet_pushInto (newer := mergeLevel0 l0') (m := []) (post := [])
            (by simp) hs0 (by simp)
          exact ⟨[pushInto (mergeLevel0 l0') [] true], rfl, by simpa using hp.1,
            by simp [length_pushInto_le], by simpa using hp.2⟩
      | m :: post, hd', hvd' =>
          have hm : m.length ≤ 1 := hd' m (by simp)
          have hp := preservesGet_pushInto (newer := mergeLevel0 l0') (m := m) (post := post)
            hm hs0 (by simpa using hvd')
          refine ⟨pushInto (mergeLevel0 l0') m (post.all List.isEmpty) :: post, rfl,
            by simpa using hp.1, ?_, by simpa using hp.2⟩
          intro l' hl'
          rcases List.mem_cons.mp hl' with rfl | hl'
          · exact length_slot_le _
          · exact hd' l' (by simp [hl'])
    have hc := cascadeFrom_spec sh fuel 1 rest h1 hvr
    rw [hrest]
    simp only [cascade, List.flatten_cons, List.nil_append, List.headD_cons, List.length_nil,
      Nat.zero_le, List.tail_cons, true_and]
    exact ⟨hstep.trans (hpr.trans hc.1), hc.2.2, hc.2.1⟩

omit [LinearOrder α] in
theorem headD_append_flatten_tail (ls : List (List (Run α β))) :
    ls.headD [] ++ ls.tail.flatten = ls.flatten := by
  cases ls <;> simp

/-- **A flush loses nothing a client can see**: every key's `get` is what it was, whatever the
flush spilled, cascaded or collected. -/
theorem preservesGet_flush {s : Store α β} (h : RunsSorted s) (hf : FewRuns s) :
    PreservesGet s.runs (flush s).runs := by
  unfold flush
  cases he : s.memtable.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hfr := fileRun_spec s.shape s.fuel h.1 (l0 := s.levels.headD []) (deeper := s.levels.tail)
      (by rw [headD_append_flatten_tail]; exact h.2) hf.2
    rw [headD_append_flatten_tail] at hfr
    exact hfr.1.trans (preservesLookup_nil_cons _).preservesGet
  · simp only [↓reduceIte]
    exact PreservesGet.rfl

/-- A flush leaves the memtable empty. -/
theorem memtable_flush (s : Store α β) : (flush s).memtable = [] := by
  unfold flush
  cases he : s.memtable.isEmpty
  · rfl
  · simpa using he

/-- **A flush keeps every run sorted.** -/
theorem runsSorted_flush {s : Store α β} (h : RunsSorted s) (hf : FewRuns s) :
    RunsSorted (flush s) := by
  unfold flush
  cases he : s.memtable.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hfr := fileRun_spec s.shape s.fuel h.1 (l0 := s.levels.headD [])
      (deeper := s.levels.tail) (by rw [headD_append_flatten_tail]; exact h.2) hf.2
    exact ⟨Run.sorted_nil, hfr.2.1⟩
  · simp only [↓reduceIte]
    exact h

/-- **A flush keeps the batches few**: level 0 within its run count, every deeper level at one
run at most. -/
theorem fewRuns_flush {s : Store α β} (h : RunsSorted s) (hf : FewRuns s) :
    FewRuns (flush s) := by
  unfold flush
  cases he : s.memtable.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hfr := fileRun_spec s.shape s.fuel h.1 (l0 := s.levels.headD [])
      (deeper := s.levels.tail) (by rw [headD_append_flatten_tail]; exact h.2) hf.2
    exact ⟨hfr.2.2.1, hfr.2.2.2⟩
  · simp only [↓reduceIte]
    exact hf

theorem preservesGet_flushIfFull {s : Store α β} (h : RunsSorted s)
    (hf : FewRuns s) : PreservesGet s.runs (flushIfFull s).runs := by
  unfold flushIfFull
  split_ifs
  · exact preservesGet_flush h hf
  · exact PreservesGet.rfl

theorem runsSorted_flushIfFull {s : Store α β} (h : RunsSorted s)
    (hf : FewRuns s) : RunsSorted (flushIfFull s) := by
  unfold flushIfFull
  split_ifs
  · exact runsSorted_flush h hf
  · exact h

theorem fewRuns_flushIfFull {s : Store α β} (h : RunsSorted s)
    (hf : FewRuns s) : FewRuns (flushIfFull s) := by
  unfold flushIfFull
  split_ifs
  · exact fewRuns_flush h hf
  · exact hf

/-- The memtable after a write is still sorted. -/
theorem runsSorted_write_memtable {s : Store α β} (h : RunsSorted s) (a : α) (v : Option β) :
    RunsSorted { s with memtable := Run.mergeRuns [(a, v)] s.memtable } :=
  ⟨Run.sorted_mergeRuns (Run.sorted_singleton _) h.1, h.2⟩

/-- **A write keeps every run sorted**, flush or no flush. -/
theorem runsSorted_write {s : Store α β} (h : RunsSorted s) (hf : FewRuns s)
    (a : α) (v : Option β) : RunsSorted (write a v s) :=
  runsSorted_flushIfFull (runsSorted_write_memtable h a v) hf

/-- **A write keeps the batches few**, flush or no flush. -/
theorem fewRuns_write {s : Store α β} (h : RunsSorted s) (hf : FewRuns s)
    (a : α) (v : Option β) : FewRuns (write a v s) :=
  fewRuns_flushIfFull (runsSorted_write_memtable h a v) hf

/-- **A write is visible at once**, through the memtable or, if it filled the memtable, through
the flush it set off. With `v = none` this is a delete: `get` answers "no value". -/
theorem get_write_self {s : Store α β} (h : RunsSorted s) (hf : FewRuns s) (a : α)
    (v : Option β) : get a (write a v s) = v := by
  have hp := preservesGet_flushIfFull (runsSorted_write_memtable h a v) hf a
  simp only [get_eq, write] at hp ⊢
  rw [← hp]
  simp only [LSM.get, runs, lookup_cons,
    Run.lookup_mergeRuns a (Run.sorted_singleton (a, v)), Run.lookup_cons, ↓reduceIte]
  simp

/-- **A write disturbs no other key**, even when it sets off a flush, a spill and a cascade. -/
theorem get_write_other {s : Store α β} (h : RunsSorted s) (hf : FewRuns s)
    {a b : α} (hab : a ≠ b) (v : Option β) : get b (write a v s) = get b s := by
  have hp := preservesGet_flushIfFull (runsSorted_write_memtable h a v) hf b
  simp only [get_eq, write] at hp ⊢
  rw [← hp]
  simp only [LSM.get, runs, lookup_cons,
    Run.lookup_mergeRuns b (Run.sorted_singleton (a, v)), Run.lookup_cons, hab, ↓reduceIte,
    Run.lookup_nil, Option.none_or]

/-- **A delete removes the key**: `get` answers nothing, flush or no flush. -/
theorem get_delete_self {s : Store α β} (h : RunsSorted s) (hf : FewRuns s) (a : α) :
    get a (delete a s) = none :=
  get_write_self h hf a none

/-- **A delete disturbs no other key.** -/
theorem get_delete_other {s : Store α β} (h : RunsSorted s) (hf : FewRuns s) {a b : α}
    (hab : a ≠ b) : get b (delete a s) = get b s :=
  get_write_other h hf hab none

/-- **A full compaction loses nothing a client can see**, though it collects every tombstone. -/
theorem preservesGet_compactFully {s : Store α β} (h : RunsSorted s)
    (hfew : FewRuns s) :
    PreservesGet s.runs (compactFully s).runs ∧ LSM.EachSorted (compactFully s).runs := by
  have hs := runsSorted_flush h hfew
  have hmt := memtable_flush s
  have hf := preservesGet_flush h hfew
  set s' := flush s with hs'
  have hv : LSM.EachSorted s'.levels.flatten := hs.2
  have hfold : s'.levels.flatten.reverse.foldl (fun older newer => Run.mergeRuns newer older) []
      = s'.levels.flatten.foldr Run.mergeRuns [] := by
    rw [List.foldl_reverse]
  have hsorted := sorted_foldr_mergeRuns _ hv
  have hsd := Run.sorted_dropTombstones hsorted
  refine ⟨hf.trans fun a => ?_, ?_⟩
  · have hl := lookup_foldr_mergeRuns a _ hv
    have hj := Run.lookup_dropTombstones_join a hsorted
    simp only [compactFully, ← hs', hfold, LSM.get, runs, hmt]
    split_ifs with he
    · have : Run.dropTombstones (s'.levels.flatten.foldr Run.mergeRuns []) = [] :=
        List.isEmpty_iff.mp he
      rw [this] at hj
      change (LSM.lookup a s'.levels.flatten).join = (none : Option (Option β)).join
      rw [← hl]
      simpa using hj.symm
    · change (LSM.lookup a s'.levels.flatten).join =
        (LSM.lookup a [Run.dropTombstones (s'.levels.flatten.foldr Run.mergeRuns [])]).join
      rw [lookup_cons, lookup_nil, Option.or_none, hj, hl]
  · intro q hq
    simp only [compactFully, ← hs', hfold, runs, diskRuns, hmt] at hq
    split_ifs at hq
    · simp only [List.flatten_nil, List.mem_singleton] at hq
      subst hq; exact Run.sorted_nil
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact Run.sorted_nil
      · exact hsd

/-- **A full compaction does its job:** it leaves the memtable empty and at most one run on disk. -/
theorem compactFully_one_run (s : Store α β) :
    (compactFully s).memtable = [] ∧ (compactFully s).diskRuns.length ≤ 1 := by
  refine ⟨memtable_flush s, ?_⟩
  simp only [compactFully]
  split <;> simp

end Store

end LSM

end AlgoDesign.Searching
