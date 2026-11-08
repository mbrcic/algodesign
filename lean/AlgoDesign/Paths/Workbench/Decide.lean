/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Workbench.Spec
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Perm.Subperm

/-! # The design project's contract: deciding its pieces on one trip

Each piece of the contract asks something of every town and every start and goal. On one town,
one start, one goal and one candidate's answer, each piece is a claim about that answer alone,
and it decides, so `decide` judges small towns. They are the pieces the Python judge checks, one
function each (the book's design-run bench, `bench.py`): `RealTripOn` is `is_real_trip` with
`is_never_flat`, `NoneQuickerOn` `is_none_quicker`, and `SaysNoneOn` `is_says_none`. Each `Ops`
piece is its one-trip piece on every well-formed town (`Ops.realTrip_iff` and the rest).

"No trip is quicker" and "there is none" speak of every trip, and a trip may pass the same place
at the same level more than once. Such a trip can be cut short: leave out what it rode between two
visits of one state, and what is left is a trip with the same ends, never flat, and no slower,
since no step takes fewer than no minutes (`shorten`). A trip that passes no state twice passes at
most as many states as there are (`allStates`), so every question about all trips is one about
the trips of at most that many steps, which `tripsFrom` lists (`exists_short`). -/

@[expose] public section

namespace AlgoDesign.Paths.Workbench

namespace Town

/-! ## Single trips, decided -/

variable (T : Town)

instance : Decidable T.WellFormed := by
  unfold WellFormed; infer_instance

instance (s g : ℕ) (t : List Step) : Decidable (T.IsTrip s g t) := by
  unfold IsTrip; infer_instance

instance (s : ℕ) (t : List Step) : Decidable (T.NeverFlat s t) := by
  unfold NeverFlat; infer_instance

/-- The steps a trip can take anywhere: a charging stop, or a ride to where a street leads. -/
def steps : List Step := .charge :: T.streets.map fun s => .ride s.target

/-- Every list of at most `k` steps that can be taken, one after another, from `x`. -/
def tripsFrom : ℕ → State → List (List Step)
  | 0, _ => [[]]
  | k + 1, x => [] :: T.steps.flatMap fun st =>
      match T.next x st with
      | some y => (tripsFrom k y).map (st :: ·)
      | none => []

/-- The states a trip from `x` can pass: a place it starts at or a street leads to, and a level
from empty to full. -/
def allStates (x : State) : List State :=
  (x.place :: T.streets.map Street.target).flatMap fun p =>
    (List.range (T.full + 1)).map fun l : ℕ => (⟨p, (l : ℤ)⟩ : State)

/-! ## A trip, step by step -/

variable {T}

theorem passes_cons {x : State} {st : Step} {r : List Step} {xs : List State} :
    T.passes x (st :: r) = some xs ↔
      ∃ y ys, T.next x st = some y ∧ T.passes y r = some ys ∧ xs = x :: ys := by
  simp only [passes, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨y, hy, ys, hys, rfl⟩
    exact ⟨y, ys, hy, hys, rfl⟩
  · rintro ⟨y, ys, hy, hys, rfl⟩
    exact ⟨y, hy, ys, hys, rfl⟩

/-- A trip passes its first state first. -/
theorem head_of_passes {x : State} {t : List Step} {xs : List State}
    (h : T.passes x t = some xs) : ∃ ys, xs = x :: ys := by
  cases t with
  | nil => simp only [passes, Option.some.injEq] at h; exact ⟨[], h.symm⟩
  | cons st r =>
    obtain ⟨_, ys, -, -, rfl⟩ := passes_cons.1 h
    exact ⟨ys, rfl⟩

/-- A trip of `k` steps passes `k + 1` states. -/
theorem length_passes {x : State} {t : List Step} {xs : List State}
    (h : T.passes x t = some xs) : xs.length = t.length + 1 := by
  induction t generalizing x xs with
  | nil => simp only [passes, Option.some.injEq] at h; simp [← h]
  | cons st r ih =>
    obtain ⟨y, ys, -, hys, rfl⟩ := passes_cons.1 h
    simp [ih hys]

theorem minutesFrom_cons {x y : State} {st : Step} {r : List Step} (h : T.next x st = some y) :
    T.minutesFrom x (st :: r) = T.stepMinutes x st + T.minutesFrom y r := by
  simp [minutesFrom, h]

/-- A step ends at most at full, where the bike stood or where a street leads, and it is one of
`steps`. -/
theorem next_spec {x y : State} {st : Step} (h : T.next x st = some y) :
    y.level ≤ T.full ∧ (y.place = x.place ∨ y.place ∈ T.streets.map Street.target) ∧
      st ∈ T.steps := by
  cases st with
  | ride q =>
    simp only [next, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    have hp := List.find?_some hs
    simp only [decide_eq_true_eq] at hp
    have hm := List.mem_of_find?_eq_some hs
    refine ⟨Int.min_le_left _ _, Or.inr (List.mem_map.2 ⟨s, hm, hp.2⟩), ?_⟩
    exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨s, hm, by rw [hp.2]⟩)
  | charge =>
    simp only [next] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨Int.min_le_left _ _, Or.inl rfl, List.mem_cons_self⟩

/-- Every state a trip passes is at most full, at the start place or where a street leads. -/
theorem passes_within {x : State} {t : List Step} {xs : List State}
    (h : T.passes x t = some xs) (hx : x.level ≤ T.full) :
    ∀ z ∈ xs, z.level ≤ T.full ∧ z.place ∈ x.place :: T.streets.map Street.target := by
  induction t generalizing x xs with
  | nil =>
    simp only [passes, Option.some.injEq] at h
    subst h
    simpa using hx
  | cons st r ih =>
    obtain ⟨y, ys, hy, hys, rfl⟩ := passes_cons.1 h
    obtain ⟨hyl, hyp, -⟩ := next_spec hy
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨hx, List.mem_cons_self⟩
    · obtain ⟨hzl, hzp⟩ := ih hys hyl z hz
      refine ⟨hzl, ?_⟩
      rcases List.mem_cons.1 hzp with hzp | hzp
      · rw [hzp]
        rcases hyp with hyp | hyp
        · rw [hyp]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hyp
      · exact List.mem_cons_of_mem _ hzp

/-- A state a trip passes that is never flat and at most full is one of `allStates`. -/
theorem mem_allStates {x z : State}
    (h : z.level ≤ T.full ∧ z.place ∈ x.place :: T.streets.map Street.target)
    (h0 : 0 ≤ z.level) : z ∈ T.allStates x := by
  refine List.mem_flatMap.2 ⟨z.place, h.2, List.mem_map.2 ⟨z.level.toNat, ?_, ?_⟩⟩
  · have := h.1
    exact List.mem_range.2 (by omega : z.level.toNat < T.full + 1)
  · rw [Int.toNat_of_nonneg h0]

/-- Every list of at most `k` steps that can be taken from `x` is in `tripsFrom k x`. -/
theorem mem_tripsFrom {k : ℕ} {x : State} {t : List Step} {xs : List State}
    (h : T.passes x t = some xs) (hk : t.length ≤ k) : t ∈ T.tripsFrom k x := by
  induction t generalizing k x xs with
  | nil => cases k <;> simp [tripsFrom]
  | cons st r ih =>
    obtain ⟨y, ys, hy, hys, rfl⟩ := passes_cons.1 h
    cases k with
    | zero => simp at hk
    | succ k =>
      refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨st, (next_spec hy).2.2, ?_⟩)
      rw [hy]
      exact List.mem_map_of_mem (ih hys (by simpa using hk))

/-! ## Cutting a trip short -/

theorem getLast?_of_suffix {l₁ l₂ : List State} (h : l₁ <:+ l₂) (hne : l₁ ≠ []) :
    l₁.getLast? = l₂.getLast? := by
  obtain ⟨c, rfl⟩ := h
  exact (List.getLast?_append_of_ne_nil c hne).symm

/-- A trip from `y` that passes `x` goes on from `x`: what is left after it passes `x` is a trip
from `x` with the same end, and no slower. -/
theorem cut {x y : State} {r : List Step} {ys : List State} (h : T.passes y r = some ys)
    (hx : x ∈ ys) :
    ∃ b zs, T.passes x b = some zs ∧ zs <:+ ys ∧ T.minutesFrom x b ≤ T.minutesFrom y r := by
  induction r generalizing y ys with
  | nil =>
    simp only [passes, Option.some.injEq] at h
    subst h
    rw [List.mem_singleton.1 hx]
    exact ⟨[], [y], rfl, List.suffix_refl _, le_refl _⟩
  | cons st r ih =>
    obtain ⟨z, zs₂, hz, hzs, rfl⟩ := passes_cons.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨st :: r, x :: zs₂, h, List.suffix_refl _, le_refl _⟩
    · obtain ⟨b, zs, hb, hsuf, hm⟩ := ih hzs hx
      refine ⟨b, zs, hb, hsuf.trans (List.suffix_cons _ _), ?_⟩
      rw [minutesFrom_cons hz]
      omega

/-- **A trip cut short.** Every trip from `x` has one that passes no state twice, passes only
states the first passes, ends where it ends, and is no slower. -/
theorem shorten {x : State} {t : List Step} {xs : List State} (h : T.passes x t = some xs) :
    ∃ t' xs', T.passes x t' = some xs' ∧ xs'.Nodup ∧ xs' ⊆ xs ∧
      xs'.getLast? = xs.getLast? ∧ T.minutesFrom x t' ≤ T.minutesFrom x t := by
  induction t generalizing x xs with
  | nil => exact ⟨[], xs, h, by simp only [passes, Option.some.injEq] at h; simp [← h],
      List.Subset.refl _, rfl, le_refl _⟩
  | cons st r ih =>
    obtain ⟨y, ys, hy, hys, rfl⟩ := passes_cons.1 h
    obtain ⟨r', ys', hp', hnd, hsub, hlast, hmin⟩ := ih hys
    obtain ⟨ys₀, hys₀⟩ := head_of_passes hys
    obtain ⟨ys₀', hys₀'⟩ := head_of_passes hp'
    have hcons : (x :: ys).getLast? = ys.getLast? := by rw [hys₀, List.getLast?_cons_cons]
    rw [minutesFrom_cons hy]
    by_cases hx : x ∈ ys'
    · obtain ⟨b, zs, hb, hsuf, hbm⟩ := cut hp' hx
      obtain ⟨zs₀, hzs₀⟩ := head_of_passes hb
      refine ⟨b, zs, hb, hnd.sublist hsuf.sublist,
        (hsuf.subset.trans hsub).trans (List.subset_cons_self _ _), ?_, by omega⟩
      rw [getLast?_of_suffix hsuf (by simp [hzs₀]), hlast, hcons]
    · refine ⟨st :: r', x :: ys', passes_cons.2 ⟨y, ys', hy, hp', rfl⟩,
        List.nodup_cons.2 ⟨hx, hnd⟩, List.cons_subset_cons _ hsub, ?_, ?_⟩
      · rw [hcons, hys₀', List.getLast?_cons_cons, ← hys₀', hlast]
      · rw [minutesFrom_cons hy]
        omega

/-- **Every trip has a short one.** A trip from `s` to `g` that never runs flat has one among the
trips of at most as many steps as there are states, with the same ends, never flat, and no
slower. -/
theorem exists_short {s g : ℕ} {u : List Step} (h : T.IsTrip s g u) (hf : T.NeverFlat s u) :
    ∃ u' ∈ T.tripsFrom (T.allStates (T.startAt s)).length (T.startAt s),
      T.IsTrip s g u' ∧ T.NeverFlat s u' ∧ T.tripMinutes s u' ≤ T.tripMinutes s u := by
  obtain ⟨xs, hxs, hg⟩ := h
  obtain ⟨u', xs', hp, hnd, hsub, hlast, hmin⟩ := shorten hxs
  have hflat : ∀ z ∈ xs', 0 ≤ z.level := fun z hz => hf xs hxs z (hsub hz)
  have hin : xs' ⊆ T.allStates (T.startAt s) := fun z hz =>
    mem_allStates (passes_within hp (by simp [startAt]) z hz) (hflat z hz)
  have hlen := (List.subperm_of_subset hnd hin).length_le
  have hl := length_passes hp
  refine ⟨u', mem_tripsFrom hp (by omega), ⟨xs', hp, by rw [hlast]; exact hg⟩, ?_, hmin⟩
  intro ys hys
  rw [Option.mem_def, hp, Option.some.injEq] at hys
  subst hys
  exact hflat

variable (T)

theorem exists_trip_iff (s g : ℕ) :
    (∃ t, T.IsTrip s g t ∧ T.NeverFlat s t) ↔
      ∃ t ∈ T.tripsFrom (T.allStates (T.startAt s)).length (T.startAt s),
        T.IsTrip s g t ∧ T.NeverFlat s t :=
  ⟨fun ⟨_, h, hf⟩ => (exists_short h hf).elim fun u ⟨hu, h', hf', _⟩ => ⟨u, hu, h', hf'⟩,
    fun ⟨t, _, h⟩ => ⟨t, h⟩⟩

theorem noneQuicker_iff (s g m : ℕ) :
    (∀ u, T.IsTrip s g u → T.NeverFlat s u → m ≤ T.tripMinutes s u) ↔
      ∀ u ∈ T.tripsFrom (T.allStates (T.startAt s)).length (T.startAt s),
        T.IsTrip s g u → T.NeverFlat s u → m ≤ T.tripMinutes s u := by
  refine ⟨fun h u _ => h u, fun h u hu hf => ?_⟩
  obtain ⟨u', hu', h', hf', hm⟩ := exists_short hu hf
  exact le_trans (h u' hu' h' hf') hm

end Town

/-! ## The pieces on one trip -/

/-- **A real trip**, on one town, start and goal: a trip it gives goes from the start to the goal
and never runs the battery flat. -/
def RealTripOn (T : Town) (s g : ℕ) (ans : Option (List Step)) : Prop :=
  ∀ t ∈ ans, T.IsTrip s g t ∧ T.NeverFlat s t

/-- **None quicker**, on one town, start and goal: no trip that never runs flat is quicker than
the one it gives. -/
def NoneQuickerOn (T : Town) (s g : ℕ) (ans : Option (List Step)) : Prop :=
  ∀ t ∈ ans, ∀ u, T.IsTrip s g u → T.NeverFlat s u → T.tripMinutes s t ≤ T.tripMinutes s u

/-- **Says none**, on one town, start and goal: nothing exactly when no trip never runs flat. -/
def SaysNoneOn (T : Town) (s g : ℕ) (ans : Option (List Step)) : Prop :=
  ans = none ↔ ¬ ∃ t, T.IsTrip s g t ∧ T.NeverFlat s t

instance (T : Town) (s g : ℕ) (ans : Option (List Step)) : Decidable (RealTripOn T s g ans) := by
  unfold RealTripOn; infer_instance

instance (T : Town) (s g : ℕ) (ans : Option (List Step)) :
    Decidable (NoneQuickerOn T s g ans) :=
  decidable_of_iff (∀ t ∈ ans, ∀ u ∈ T.tripsFrom (T.allStates (T.startAt s)).length (T.startAt s),
      T.IsTrip s g u → T.NeverFlat s u → T.tripMinutes s t ≤ T.tripMinutes s u) (by
    unfold NoneQuickerOn
    exact forall₂_congr fun t _ => (T.noneQuicker_iff s g _).symm)

instance (T : Town) (s g : ℕ) (ans : Option (List Step)) : Decidable (SaysNoneOn T s g ans) :=
  decidable_of_iff (ans = none ↔ ¬ ∃ t ∈ T.tripsFrom (T.allStates (T.startAt s)).length
      (T.startAt s), T.IsTrip s g t ∧ T.NeverFlat s t) (by
    unfold SaysNoneOn
    rw [T.exists_trip_iff s g])

/-! ## Each `Ops` piece is its one-trip piece on every trip -/

variable {S : Type} (o : Ops S)

theorem Ops.realTrip_iff : o.RealTrip ↔ ∀ T, T.WellFormed → ∀ s g, s < T.places →
    g < T.places → RealTripOn T s g (o.plan (o.build T) s g) := Iff.rfl

theorem Ops.noneQuicker_iff : o.NoneQuicker ↔ ∀ T, T.WellFormed → ∀ s g, s < T.places →
    g < T.places → NoneQuickerOn T s g (o.plan (o.build T) s g) := Iff.rfl

theorem Ops.saysNone_iff : o.SaysNone ↔ ∀ T, T.WellFormed → ∀ s g, s < T.places →
    g < T.places → SaysNoneOn T s g (o.plan (o.build T) s g) := Iff.rfl

end AlgoDesign.Paths.Workbench
