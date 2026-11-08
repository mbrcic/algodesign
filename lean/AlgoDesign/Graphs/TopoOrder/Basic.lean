/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.TopoOrder.Decide

/-! # Topological order: cycles, checkers and order facts

A named cycle and the DFS order's promise; each property of an answer as a `Bool` checker with a
proof it says the same; the facts about orders the two methods' proofs share; and the stuck set's
uniqueness. -/

@[expose] public section

namespace AlgoDesign.Graphs.TopoOrder

open Digraph

/-- **A named cycle** `w, …, v, w`: at least two vertices, the last the first again, each vertex
followed by one it has an arrow to, and the vertices before the last all different. A loop at `v`
gives `v, v`. -/
def IsCycle (g : Digraph) (c : List ℕ) : Prop :=
  2 ≤ c.length ∧ c.head? = c.getLast? ∧ c.IsChain g.Arrow ∧ c.dropLast.Nodup

instance decidableIsCycle (g : Digraph) (c : List ℕ) : Decidable (IsCycle g c) := by
  unfold IsCycle; infer_instance

/-- **What the DFS order's answer means**: a topological order, or a named cycle. -/
def DfsPromise (g : Digraph) : Except (List ℕ) (List ℕ) → Prop
  | .ok l => IsTopoOrder g l
  | .error c => IsCycle g c

/-! ## Rows -/

/-- An entry of `v`'s row leads to a vertex of the graph, by an arrow from `v`. -/
theorem mem_out {g : Digraph} {v : ℕ} {e : ℕ × ℕ} (he : e ∈ g.out v) :
    e.1 < g.n ∧ g.Arrow v e.1 := by
  simp only [out, idsBetween, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter] at he
  obtain ⟨w, hw, i, ⟨-, hi⟩, rfl⟩ := he
  exact ⟨hw, List.mem_of_getElem? (by simpa using hi)⟩

/-! ## Checkers

Each property above has a checker returning a `Bool`, with a proof it says the same. The one with
work in it is `RestPlaceable`: `peel` places the vertices outside the set one at a time, each time
the first in increasing order whose every arrow in comes from a vertex already placed, and the
rest is placeable exactly when this places them all. -/

/-- Every arrow into `v` comes from a vertex of `l`. -/
def readyAfter (g : Digraph) (l : List ℕ) (v : ℕ) : Bool :=
  g.arrows.all fun a => a.2 = v → a.1 ∈ l

/-- Vertex the vertices of `rest`, after `l`, for at most `f` rounds: each round appends the first
vertex of `rest` not yet placed whose every arrow in comes from a vertex already placed, and stops
when there is none. -/
def peel (g : Digraph) (rest : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, l => l
  | f + 1, l =>
    match rest.find? (fun v => v ∉ l ∧ readyAfter g l v) with
    | some v => peel g rest f (l ++ [v])
    | none => l

/-- Checks `RestPlaceable`. -/
def restPlaceable (g : Digraph) (s : List ℕ) : Bool :=
  (peel g (outside g s) (outside g s).length []).length = (outside g s).length

/-- Checks `IsStuck`. -/
def isStuck (g : Digraph) (s : List ℕ) : Bool :=
  !s.isEmpty && decide (s.Pairwise (· < ·)) && s.all (· < g.n) && decide (WaitsInside g s) &&
    restPlaceable g s

/-- Checks `IsTopoOrder`. -/
def isTopoOrder (g : Digraph) (l : List ℕ) : Bool := decide (IsTopoOrder g l)

/-- Checks `IsCycle`. -/
def isCycle (g : Digraph) (c : List ℕ) : Bool := decide (IsCycle g c)

theorem isTopoOrder_iff (g : Digraph) (l : List ℕ) : isTopoOrder g l = true ↔ IsTopoOrder g l :=
  decide_eq_true_iff

theorem isCycle_iff (g : Digraph) (c : List ℕ) : isCycle g c = true ↔ IsCycle g c :=
  decide_eq_true_iff

/-! ### Order facts -/

theorem Before.mem_left {l : List ℕ} {u v : ℕ} (h : Before l u v) : u ∈ l :=
  h.subset (by simp)

theorem Before.mem_right {l : List ℕ} {u v : ℕ} (h : Before l u v) : v ∈ l :=
  h.subset (by simp)

theorem Before.append {l : List ℕ} {u v : ℕ} (h : Before l u v) (r : List ℕ) :
    Before (l ++ r) u v :=
  h.trans (List.sublist_append_left l r)

theorem before_append_singleton {l : List ℕ} {u v : ℕ} (hu : u ∈ l) : Before (l ++ [v]) u v := by
  have : List.Sublist ([u] ++ [v]) (l ++ [v]) :=
    List.Sublist.append (List.singleton_sublist.2 hu) (List.Sublist.refl _)
  simpa [Before] using this

/-- In a list without repeats, a vertex before the first member of a set lies in the stretch
before it. -/
theorem mem_prefix_of_before {as bs : List ℕ} {u v : ℕ} (hnd : (as ++ v :: bs).Nodup)
    (h : Before (as ++ v :: bs) u v) : u ∈ as := by
  rw [List.nodup_append] at hnd
  have hv : v ∉ as := fun hv => hnd.2.2 v hv v (by simp) rfl
  have hvb : v ∉ bs := (List.nodup_cons.1 hnd.2.1).1
  unfold Before at h
  rw [List.sublist_append_iff] at h
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := h
  match l₁, he with
  | [], he =>
    simp only [List.nil_append] at he
    subst he
    rcases List.sublist_cons_iff.1 h₂ with h₂ | ⟨r, hr, h₂⟩
    · exact absurd (h₂.subset (by simp)) hvb
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact absurd (h₂.subset (by simp)) hvb
  | [x], he =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    exact he.1 ▸ h₁.subset (by simp)
  | [x, y], he =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    exact absurd (h₁.subset (by simp)) hv
  | _ :: _ :: _ :: _, he => simp at he

/-- A topological order has every vertex exactly once. -/
theorem IsTopoOrder.nodup {g : Digraph} {l : List ℕ} (h : IsTopoOrder g l) : l.Nodup :=
  h.1.nodup_iff.2 List.nodup_range

/-- **A set of vertices each waiting on one of them leaves no topological order.** In any order,
the first of them to appear waits on one of them, which must come earlier still. -/
theorem no_topoOrder_of_waitsInside {g : Digraph} {s : List ℕ} (hne : s ≠ [])
    (hw : WaitsInside g s) : ¬ ∃ l, IsTopoOrder g l := by
  rintro ⟨l, hl⟩
  obtain ⟨v₀, hv₀⟩ := List.exists_mem_of_ne_nil s hne
  obtain ⟨u₀, -, hu₀⟩ := hw v₀ hv₀
  have hv₀l : v₀ ∈ l := (hl.2 _ hu₀).mem_right
  obtain ⟨x, hx⟩ : ∃ x, l.find? (fun v => v ∈ s) = some x := by
    cases h : l.find? (fun v => v ∈ s) with
    | some x => exact ⟨x, rfl⟩
    | none => exact absurd hv₀ (by simpa using List.find?_eq_none.1 h v₀ hv₀l)
  rw [List.find?_eq_some_iff_append] at hx
  obtain ⟨hxs, as, bs, rfl, has⟩ := hx
  obtain ⟨u, hus, hu⟩ := hw x (by simpa using hxs)
  have := mem_prefix_of_before hl.nodup (hl.2 _ hu)
  simp_all

/-- In a named cycle every vertex has an arrow into it from a vertex of the cycle. -/
theorem IsCycle.waitsInside {g : Digraph} {c : List ℕ} (h : IsCycle g c) : WaitsInside g c := by
  obtain ⟨hlen, hhl, hch, -⟩ := h
  -- each vertex after the first has an arrow from the vertex before it
  have key : ∀ (a : ℕ) (t : List ℕ), (a :: t).IsChain g.Arrow → ∀ x ∈ t, ∃ y ∈ a :: t,
      g.Arrow y x := by
    intro a t
    induction t generalizing a with
    | nil => simp
    | cons b t ih =>
      intro hc x hx
      rw [List.isChain_cons_cons] at hc
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨a, by simp, hc.1⟩
      · obtain ⟨y, hy, hxy⟩ := ih b hc.2 x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
  match c, hlen, hhl, hch with
  | a :: t, hlen, hhl, hch =>
    intro x hx
    have ht : t ≠ [] := by rintro rfl; simp at hlen
    rcases List.mem_cons.1 hx with rfl | hx
    · -- the first vertex is also the last, which is in the tail
      have hlast : (x :: t).getLast? = t.getLast? := by
        cases t with
        | nil => exact absurd rfl ht
        | cons b t => simp [List.getLast?_cons_cons]
      have : x ∈ t := by
        rw [hlast] at hhl
        exact List.mem_of_getLast? (by simpa using hhl.symm)
      exact key x t hch x this
    · exact key a t hch x hx

/-- **A named cycle leaves no topological order.** -/
theorem no_topoOrder_of_isCycle {g : Digraph} {c : List ℕ} (h : IsCycle g c) :
    ¬ ∃ l, IsTopoOrder g l :=
  no_topoOrder_of_waitsInside (by rintro rfl; simp [IsCycle] at h) h.waitsInside

/-- **A stuck set leaves no topological order.** -/
theorem no_topoOrder_of_isStuck {g : Digraph} {s : List ℕ} (h : IsStuck g s) :
    ¬ ∃ l, IsTopoOrder g l :=
  no_topoOrder_of_waitsInside h.1 h.2.2.2.1

/-! ### The checker for the rest -/

/-- A list without repeats, inside `r` and at least as long, holds all of `r`. -/
theorem subset_of_length_le {l r : List ℕ} (hl : l.Nodup) (hsub : l ⊆ r)
    (hlen : r.length ≤ l.length) : r ⊆ l := by
  intro x hx
  by_contra hxl
  have : l ⊆ r.erase x := fun y hy =>
    (List.mem_erase_of_ne (fun h => hxl (by subst h; exact hy))).2 (hsub hy)
  have h1 := hl.length_le_of_subset this
  rw [List.length_erase_of_mem hx] at h1
  have : 0 < r.length := List.length_pos_of_mem hx
  omega

theorem readyAfter_iff {g : Digraph} {l : List ℕ} {v : ℕ} :
    readyAfter g l v = true ↔ ∀ a ∈ g.arrows, a.2 = v → a.1 ∈ l := by
  simp only [readyAfter, List.all_eq_true, decide_eq_true_eq]

theorem nodup_outside (g : Digraph) (s : List ℕ) : (outside g s).Nodup :=
  List.nodup_range.filter _

theorem mem_outside {g : Digraph} {s : List ℕ} {x : ℕ} : x ∈ outside g s ↔ x < g.n ∧ x ∉ s := by
  simp [outside]

/-- Placing a ready vertex keeps every placed vertex after everything it waits for. -/
theorem AfterWaits.append_ready {g : Digraph} {l : List ℕ} {v : ℕ} (h : AfterWaits g l)
    (hv : v ∉ l) (hr : ∀ a ∈ g.arrows, a.2 = v → a.1 ∈ l) : AfterWaits g (l ++ [v]) := by
  refine ⟨?_, fun a ha hin => ?_⟩
  · have : ∀ x ∈ l, x ≠ v := fun x hx (hxv : x = v) => hv (hxv ▸ hx)
    simpa [List.nodup_append, h.1] using this
  rcases List.mem_append.1 hin with hin | hin
  · exact (h.2 a ha hin).append _
  · have h2 : a.2 = v := by simpa using hin
    rw [h2]
    exact before_append_singleton (hr a ha h2)

/-- `peel` only places vertices of `rest`, each after everything it waits for. -/
theorem peel_sound (g : Digraph) (rest : List ℕ) (f : ℕ) {l : List ℕ} (h : AfterWaits g l)
    (hsub : l ⊆ rest) : AfterWaits g (peel g rest f l) ∧ peel g rest f l ⊆ rest := by
  induction f generalizing l with
  | zero => exact ⟨h, hsub⟩
  | succ f ih =>
    unfold peel
    split
    · next v hv =>
      rw [List.find?_eq_some_iff_append] at hv
      obtain ⟨hp, as, bs, he, -⟩ := hv
      simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, decide_not,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hp
      refine ih (h.append_ready hp.1 (readyAfter_iff.1 hp.2)) ?_
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsub hx
      · simp only [List.mem_singleton] at hx
        simp [he, hx]
    · exact ⟨h, hsub⟩

/-- If some order places the vertices of `rest`, `peel` with enough rounds places all of them: the
first vertex of that order not yet placed is always ready. -/
theorem peel_complete (g : Digraph) {rest L : List ℕ} (hL : L.Perm rest) (hLw : AfterWaits g L)
    (f : ℕ) {l : List ℕ} (h : AfterWaits g l) (hsub : l ⊆ rest)
    (hlen : rest.length ≤ l.length + f) : rest ⊆ peel g rest f l := by
  induction f generalizing l with
  | zero => exact subset_of_length_le h.1 hsub hlen
  | succ f ih =>
    unfold peel
    split
    · next v hv =>
      rw [List.find?_eq_some_iff_append] at hv
      obtain ⟨hp, as, bs, he, -⟩ := hv
      simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq, decide_not,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hp
      refine ih (h.append_ready hp.1 (readyAfter_iff.1 hp.2)) ?_ (by simp; omega)
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hsub hx
      · simp only [List.mem_singleton] at hx
        simp [he, hx]
    · next hnone =>
      intro x hx
      by_contra hxl
      obtain ⟨y, hy⟩ : ∃ y, L.find? (fun v => v ∉ l) = some y := by
        cases hf : L.find? (fun v => v ∉ l) with
        | some y => exact ⟨y, rfl⟩
        | none =>
          exact absurd (by simpa using List.find?_eq_none.1 hf x (hL.symm.subset hx)) hxl
      rw [List.find?_eq_some_iff_append] at hy
      obtain ⟨hyl, as, bs, hLe, has⟩ := hy
      simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        at hyl
      have hready : ∀ a ∈ g.arrows, a.2 = y → a.1 ∈ l := by
        intro a ha h2
        have hb := hLw.2 a ha (by rw [hLe, h2]; simp)
        rw [h2, hLe] at hb
        have := mem_prefix_of_before (hLe ▸ hLw.1) hb
        simpa using has _ this
      have hyrest : y ∈ rest := hL.subset (by rw [hLe]; simp)
      have := List.find?_eq_none.1 hnone y hyrest
      simp [hyl, readyAfter_iff.2 hready] at this

theorem restPlaceable_iff (g : Digraph) (s : List ℕ) :
    restPlaceable g s = true ↔ RestPlaceable g s := by
  unfold restPlaceable RestPlaceable
  simp only [decide_eq_true_eq]
  have h0 : AfterWaits g [] := ⟨List.nodup_nil, by simp⟩
  obtain ⟨hw, hsub⟩ := peel_sound g (outside g s) (outside g s).length h0 (by simp)
  constructor
  · intro hlen
    refine ⟨_, (List.perm_ext_iff_of_nodup hw.1 (nodup_outside g s)).2 fun a =>
      ⟨fun ha => hsub ha, fun ha => subset_of_length_le hw.1 hsub hlen.ge ha⟩, hw⟩
  · rintro ⟨L, hL, hLw⟩
    have hall := peel_complete g hL hLw (outside g s).length h0 (by simp) (by simp)
    exact ((List.perm_ext_iff_of_nodup hw.1 (nodup_outside g s)).2
      fun a => ⟨fun ha => hsub ha, fun ha => hall ha⟩).length_eq

theorem isStuck_iff (g : Digraph) (s : List ℕ) : isStuck g s = true ↔ IsStuck g s := by
  simp [isStuck, IsStuck, restPlaceable_iff, and_assoc]

instance decidableRestPlaceable (g : Digraph) (s : List ℕ) : Decidable (RestPlaceable g s) :=
  decidable_of_iff _ (restPlaceable_iff g s)

instance decidableIsStuck (g : Digraph) (s : List ℕ) : Decidable (IsStuck g s) :=
  decidable_of_iff _ (isStuck_iff g s)

/-- **Nothing leaves a stuck set**: an arrow from a stuck vertex to a vertex of the graph goes to a
stuck vertex, since the vertices outside are each placed after everything they wait for. -/
theorem IsStuck.closed {g : Digraph} {s : List ℕ} (h : IsStuck g s) :
    ∀ a ∈ g.arrows, a.1 ∈ s → a.2 < g.n → a.2 ∈ s := by
  intro a ha h1 h2
  by_contra h2s
  obtain ⟨l, hl, hw⟩ := h.2.2.2.2
  have h2l : a.2 ∈ l := hl.symm.subset (by simp [outside, h2, h2s])
  have h1l := (hw.2 a ha h2l).mem_left
  exact absurd h1 (by simpa using (List.mem_filter.1 (hl.subset h1l)).2)

/-- Two lists in increasing order with the same members are equal. -/
theorem eq_of_pairwise_lt_of_mem_iff :
    ∀ {s t : List ℕ}, s.Pairwise (· < ·) → t.Pairwise (· < ·) → (∀ x, x ∈ s ↔ x ∈ t) → s = t
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (by simp)
  | a :: s, b :: t, hs, ht, h => by
    rw [List.pairwise_cons] at hs ht
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with hab | hab
      · exact hab
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with hba | hba
      · exact hba.symm
      exact absurd (Nat.lt_trans (ht.1 a hab) (hs.1 b hba)) (Nat.lt_irrefl _)
    subst hab
    congr 1
    refine eq_of_pairwise_lt_of_mem_iff hs.2 ht.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with hxa | hxa
      · exact absurd (hxa ▸ hs.1 x hx) (Nat.lt_irrefl _)
      · exact hxa
    · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with hxa | hxa
      · exact absurd (hxa ▸ ht.1 x hx) (Nat.lt_irrefl _)
      · exact hxa

/-- A stuck set holds every vertex that waits, through some chain, on one of its own: a vertex
outside it would be placed in the others' order, and the first of the set to be placed would
come after a member it waits on. -/
theorem IsStuck.subset {g : Digraph} {s t : List ℕ} (hs : IsStuck g s) (ht : IsStuck g t) :
    ∀ x ∈ t, x ∈ s := by
  intro x hxt
  by_contra hxs
  obtain ⟨L, hL, hLw⟩ := hs.2.2.2.2
  have hxL : x ∈ L := hL.symm.subset (mem_outside.2 ⟨ht.2.2.1 x hxt, hxs⟩)
  obtain ⟨y, hy⟩ : ∃ y, L.find? (fun v => v ∈ t) = some y := by
    cases hf : L.find? (fun v => v ∈ t) with
    | some y => exact ⟨y, rfl⟩
    | none => exact absurd hxt (by simpa using List.find?_eq_none.1 hf x hxL)
  rw [List.find?_eq_some_iff_append] at hy
  obtain ⟨hyt, as, bs, hLe, has⟩ := hy
  obtain ⟨u, hut, hu⟩ := ht.2.2.2.1 y (by simpa using hyt)
  have hb := hLw.2 _ hu (by rw [hLe]; simp)
  rw [hLe] at hb
  have hua := mem_prefix_of_before (hLe ▸ hLw.1) hb
  simpa [hut] using has u hua

/-- **The stuck set is unique**: it is exactly the vertices that cannot be placed. -/
theorem IsStuck.unique {g : Digraph} {s t : List ℕ} (hs : IsStuck g s) (ht : IsStuck g t) :
    s = t :=
  eq_of_pairwise_lt_of_mem_iff hs.2.1 ht.2.1 fun x => ⟨ht.subset hs x, hs.subset ht x⟩

instance decidableKahnPromise (g : Digraph) :
    (r : Except (List ℕ) (List ℕ)) → Decidable (KahnPromise g r)
  | .ok l => inferInstanceAs (Decidable (IsTopoOrder g l))
  | .error s => inferInstanceAs (Decidable (IsStuck g s))

instance decidableDfsPromise (g : Digraph) :
    (r : Except (List ℕ) (List ℕ)) → Decidable (DfsPromise g r)
  | .ok l => inferInstanceAs (Decidable (IsTopoOrder g l))
  | .error c => inferInstanceAs (Decidable (IsCycle g c))

end AlgoDesign.Graphs.TopoOrder
