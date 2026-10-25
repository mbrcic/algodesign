/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Cycles

/-!
# Bridges, cut vertices and blocks: cycles

`OnCycleWith` reads a cycle from one of its links. Here a cycle is read on its own (`IsCycle`): a
walk back to its start through distinct vertices on distinct links, given by its steps. Turning it
(`IsCycle.rotate`) and cutting it into two paths (`IsCycle.split`) are cheap, and a path can be
walked backwards (`revSteps`, `IsPath.reverse`). `onCycleWith_iff` proves that `OnCycleWith g e f`
says exactly that `e` and `f` are two links of one cycle. From that:

* `onCycleWith_symm` and `sameBlock_symm`: the relation is symmetric;
* `sameBlock_trans`: blocks are classes. A cycle through `e` and `f` and a cycle through `f` and
  `h` give a cycle through `e` and `h`: the second cycle leaves the first and comes back to it
  through `h`, and that detour with the arc of the first cycle holding `e` is a cycle;
* `onCycleWith_gate`: a cycle cannot pass a gate vertex `u` of a set of vertices only once.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

variable {g : Graph}

/-- An end of link `i`. -/
def IsEnd (g : Graph) (i x : ℕ) : Prop := ∃ y, Joins g i x y

/-! ## Links and walks -/

theorem Joins.symm {i a b : ℕ} (h : Joins g i a b) : Joins g i b a := Or.symm h

/-- A link has one pair of ends. -/
theorem Joins.ends {i a b c d : ℕ} (h : Joins g i a b) (h' : Joins g i c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h] at h' <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at h' <;> omega

theorem endOf_append (x : ℕ) (l₁ l₂ : List (ℕ × ℕ)) :
    endOf x (l₁ ++ l₂) = endOf (endOf x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons s l ih => rw [List.cons_append, endOf_cons, endOf_cons, ih]

theorem endOf_singleton (x : ℕ) (s : ℕ × ℕ) : endOf x [s] = s.2 := by
  rw [endOf_cons, endOf_nil]

theorem trail_append {x : ℕ} {l₁ l₂ : List (ℕ × ℕ)} :
    Trail g x (l₁ ++ l₂) ↔ Trail g x l₁ ∧ Trail g (endOf x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => simp [Trail, endOf_nil]
  | cons s l ih =>
    obtain ⟨f, y⟩ := s
    simp only [List.cons_append, Trail, ih, endOf_cons, and_assoc]

/-- The vertices of a walk, its start first, end with where it ends. -/
theorem vertices_eq (x : ℕ) (c : List (ℕ × ℕ)) :
    x :: c.map Prod.snd = (x :: c.map Prod.snd).dropLast ++ [endOf x c] :=
  (List.dropLast_append_getLast _).symm

theorem endOf_mem (x : ℕ) (c : List (ℕ × ℕ)) : endOf x c ∈ x :: c.map Prod.snd :=
  List.getLast_mem _

theorem endOf_mem_of_ne_nil {x : ℕ} {c : List (ℕ × ℕ)} (hc : c ≠ []) :
    endOf x c ∈ c.map Prod.snd := by
  obtain ⟨s, l, rfl⟩ := List.exists_cons_of_ne_nil hc
  rw [endOf_cons]
  exact endOf_mem _ _

/-- A step of a walk: the link joins the vertex before it to the vertex it leads to. -/
theorem Trail.mem {x f v : ℕ} {c : List (ℕ × ℕ)} (h : Trail g x c) (hm : (f, v) ∈ c) :
    ∃ r₁ r₂, c = r₁ ++ (f, v) :: r₂ ∧ Joins g f (endOf x r₁) v := by
  obtain ⟨r₁, r₂, rfl⟩ := List.append_of_mem hm
  exact ⟨r₁, r₂, rfl, (trail_append.mp h).2.1⟩

/-! ## Walking backwards -/

/-- The steps of a walk from `x`, walked backwards from its end to `x`. -/
def revSteps : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | x, (f, y) :: rest => revSteps y rest ++ [(f, x)]

theorem map_fst_revSteps (x : ℕ) (c : List (ℕ × ℕ)) :
    (revSteps x c).map Prod.fst = (c.map Prod.fst).reverse := by
  induction c generalizing x with
  | nil => rfl
  | cons s l ih => obtain ⟨f, y⟩ := s; simp [revSteps, ih]

theorem endOf_revSteps (x : ℕ) (c : List (ℕ × ℕ)) : endOf (endOf x c) (revSteps x c) = x := by
  induction c generalizing x with
  | nil => rfl
  | cons s l ih =>
    obtain ⟨f, y⟩ := s
    rw [revSteps, endOf_cons, endOf_append, ih, endOf_singleton]

theorem vertices_revSteps (x : ℕ) (c : List (ℕ × ℕ)) :
    endOf x c :: (revSteps x c).map Prod.snd = (x :: c.map Prod.snd).reverse := by
  induction c generalizing x with
  | nil => rfl
  | cons s l ih =>
    obtain ⟨f, y⟩ := s
    rw [revSteps, endOf_cons, List.map_append, ← List.cons_append, ih]
    simp

theorem Trail.revSteps {x : ℕ} {c : List (ℕ × ℕ)} (h : Trail g x c) :
    Trail g (endOf x c) (revSteps x c) := by
  induction c generalizing x with
  | nil => trivial
  | cons s l ih =>
    obtain ⟨f, y⟩ := s
    rw [Blocks.revSteps, endOf_cons, trail_append, endOf_revSteps]
    exact ⟨ih h.2, h.1.symm, trivial⟩

/-! ## Paths and cycles -/

/-- **A path** from `x` to `y`: a walk through distinct vertices. -/
structure IsPath (g : Graph) (x : ℕ) (c : List (ℕ × ℕ)) (y : ℕ) : Prop where
  trail : Trail g x c
  endOf_eq : endOf x c = y
  nodup : (x :: c.map Prod.snd).Nodup

/-- **A cycle** from `x`: a walk back to `x` through distinct vertices, on distinct links. -/
structure IsCycle (g : Graph) (x : ℕ) (c : List (ℕ × ℕ)) : Prop where
  trail : Trail g x c
  closed : endOf x c = x
  vertices : (c.map Prod.snd).Nodup
  links : (c.map Prod.fst).Nodup

/-- A path walked backwards is a path. -/
theorem IsPath.reverse {x y : ℕ} {c : List (ℕ × ℕ)} (h : IsPath g x c y) :
    IsPath g y (revSteps x c) x := by
  obtain ⟨htr, rfl, hnd⟩ := h
  refine ⟨htr.revSteps, endOf_revSteps x c, ?_⟩
  rw [vertices_revSteps]
  exact List.nodup_reverse.mpr hnd

/-- A path never uses a link twice. -/
theorem IsPath.links_nodup {x y : ℕ} {c : List (ℕ × ℕ)} (h : IsPath g x c y) :
    (c.map Prod.fst).Nodup := by
  induction c generalizing x with
  | nil => simp
  | cons s l ih =>
    obtain ⟨f, w⟩ := s
    obtain ⟨⟨hj, htr⟩, hend, hnd⟩ := h
    rw [endOf_cons] at hend
    have hnd' : (w :: l.map Prod.snd).Nodup := (List.nodup_cons.mp hnd).2
    have hx : x ∉ w :: l.map Prod.snd := (List.nodup_cons.mp hnd).1
    refine List.nodup_cons.mpr ⟨fun hf => ?_, ih ⟨htr, hend, hnd'⟩⟩
    obtain ⟨⟨f', v⟩, hm, rfl⟩ := List.mem_map.mp hf
    obtain ⟨r₁, r₂, rfl, hj'⟩ := htr.mem hm
    have hv : v ∈ w :: (r₁ ++ (f', v) :: r₂).map Prod.snd := by simp
    have hu : endOf w r₁ ∈ w :: (r₁ ++ (f', v) :: r₂).map Prod.snd :=
      (by intro z; simp; tauto : w :: r₁.map Prod.snd ⊆ _) (endOf_mem w r₁)
    rcases hj.ends hj' with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hx (h1 ▸ hu)
    · exact hx (h2 ▸ hv)

/-- A closed walk through distinct vertices with at least three steps uses distinct links. -/
theorem links_nodup_of_three {x : ℕ} {c : List (ℕ × ℕ)} (htr : Trail g x c)
    (hcl : endOf x c = x) (hnd : (c.map Prod.snd).Nodup) (h3 : 3 ≤ c.length) :
    (c.map Prod.fst).Nodup := by
  obtain ⟨⟨f, w⟩, rest, rfl⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos (by omega : 0 < c.length))
  rw [endOf_cons] at hcl
  have hp : IsPath g w rest x := ⟨htr.2, hcl, hnd⟩
  refine List.nodup_cons.mpr ⟨fun hf => ?_, hp.links_nodup⟩
  obtain ⟨⟨f', v⟩, hm, rfl⟩ := List.mem_map.mp hf
  obtain ⟨r₁, r₂, rfl, hj'⟩ := htr.2.mem hm
  have hw : w ∉ (r₁ ++ (f', v) :: r₂).map Prod.snd := (List.nodup_cons.mp hnd).1
  rcases htr.1.ends hj' with ⟨-, h2⟩ | ⟨h1, rfl⟩
  · exact hw (h2 ▸ by simp)
  · have hr₁ : r₁ = [] := by
      by_contra hne
      obtain ⟨s, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      refine endOf_ne (List.Nodup.sublist ?_ hnd) h1
      simp only [List.map_cons, List.cons_append, List.map_append]
      exact List.Sublist.cons_cons _ (List.sublist_append_left _ _)
    subst hr₁
    have hr₂ : r₂ = [] := by
      by_contra hne
      obtain ⟨s, l, rfl⟩ := List.exists_cons_of_ne_nil hne
      have hnd₂ : (v :: (s :: l).map Prod.snd).Nodup := by
        simpa using (List.nodup_cons.mp hnd).2
      refine endOf_ne hnd₂ ?_
      simpa [endOf_cons, endOf_nil] using hcl
    subst hr₂
    simp at h3

/-- A cycle turned to start elsewhere is a cycle. -/
theorem IsCycle.rotate {x : ℕ} {c₁ c₂ : List (ℕ × ℕ)} (h : IsCycle g x (c₁ ++ c₂)) :
    IsCycle g (endOf x c₁) (c₂ ++ c₁) := by
  obtain ⟨htr, hcl, hp, hl⟩ := h
  rw [trail_append] at htr
  rw [endOf_append] at hcl
  have h₁ : Trail g (endOf (endOf x c₁) c₂) c₁ := by rw [hcl]; exact htr.1
  refine ⟨trail_append.mpr ⟨htr.2, h₁⟩, by rw [endOf_append, hcl], ?_, ?_⟩
  · rw [List.map_append] at hp ⊢
    exact (List.perm_append_comm.nodup_iff).mp hp
  · rw [List.map_append] at hl ⊢
    exact (List.perm_append_comm.nodup_iff).mp hl

/-- A cycle cut in two is two paths. -/
theorem IsCycle.split {x : ℕ} {c₁ c₂ : List (ℕ × ℕ)} (h : IsCycle g x (c₁ ++ c₂))
    (h₁ : c₁ ≠ []) (h₂ : c₂ ≠ []) :
    IsPath g x c₁ (endOf x c₁) ∧ IsPath g (endOf x c₁) c₂ x := by
  obtain ⟨htr, hcl, hp, -⟩ := h
  rw [trail_append] at htr
  rw [endOf_append] at hcl
  rw [List.map_append, List.nodup_append] at hp
  obtain ⟨hp₁, hp₂, hd⟩ := hp
  have hx : x ∈ c₂.map Prod.snd := hcl ▸ endOf_mem_of_ne_nil h₂
  have hy : endOf x c₁ ∈ c₁.map Prod.snd := endOf_mem_of_ne_nil h₁
  refine ⟨⟨htr.1, rfl, List.nodup_cons.mpr ⟨fun hm => hd _ hm _ hx rfl, hp₁⟩⟩,
    ⟨htr.2, hcl, List.nodup_cons.mpr ⟨fun hm => hd _ hy _ hm rfl, hp₂⟩⟩⟩

/-- A cycle turned to start with any of its steps. -/
theorem IsCycle.rotate_step {x f w : ℕ} {c : List (ℕ × ℕ)} (h : IsCycle g x c)
    (hm : (f, w) ∈ c) : ∃ z rest, IsCycle g z ((f, w) :: rest) ∧ ((f, w) :: rest).Perm c ∧
      Joins g f z w := by
  obtain ⟨r₁, r₂, rfl, hj⟩ := h.trail.mem hm
  exact ⟨_, r₂ ++ r₁, h.rotate, List.perm_append_comm (l₁ := (f, w) :: r₂), hj⟩

/-- A cycle turned to start at any of its vertices. -/
theorem IsCycle.rotate_vertex {x p : ℕ} {c : List (ℕ × ℕ)} (h : IsCycle g x c)
    (hm : p ∈ c.map Prod.snd) : ∃ c', IsCycle g p c' ∧ c'.Perm c := by
  obtain ⟨⟨f, p'⟩, hs, rfl⟩ := List.mem_map.mp hm
  obtain ⟨r₁, r₂, rfl⟩ := List.append_of_mem hs
  have h' : IsCycle g x ((r₁ ++ [(f, p')]) ++ r₂) := by simpa using h
  have := h'.rotate
  rw [endOf_append, endOf_singleton] at this
  exact ⟨_, this, List.perm_append_comm.trans (List.Perm.of_eq (by simp))⟩

/-- Both ends of a link of a cycle are vertices of it. -/
theorem IsCycle.mem_of_isEnd {x f p : ℕ} {c : List (ℕ × ℕ)} (h : IsCycle g x c)
    (hf : f ∈ c.map Prod.fst) (hp : IsEnd g f p) : p ∈ c.map Prod.snd := by
  obtain ⟨⟨f', w⟩, hm, rfl⟩ := List.mem_map.mp hf
  obtain ⟨z, rest, hc, hperm, hj⟩ := h.rotate_step hm
  obtain ⟨q, hq⟩ := hp
  refine (hperm.map Prod.snd).subset ?_
  have hz : z ∈ ((f', w) :: rest).map Prod.snd := hc.closed ▸ endOf_mem_of_ne_nil (by simp)
  rcases hj.ends hq with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hz
  · simp

/-! ## Cycles through two links -/

/-- **A cycle through `e` holding `f`** is a cycle with the two different links `e` and `f`. -/
theorem onCycleWith_iff {e f : ℕ} : OnCycleWith g e f ↔
    e ≠ f ∧ ∃ x c, IsCycle g x c ∧ e ∈ c.map Prod.fst ∧ f ∈ c.map Prod.fst := by
  constructor
  · rintro ⟨a, b, hl, -, steps, htr, hnd, hend, he, hf⟩
    have hp : IsPath g b steps a := ⟨htr, hend, hnd⟩
    refine ⟨fun h => he (h ▸ hf), a, (e, b) :: steps,
      ⟨⟨Or.inl hl, htr⟩, by rw [endOf_cons]; exact hend, hnd,
        List.nodup_cons.mpr ⟨he, hp.links_nodup⟩⟩, by simp, by simp [hf]⟩
  · rintro ⟨hef, x, c, hc, he, hf⟩
    obtain ⟨⟨e', w⟩, hm, rfl⟩ := List.mem_map.mp he
    obtain ⟨z, rest, hc', hperm, hj⟩ := hc.rotate_step hm
    have hf' : f ∈ rest.map Prod.fst := by
      have := (hperm.map Prod.fst).mem_iff.mpr hf
      simp only [List.map_cons, List.mem_cons] at this
      exact this.resolve_left (Ne.symm hef)
    have hne : rest ≠ [] := by rintro rfl; simp at hf'
    have he' : e' ∉ rest.map Prod.fst := (List.nodup_cons.mp hc'.links).1
    have hp := (hc'.split (c₁ := [(e', w)]) (c₂ := rest) (by simp) hne).2
    rw [endOf_singleton] at hp
    obtain ⟨s, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    have hzw : z ≠ w := fun h => endOf_ne hp.nodup (hp.endOf_eq.trans h)
    rcases hj with hl | hl
    · exact ⟨z, w, hl, hzw, _, hp.trail, hp.nodup, hp.endOf_eq, he', hf'⟩
    · have hr := hp.reverse
      refine ⟨w, z, hl, Ne.symm hzw, _, hr.trail, hr.nodup, hr.endOf_eq, ?_, ?_⟩
      · rwa [map_fst_revSteps, List.mem_reverse]
      · rwa [map_fst_revSteps, List.mem_reverse]

theorem onCycleWith_symm {e f : ℕ} (h : OnCycleWith g e f) : OnCycleWith g f e := by
  obtain ⟨hef, x, c, hc, he, hf⟩ := onCycleWith_iff.mp h
  exact onCycleWith_iff.mpr ⟨Ne.symm hef, x, c, hc, hf, he⟩

theorem sameBlock_symm {e f : ℕ} (h : SameBlock g e f) : SameBlock g f e := by
  obtain ⟨he, hf, h | h⟩ := h
  · exact ⟨hf, he, Or.inl h.symm⟩
  · exact ⟨hf, he, Or.inr (onCycleWith_symm h)⟩

/-! ## A gate -/

section Gate

variable {S : ℕ → Prop} {u : ℕ}
  (hS : ∀ i a b : ℕ, g.links[i]? = some (a, b) →
    (S a → ¬ S b → b = u) ∧ (S b → ¬ S a → a = u))
include hS

/-- A link leaving `S` leads to the gate. -/
theorem gate_of_joins {i a b : ℕ} (h : Joins g i a b) (ha : S a) (hb : ¬ S b) : b = u := by
  rcases h with h | h
  · exact (hS i a b h).1 ha hb
  · exact (hS i b a h).2 ha hb

/-- A walk that leaves `S` passes the gate. -/
theorem gate_mem_of_leave :
    ∀ {x : ℕ} {c : List (ℕ × ℕ)}, Trail g x c → S x → ¬ S (endOf x c) → u ∈ c.map Prod.snd
  | _, [], _, hx, hend => absurd hx hend
  | _, (f, w) :: rest, ⟨hj, htr⟩, hx, hend => by
    rw [endOf_cons] at hend
    by_cases hw : S w
    · exact List.mem_cons_of_mem _ (gate_mem_of_leave htr hw hend)
    · rw [← gate_of_joins hS hj hx hw]
      exact List.mem_cons_self ..

/-- A walk that enters `S` starts at the gate or passes it. -/
theorem gate_mem_of_enter :
    ∀ {x : ℕ} {c : List (ℕ × ℕ)}, Trail g x c → ¬ S x → S (endOf x c) →
      u ∈ x :: c.map Prod.snd
  | _, [], _, hx, hend => absurd hend hx
  | _, (f, w) :: rest, ⟨hj, htr⟩, hx, hend => by
    rw [endOf_cons] at hend
    by_cases hw : S w
    · rw [← gate_of_joins hS hj.symm hw hx]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (gate_mem_of_enter htr hw hend)

end Gate

/-- **No cycle crosses a single gate**: if every link with exactly one end in `S` has its other
end at `u` (and `u ∉ S`), a cycle with a vertex in `S` has none outside `S` other than `u`. -/
theorem onCycleWith_gate {S : ℕ → Prop} {u : ℕ} (_hu : ¬ S u)
    (hS : ∀ i a b : ℕ, g.links[i]? = some (a, b) →
      (S a → ¬ S b → b = u) ∧ (S b → ¬ S a → a = u))
    {e f x y : ℕ} (h : OnCycleWith g e f) (hx : IsEnd g e x ∨ IsEnd g f x)
    (hy : IsEnd g e y ∨ IsEnd g f y) (hxS : S x) (hyS : ¬ S y) : y = u := by
  obtain ⟨-, z, c, hc, he, hf⟩ := onCycleWith_iff.mp h
  have hmem : ∀ p, (IsEnd g e p ∨ IsEnd g f p) → p ∈ c.map Prod.snd := by
    rintro p (hp | hp)
    · exact hc.mem_of_isEnd he hp
    · exact hc.mem_of_isEnd hf hp
  obtain ⟨c', hc', hperm⟩ := hc.rotate_vertex (hmem x hx)
  have hy' : y ∈ c'.map Prod.snd := (hperm.map Prod.snd).mem_iff.mpr (hmem y hy)
  obtain ⟨⟨f', y'⟩, hs, rfl⟩ := List.mem_map.mp hy'
  obtain ⟨r₁, r₂, rfl⟩ := List.append_of_mem hs
  have htr : Trail g x ((r₁ ++ [(f', y')]) ++ r₂) := by simpa using hc'.trail
  rw [trail_append, endOf_append, endOf_singleton] at htr
  have hcl : endOf y' r₂ = x := by
    simpa [endOf_append, endOf_cons] using hc'.closed
  have h₁ := gate_mem_of_leave hS htr.1 hxS (by rwa [endOf_append, endOf_singleton])
  have h₂ := gate_mem_of_enter hS htr.2 hyS (hcl ▸ hxS)
  rcases List.mem_cons.mp h₂ with h₂ | h₂
  · exact h₂.symm
  · have hnd : ((r₁ ++ [(f', y')]).map Prod.snd ++ r₂.map Prod.snd).Nodup := by
      simpa using hc'.vertices
    exact (List.disjoint_of_nodup_append hnd h₁ h₂).elim

/-! ## Blocks are classes -/

/-- The first vertex of a walk in `P`: the walk up to it meets `P` only there. -/
theorem first_hit (P : ℕ → Prop) :
    ∀ (x : ℕ) (c : List (ℕ × ℕ)), (∃ p ∈ x :: c.map Prod.snd, P p) →
      ∃ c₁ c₂, c = c₁ ++ c₂ ∧ P (endOf x c₁) ∧ ∀ p ∈ (x :: c₁.map Prod.snd).dropLast, ¬ P p
  | x, c, ⟨p, hp, hP⟩ => by
    by_cases hx : P x
    · exact ⟨[], c, rfl, hx, by simp⟩
    induction c generalizing x with
    | nil =>
      rw [List.map_nil, List.mem_singleton] at hp
      exact absurd (hp ▸ hP) hx
    | cons s l ih =>
      obtain ⟨f, v⟩ := s
      have hp' : p ∈ v :: l.map Prod.snd := by
        rcases List.mem_cons.mp hp with rfl | hp
        · exact absurd hP hx
        · simpa using hp
      by_cases hv : P v
      · exact ⟨[(f, v)], l, rfl, hv, by simpa using hx⟩
      obtain ⟨c₁, c₂, rfl, hend, hout⟩ := ih v hp' hv
      refine ⟨(f, v) :: c₁, c₂, rfl, by rwa [endOf_cons], ?_⟩
      intro q hq
      simp only [List.map_cons, List.dropLast_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hx
      · exact hout q hq

/-- The last vertex of a walk in `P`, for a walk from a vertex in `P`: after it the walk misses
`P`. -/
theorem last_hit (P : ℕ → Prop) (x : ℕ) (hx : P x) (c : List (ℕ × ℕ)) :
    ∃ c₁ c₂, c = c₁ ++ c₂ ∧ P (endOf x c₁) ∧ ∀ p ∈ c₂.map Prod.snd, ¬ P p := by
  induction c using List.reverseRecOn with
  | nil => exact ⟨[], [], rfl, hx, by simp⟩
  | append_singleton l s ih =>
    by_cases hs : P s.2
    · exact ⟨l ++ [s], [], by simp, by rwa [endOf_append, endOf_singleton], by simp⟩
    · obtain ⟨c₁, c₂, rfl, hend, hout⟩ := ih
      refine ⟨c₁, c₂ ++ [s], by simp, hend, ?_⟩
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton]
      rintro p (hp | rfl)
      · exact hout p hp
      · exact hs

/-- **A detour through `h`**: a cycle starting with link `h` that meets a set `P` of vertices in two
different vertices leaves `P` and comes back to it through `h`. Turned to start where it last
leaves `P` before `h`, its first steps `Q` lead to a vertex of `P` through `h`, with no vertex of
`P` between. -/
theorem detour (P : ℕ → Prop) {x h y : ℕ} {B : List (ℕ × ℕ)} (hc : IsCycle g x ((h, y) :: B))
    {z w : ℕ} (hz : z ∈ y :: B.map Prod.snd) (hw : w ∈ y :: B.map Prod.snd) (hzP : P z)
    (hwP : P w) (hzw : z ≠ w) :
    ∃ s Q R, IsCycle g s (Q ++ R) ∧ Q ≠ [] ∧ R ≠ [] ∧ h ∈ Q.map Prod.fst ∧ P s ∧
      P (endOf s Q) ∧ ∀ p ∈ (Q.map Prod.snd).dropLast, ¬ P p := by
  obtain ⟨L₁, L₂, rfl, ht, hout₁⟩ := first_hit P y B ⟨z, hz, hzP⟩
  obtain ⟨M₁, M₂, rfl, hs, hout₂⟩ := last_hit P _ ht L₂
  have hc' : IsCycle g x (((h, y) :: L₁ ++ M₁) ++ M₂) := by simpa using hc
  have hr := hc'.rotate
  have hsx : endOf x ((h, y) :: L₁ ++ M₁) = endOf (endOf y L₁) M₁ := by
    rw [List.cons_append, endOf_cons, endOf_append]
  rw [hsx] at hr
  refine ⟨_, M₂ ++ (h, y) :: L₁, M₁, by simpa using hr, by simp, ?_, by simp, hs, ?_, ?_⟩
  · rintro rfl
    apply hzw
    have key : ∀ p ∈ y :: (L₁ ++ M₂).map Prod.snd, P p → p = endOf y L₁ := by
      intro p hp hP
      have hsplit : y :: (L₁ ++ M₂).map Prod.snd =
          (y :: L₁.map Prod.snd).dropLast ++ [endOf y L₁] ++ M₂.map Prod.snd := by
        rw [← vertices_eq]
        simp
      rw [hsplit] at hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with (hp | hp) | hp
      · exact absurd hP (hout₁ p hp)
      · exact hp
      · exact absurd hP (hout₂ p hp)
    rw [List.nil_append] at hz hw
    rw [key z hz hzP, key w hw hwP]
  · rw [endOf_append, endOf_cons]
    exact ht
  · intro p hp
    rw [List.map_append, List.dropLast_append_of_ne_nil (by simp), List.mem_append] at hp
    rcases hp with hp | hp
    · exact hout₂ p hp
    · exact hout₁ p hp

/-- **An arc**: two different vertices of a cycle are joined by a path along the cycle holding any
given link of it. -/
theorem arc {x s t e : ℕ} {c : List (ℕ × ℕ)} (hc : IsCycle g x c) (hs : s ∈ c.map Prod.snd)
    (ht : t ∈ c.map Prod.snd) (hst : s ≠ t) (he : e ∈ c.map Prod.fst) :
    ∃ A, IsPath g t A s ∧ e ∈ A.map Prod.fst ∧ ∀ p ∈ A.map Prod.snd, p ∈ c.map Prod.snd := by
  obtain ⟨D, hD, hperm⟩ := hc.rotate_vertex ht
  have hsub : ∀ p ∈ D.map Prod.snd, p ∈ c.map Prod.snd :=
    fun p hp => (hperm.map Prod.snd).subset hp
  obtain ⟨⟨f, s'⟩, hm, rfl⟩ := List.mem_map.mp ((hperm.map Prod.snd).mem_iff.mpr hs)
  obtain ⟨r₁, r₂, rfl⟩ := List.append_of_mem hm
  have hD' : IsCycle g t ((r₁ ++ [(f, s')]) ++ r₂) := by simpa using hD
  have hend : endOf t (r₁ ++ [(f, s')]) = s' := by rw [endOf_append, endOf_singleton]
  have hr₂ : r₂ ≠ [] := by
    rintro rfl
    have := hD'.closed
    rw [List.append_nil, hend] at this
    exact hst this
  obtain ⟨hp₁, hp₂⟩ := hD'.split (by simp) hr₂
  rw [hend] at hp₁ hp₂
  have he' : e ∈ (r₁ ++ [(f, s')]).map Prod.fst ∨ e ∈ r₂.map Prod.fst := by
    have := (hperm.map Prod.fst).mem_iff.mpr he
    simpa [or_assoc] using this
  rcases he' with he' | he'
  · refine ⟨_, hp₁, he', fun p hp => hsub p ?_⟩
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil] at hp ⊢
    tauto
  · refine ⟨_, hp₂.reverse, by rwa [map_fst_revSteps, List.mem_reverse], fun p hp => ?_⟩
    have hp' : p ∈ endOf s' r₂ :: (revSteps s' r₂).map Prod.snd := List.mem_cons_of_mem _ hp
    rw [vertices_revSteps, List.mem_reverse, List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · exact hs
    · exact hsub p (by simp [hp'])

/-- A vertex a walk steps to is its end or a vertex before the end. -/
theorem mem_dropLast_or {x p : ℕ} {c : List (ℕ × ℕ)} (hp : p ∈ c.map Prod.snd) :
    p ∈ (c.map Prod.snd).dropLast ∨ p = endOf x c := by
  have hne : c.map Prod.snd ≠ [] := List.ne_nil_of_mem hp
  have hl : endOf x c = (c.map Prod.snd).getLast hne := List.getLast_cons hne
  rw [← List.dropLast_append_getLast hne, List.mem_append, List.mem_singleton] at hp
  rwa [hl]

/-- **Two cycles through a common link give a cycle through `e` and `h`**: the first holds `e`
and `f`, the second `f` and `h`, and `h` is not on the first. The second leaves the first and
comes back to it through `h`; that detour and the arc of the first holding `e` are a cycle. -/
theorem exists_cycle_of_cycles {x₁ x₂ e f h : ℕ} {c₁ c₂ : List (ℕ × ℕ)}
    (hc₁ : IsCycle g x₁ c₁) (he : e ∈ c₁.map Prod.fst) (hf₁ : f ∈ c₁.map Prod.fst)
    (hc₂ : IsCycle g x₂ c₂) (hf₂ : f ∈ c₂.map Prod.fst) (hh : h ∈ c₂.map Prod.fst)
    (hh₁ : h ∉ c₁.map Prod.fst) :
    ∃ s c, IsCycle g s c ∧ e ∈ c.map Prod.fst ∧ h ∈ c.map Prod.fst := by
  -- the two ends of `f` are two vertices of both cycles
  obtain ⟨⟨f', w⟩, hmf, rfl⟩ := List.mem_map.mp hf₂
  obtain ⟨z, rest, hcf, hpermf, hjf⟩ := hc₂.rotate_step hmf
  have hrest : rest ≠ [] := by
    rintro rfl
    have := (hpermf.map Prod.fst).mem_iff.mpr hh
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at this
    exact hh₁ (this ▸ hf₁)
  have hpf := (hcf.split (c₁ := [(f', w)]) (by simp) hrest).2
  rw [endOf_singleton] at hpf
  obtain ⟨s₀, l₀, hl₀⟩ := List.exists_cons_of_ne_nil hrest
  have hzw : z ≠ w := by
    subst hl₀
    exact fun hzw => endOf_ne hpf.nodup (hpf.endOf_eq.trans hzw)
  have hz₁ : z ∈ c₁.map Prod.snd := hc₁.mem_of_isEnd hf₁ ⟨w, hjf⟩
  have hw₁ : w ∈ c₁.map Prod.snd := hc₁.mem_of_isEnd hf₁ ⟨z, hjf.symm⟩
  have hz₂ : z ∈ c₂.map Prod.snd :=
    (hpermf.map Prod.snd).subset (hcf.closed ▸ endOf_mem_of_ne_nil (by simp))
  have hw₂ : w ∈ c₂.map Prod.snd := (hpermf.map Prod.snd).subset (by simp)
  -- the detour through `h`
  obtain ⟨⟨h', y⟩, hmh, rfl⟩ := List.mem_map.mp hh
  obtain ⟨x, B, hch, hpermh, -⟩ := hc₂.rotate_step hmh
  have hz : z ∈ y :: B.map Prod.snd := by
    simpa using (hpermh.map Prod.snd).mem_iff.mpr hz₂
  have hw : w ∈ y :: B.map Prod.snd := by
    simpa using (hpermh.map Prod.snd).mem_iff.mpr hw₂
  obtain ⟨s, Q, R, hQR, hQ, hR, hhQ, hsP, htP, hin⟩ :=
    detour (fun p => p ∈ c₁.map Prod.snd) hch hz hw hz₁ hw₁ hzw
  obtain ⟨hpQ, -⟩ := hQR.split hQ hR
  have hst : s ≠ endOf s Q := by
    obtain ⟨q, l, rfl⟩ := List.exists_cons_of_ne_nil hQ
    exact fun h => endOf_ne hpQ.nodup h.symm
  -- the arc of the first cycle holding `e`
  obtain ⟨A, hA, heA, hAsub⟩ := arc hc₁ hsP htP hst he
  -- the two make a cycle
  have htr : Trail g s (Q ++ A) := trail_append.mpr ⟨hpQ.trail, hA.trail⟩
  have hcl : endOf s (Q ++ A) = s := by rw [endOf_append]; exact hA.endOf_eq
  have hnd : ((Q ++ A).map Prod.snd).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨(List.nodup_cons.mp hpQ.nodup).2, (List.nodup_cons.mp hA.nodup).2, ?_⟩
    rintro p hp q hq rfl
    rcases mem_dropLast_or (x := s) hp with hp | hp
    · exact hin p hp (hAsub p hq)
    · exact (List.nodup_cons.mp hA.nodup).1 (hp ▸ hq)
  refine ⟨s, Q ++ A, ⟨htr, hcl, hnd, ?_⟩, by simp [heA], by simp [hhQ]⟩
  by_cases h3 : 3 ≤ (Q ++ A).length
  · exact links_nodup_of_three htr hcl hnd h3
  · have hA0 : A ≠ [] := List.ne_nil_of_mem (List.mem_map.mp heA).choose_spec.1
    obtain ⟨q, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
    obtain ⟨a, A', rfl⟩ := List.exists_cons_of_ne_nil hA0
    have hQ' : Q' = [] := by
      rcases Q' with _ | ⟨_, _⟩
      · rfl
      · simp at h3
    have hA' : A' = [] := by
      rcases A' with _ | ⟨_, _⟩
      · rfl
      · simp at h3; omega
    subst hQ' hA'
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hhQ heA
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    rintro hqa
    exact hh₁ (by rw [hhQ, hqa, ← heA]; exact he)

/-- Two links on a common cycle with a third, and different, are on a common cycle. -/
theorem onCycleWith_trans {e f h : ℕ} (h₁ : OnCycleWith g e f) (h₂ : OnCycleWith g f h)
    (heh : e ≠ h) : OnCycleWith g e h := by
  obtain ⟨-, x₁, c₁, hc₁, he, hf₁⟩ := onCycleWith_iff.mp h₁
  obtain ⟨-, x₂, c₂, hc₂, hf₂, hh⟩ := onCycleWith_iff.mp h₂
  refine onCycleWith_iff.mpr ⟨heh, ?_⟩
  by_cases hh₁ : h ∈ c₁.map Prod.fst
  · exact ⟨x₁, c₁, hc₁, he, hh₁⟩
  · exact exists_cycle_of_cycles hc₁ he hf₁ hc₂ hf₂ hh hh₁

/-- Blocks are classes: two links on a common cycle with a third are on a common cycle. -/
theorem sameBlock_trans {e f h : ℕ} (h₁ : SameBlock g e f) (h₂ : SameBlock g f h) :
    SameBlock g e h := by
  obtain ⟨he, -, h₁⟩ := h₁
  obtain ⟨-, hh, h₂⟩ := h₂
  refine ⟨he, hh, ?_⟩
  by_cases heh : e = h
  · exact Or.inl heh
  rcases h₁ with rfl | h₁
  · exact h₂
  rcases h₂ with rfl | h₂
  · exact Or.inr h₁
  exact Or.inr (onCycleWith_trans h₁ h₂ heh)

end AlgoDesign.Graphs.Blocks
