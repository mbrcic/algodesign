/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Dijkstra.Basic

/-!
# Breadth-first search: the fewest arrows

Sources: the Paths chapter; Weiss, *Data Structures and Algorithm Analysis in C++* (4th ed.),
Fig. 9.18 (p. 392), and Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*
(4th ed.), §20.2 (p. 556), for the first-in-first-out queue and a vertex marked when it is first
found.

Every arrow costs one, so a path's length is its number of arrows. The search keeps a
first-in-first-out queue of the vertices found and not yet left, each with its distance. It takes
the front vertex, leaves it, and walks its row in order: each neighbor not yet found gets the
front's distance plus one, the front as its previous vertex, and a place at the back of the queue.

The key fact is the frontier: the distances in the queue never decrease from front to back, and
differ by at most one, so the queue holds every vertex at distance `k` before any at `k + 1`
(`QueueInOrder`). With it, the first time a vertex is found is along a path of the fewest arrows.
A path here is a path of the network whose arrows each cost one, `unit g`.
-/

@[expose] public section

namespace AlgoDesign.Paths.Bfs

open AlgoDesign.Graphs Network Dijkstra

/-- The network of `g` in which every arrow costs one. -/
def unit (g : Digraph) : Network := ⟨g, List.replicate g.arrows.length 1⟩

/-- **`c` is the fewest arrows of a path from `s` to `v` among those `ok` admits**: no such path
has fewer, and some such path has exactly `c`; `c` is `none` exactly when there is no such path. -/
def FewestAmong (g : Digraph) (ok : List ℕ → Prop) (s v : ℕ) (c : Option ℕ) : Prop :=
  (∀ p, (unit g).IsPath s p v → ok p → ∃ d ∈ c, d ≤ p.length) ∧
    ∀ d ∈ c, ∃ p, (unit g).IsPath s p v ∧ ok p ∧ p.length = d

/-- **`c` is the fewest arrows of any path from `s` to `v`**, `none` when no path leads there. -/
def Fewest (g : Digraph) (s v : ℕ) (c : Option ℕ) : Prop := FewestAmong g (fun _ => True) s v c

/-! ## The search's state -/

/-- **The state of the search.** -/
structure State where
  /-- The vertices left so far, in the order they were taken off the queue. -/
  left : List ℕ
  /-- Each vertex's distance; `none` while it has not been found. -/
  dist : ℕ → Option ℕ
  /-- Each vertex's recorded previous vertex. -/
  prev : ℕ → Option ℕ
  /-- The vertices found and not yet left, each with its distance, front first. -/
  queue : List (ℕ × ℕ)

/-- Every vertex left has the fewest arrows of any path, and none is left twice. -/
def LeftAreFewest (g : Digraph) (s : ℕ) (st : State) : Prop :=
  st.left.Nodup ∧ ∀ v ∈ st.left, st.dist v ≠ none ∧ Fewest g s v (st.dist v)

/-- Every vertex not left has, as its distance, the fewest arrows of a path on which every earlier
vertex has been left. -/
def FoundAreFewestThroughLeft (g : Digraph) (s : ℕ) (st : State) : Prop :=
  ∀ v < g.n, v ∉ st.left → FewestAmong g (Through (unit g) st.left s) s v (st.dist v)

/-- **The frontier**: the distances in the queue never decrease from front to back and differ by
at most one, and no vertex left is farther than any in the queue. -/
def QueueInOrder (st : State) : Prop :=
  (st.queue.map Prod.snd).Pairwise (· ≤ ·) ∧ (∀ a ∈ st.queue, ∀ b ∈ st.queue, b.2 ≤ a.2 + 1) ∧
    ∀ x ∈ st.left, ∀ dx ∈ st.dist x, ∀ e ∈ st.queue, dx ≤ e.2

/-- The queue holds, once each, exactly the vertices found and not left, with their distances. -/
def QueueIsFound (g : Digraph) (st : State) : Prop :=
  (st.queue.map Prod.fst).Nodup ∧
    (∀ e ∈ st.queue, e.1 < g.n ∧ e.1 ∉ st.left ∧ st.dist e.1 = some e.2) ∧
    ∀ v < g.n, v ∉ st.left → ∀ d ∈ st.dist v, (v, d) ∈ st.queue

/-- Every arrow out of a vertex left leads to a vertex found, at most one farther. -/
def LeftRowsFound (g : Digraph) (st : State) : Prop :=
  ∀ x ∈ st.left, ∀ e ∈ g.out x, ∀ dx ∈ st.dist x, ∃ d ∈ st.dist e.1, d ≤ dx + 1

/-- Following the previous vertices back from a vertex found gives a path from the start with
exactly its distance in arrows, every earlier vertex of it left. -/
def PreviousLeadsBack (g : Digraph) (s : ℕ) (st : State) : Prop :=
  st.prev s = none ∧ ∀ v < g.n, ∀ d ∈ st.dist v, ∃ p, (unit g).IsPath s p v ∧ p.length = d ∧
    Through (unit g) st.left s p ∧ LeadsBack st.prev s ((unit g).visits s p)

/-- Once a vertex is left, the start is the first. -/
def StartLeftFirst (s : ℕ) (st : State) : Prop := st.left ≠ [] → st.left.head? = some s

/-- **A legal state of the search.** -/
def Valid (g : Digraph) (s : ℕ) (st : State) : Prop :=
  LeftAreFewest g s st ∧ FoundAreFewestThroughLeft g s st ∧ QueueInOrder st ∧
    QueueIsFound g st ∧ LeftRowsFound g st ∧ PreviousLeadsBack g s st ∧ StartLeftFirst s st

/-! ## The search -/

/-- **Look along one arrow** `(w, i)` out of `u`, at distance `du`: if `w` has not been found,
it gets distance `du + 1`, previous vertex `u`, and a place at the back of the queue. -/
def tryArrow (u du : ℕ) (st : State) (e : ℕ × ℕ) : State :=
  if st.dist e.1 = none then
    { st with
      dist := Function.update st.dist e.1 (some (du + 1))
      prev := Function.update st.prev e.1 (some u)
      queue := st.queue ++ [(e.1, du + 1)] }
  else st

/-- **The start**: nothing left; the start found at distance 0 and queued. -/
def start (s : ℕ) : State :=
  ⟨[], Function.update (fun _ => none) s (some 0), fun _ => none, [(s, 0)]⟩

/-- **One step**: take the front vertex off the queue, leave it, and look along every arrow out of
it, in its row's order. -/
def step (g : Digraph) (st : State) : State :=
  match st.queue with
  | [] => st
  | (u, du) :: q => (g.out u).foldl (tryArrow u du) { st with left := st.left ++ [u], queue := q }

/-- Take steps while the queue is not empty, at most `f` of them. -/
def runSteps (g : Digraph) : ℕ → State → State
  | 0, st => st
  | f + 1, st => if st.queue = [] then st else runSteps g f (step g st)

/-- **The answer**: each vertex's distance in arrows, `none` for a vertex that cannot be reached,
and its previous vertex. -/
structure Answer where
  /-- Each vertex's distance; `none` reports it unreachable. -/
  dist : ℕ → Option ℕ
  /-- Each vertex's recorded previous vertex. -/
  prev : ℕ → Option ℕ

/-- **Breadth-first search**: steps until the queue is empty, at most one per vertex. -/
def bfs (g : Digraph) (s : ℕ) : Answer :=
  let st := runSteps g g.n (start s)
  ⟨st.dist, st.prev⟩

/-! ## Deciding the pieces -/

instance (g : Digraph) (ok : List ℕ → Prop) [DecidablePred ok] (s v : ℕ) (c : Option ℕ) :
    Decidable (FewestAmong g ok s v c) :=
  decidable_of_iff
    ((∀ p ∈ (unit g).candidates, (unit g).IsPath s p v → ok p → ∃ d ∈ c, d ≤ p.length) ∧
      ∀ d ∈ c, ∃ p ∈ (unit g).candidates, (unit g).IsPath s p v ∧ ok p ∧ p.length = d)
    ⟨fun ⟨h1, h2⟩ => ⟨fun p hp => h1 p hp.mem_candidates hp, fun d hd => by
        obtain ⟨p, -, h⟩ := h2 d hd; exact ⟨p, h⟩⟩,
      fun ⟨h1, h2⟩ => ⟨fun p _ => h1 p, fun d hd => by
        obtain ⟨p, hp, h⟩ := h2 d hd; exact ⟨p, hp.mem_candidates, hp, h⟩⟩⟩

instance (g : Digraph) (s v : ℕ) (c : Option ℕ) : Decidable (Fewest g s v c) :=
  inferInstanceAs (Decidable (FewestAmong g (fun _ => True) s v c))

theorem previousLeadsBack_iff {g : Digraph} {s : ℕ} {st : State} :
    PreviousLeadsBack g s st ↔ st.prev s = none ∧ ∀ v < g.n, ∀ d ∈ st.dist v,
      ∃ p ∈ (unit g).candidates, (unit g).IsPath s p v ∧ p.length = d ∧
        Through (unit g) st.left s p ∧ LeadsBack st.prev s ((unit g).visits s p) := by
  unfold PreviousLeadsBack
  refine and_congr_right fun _ => forall₂_congr fun v _ => forall₂_congr fun d _ => ?_
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp.mem_candidates, hp, h⟩, fun ⟨p, _, h⟩ => ⟨p, h⟩⟩

instance (g : Digraph) (s : ℕ) (st : State) : Decidable (PreviousLeadsBack g s st) :=
  decidable_of_iff' _ previousLeadsBack_iff

instance (g : Digraph) (s : ℕ) (st : State) : Decidable (LeftAreFewest g s st) := by
  unfold LeftAreFewest; infer_instance

instance (g : Digraph) (s : ℕ) (st : State) : Decidable (FoundAreFewestThroughLeft g s st) := by
  unfold FoundAreFewestThroughLeft; infer_instance

instance (st : State) : Decidable (QueueInOrder st) := by
  unfold QueueInOrder; infer_instance

instance (g : Digraph) (st : State) : Decidable (QueueIsFound g st) := by
  unfold QueueIsFound; infer_instance

instance (g : Digraph) (st : State) : Decidable (LeftRowsFound g st) := by
  unfold LeftRowsFound; infer_instance

instance (s : ℕ) (st : State) : Decidable (StartLeftFirst s st) := by
  unfold StartLeftFirst; infer_instance

instance (g : Digraph) (s : ℕ) (st : State) : Decidable (Valid g s st) := by
  unfold Valid; infer_instance

/-! ## Looking along the arrows out of the front vertex -/

/-- What looking along the arrows `l` out of `u`, at distance `du`, does to a state `st`, giving
`st'`: a vertex found keeps its distance and previous vertex, each vertex newly found gets `du + 1`
and `u`, and is queued at the back. -/
structure Looks (g : Digraph) (u du : ℕ) (l : List (ℕ × ℕ)) (st st' : State) : Prop where
  left : st'.left = st.left
  keeps : ∀ x d, st.dist x = some d → st'.dist x = some d ∧ st'.prev x = st.prev x
  found : ∀ x, st.dist x = none →
    (st'.dist x = none ∧ st'.prev x = st.prev x) ∨
      (st'.dist x = some (du + 1) ∧ st'.prev x = some u ∧ ∃ e ∈ l, e.1 = x)
  marks : ∀ e ∈ l, st'.dist e.1 ≠ none
  added : ∃ new, st'.queue = st.queue ++ new ∧ (new.map Prod.fst).Nodup ∧
    (∀ e ∈ new, e.2 = du + 1 ∧ st.dist e.1 = none ∧ st'.dist e.1 = some (du + 1) ∧ e.1 < g.n) ∧
    ∀ x d, st.dist x = none → st'.dist x = some d → (x, d) ∈ new

theorem Looks.nil (g : Digraph) (u du : ℕ) (st : State) : Looks g u du [] st st where
  left := rfl
  keeps _ _ h := ⟨h, rfl⟩
  found _ h := Or.inl ⟨h, rfl⟩
  marks _ h := absurd h (by simp)
  added := ⟨[], by simp, by simp, by simp, fun x d h h' => absurd (h.symm.trans h') (by simp)⟩

theorem looks_tryArrow (g : Digraph) (u du : ℕ) (st : State) {e : ℕ × ℕ} (he : e.1 < g.n) :
    Looks g u du [e] st (tryArrow u du st e) := by
  unfold tryArrow
  split_ifs with hd
  · refine
      { left := rfl
        keeps := fun x d hx => ?_
        found := fun x hx => ?_
        marks := fun e' he' => ?_
        added := ⟨[(e.1, du + 1)], rfl, by simp, fun e' he' => ?_, fun x d hx hx' => ?_⟩ }
    · have hne : x ≠ e.1 := fun h => by rw [h, hd] at hx; exact absurd hx (by simp)
      simp [Function.update_of_ne hne, hx]
    · by_cases hxe : x = e.1
      · subst hxe; exact Or.inr ⟨by simp, by simp, e, by simp, rfl⟩
      · exact Or.inl ⟨by simp [Function.update_of_ne hxe, hx], by simp [hxe]⟩
    · rw [List.mem_singleton.1 he']; simp
    · rw [List.mem_singleton.1 he']; exact ⟨rfl, hd, by simp, he⟩
    · by_cases hxe : x = e.1
      · subst hxe
        simp only [Function.update_self, Option.some.injEq] at hx'
        simp [hx']
      · simp [Function.update_of_ne hxe, hx] at hx'
  · refine
      { left := rfl
        keeps := fun _ _ h => ⟨h, rfl⟩
        found := fun _ h => Or.inl ⟨h, rfl⟩
        marks := fun e' he' => by rw [List.mem_singleton.1 he']; exact hd
        added := ⟨[], by simp, by simp, by simp,
          fun x d h h' => absurd (h.symm.trans h') (by simp)⟩ }

theorem Looks.append {g : Digraph} {u du : ℕ} {l₁ l₂ : List (ℕ × ℕ)} {st st₁ st₂ : State}
    (h₁ : Looks g u du l₁ st st₁) (h₂ : Looks g u du l₂ st₁ st₂) :
    Looks g u du (l₁ ++ l₂) st st₂ where
  left := h₂.left.trans h₁.left
  keeps x d h := by
    obtain ⟨a, b⟩ := h₁.keeps x d h
    obtain ⟨c, e⟩ := h₂.keeps x d a
    exact ⟨c, e.trans b⟩
  found x h := by
    rcases h₁.found x h with ⟨a, b⟩ | ⟨a, b, e₀, he₀, hx₀⟩
    · rcases h₂.found x a with ⟨c, e⟩ | ⟨c, e, e₀, he₀, hx₀⟩
      · exact Or.inl ⟨c, e.trans b⟩
      · exact Or.inr ⟨c, e, e₀, List.mem_append_right _ he₀, hx₀⟩
    · obtain ⟨c, e⟩ := h₂.keeps x _ a
      exact Or.inr ⟨c, e.trans b, e₀, List.mem_append_left _ he₀, hx₀⟩
  marks e he := by
    rcases List.mem_append.1 he with he | he
    · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 (h₁.marks e he)
      rw [(h₂.keeps _ d hd).1]; simp
    · exact h₂.marks e he
  added := by
    obtain ⟨n₁, q₁, nd₁, e₁, f₁⟩ := h₁.added
    obtain ⟨n₂, q₂, nd₂, e₂, f₂⟩ := h₂.added
    refine ⟨n₁ ++ n₂, by rw [q₂, q₁, List.append_assoc], ?_, fun e he => ?_, fun x d hx hx' => ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨nd₁, nd₂, fun a ha b hb hab => ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
      have := (e₂ e' he').2.1
      rw [← hab, (e₁ e he).2.2.1] at this
      exact absurd this (by simp)
    · rcases List.mem_append.1 he with he | he
      · obtain ⟨a, b, c, d⟩ := e₁ e he
        exact ⟨a, b, (h₂.keeps _ _ c).1, d⟩
      · obtain ⟨a, b, c, d⟩ := e₂ e he
        refine ⟨a, ?_, c, d⟩
        rcases h₁.found e.1 (by
          cases h : st.dist e.1 with
          | none => rfl
          | some v => rw [(h₁.keeps _ v h).1] at b; exact absurd b (by simp)) with
          ⟨x, -⟩ | ⟨x, -⟩
        · cases h : st.dist e.1 with
          | none => rfl
          | some v => rw [(h₁.keeps _ v h).1] at b; exact absurd b (by simp)
        · rw [x] at b; exact absurd b (by simp)
    · rcases h₁.found x hx with ⟨a, -⟩ | ⟨a, -, -⟩
      · exact List.mem_append_right _ (f₂ x d a hx')
      · have := (h₂.keeps x _ a).1
        rw [this] at hx'
        cases hx'
        exact List.mem_append_left _ (f₁ x _ hx a)

theorem looks_foldl (g : Digraph) (u du : ℕ) :
    ∀ (l : List (ℕ × ℕ)) (st : State), (∀ e ∈ l, e.1 < g.n) →
      Looks g u du l st (l.foldl (tryArrow u du) st)
  | [], st, _ => Looks.nil g u du st
  | e :: l, st, h => by
    rw [List.foldl_cons]
    exact (looks_tryArrow g u du st (h e (by simp))).append
      (looks_foldl g u du l _ fun e' he' => h e' (by simp [he']))

/-! ## One step keeps the search legal -/

variable {g : Digraph} {s : ℕ}

theorem mem_dist_start {v d : ℕ} : d ∈ (start s).dist v ↔ v = s ∧ d = 0 := by
  by_cases hv : v = s
  · subst hv; simp [start, eq_comm]
  · simp [start, hv]

theorem valid_start (hs : s < g.n) : Valid g s (start s) := by
  refine ⟨⟨List.nodup_nil, fun v hv => absurd hv (by simp [start])⟩, fun v _ _ => ⟨?_, ?_⟩,
    ⟨by simp [start], by simp [start], fun x hx => absurd hx (by simp [start])⟩,
    ⟨by simp [start], fun e he => ?_, fun v _ _ d hd => ?_⟩,
    fun x hx => absurd hx (by simp [start]), ⟨rfl, fun v _ d hd => ?_⟩, fun h => absurd rfl h⟩
  · intro p hp ht
    obtain rfl := eq_nil_of_through_nil ht
    rw [isPath_nil_iff.1 hp]
    simp [start]
  · intro d hd
    obtain ⟨rfl, rfl⟩ := mem_dist_start.1 hd
    exact ⟨[], isPath_nil v, through_nil _ _, rfl⟩
  · simp only [start, List.mem_singleton] at he
    subst he
    exact ⟨hs, by simp [start], by simp [start]⟩
  · obtain ⟨rfl, rfl⟩ := mem_dist_start.1 hd
    simp [start]
  · obtain ⟨rfl, rfl⟩ := mem_dist_start.1 hd
    exact ⟨[], isPath_nil v, rfl, through_nil _ _, rfl, by simp [visits]⟩

/-- The front of the queue: a vertex of the graph not yet left, at its distance; every entry is
no nearer, and at most one farther. -/
theorem front_spec {st : State} {u du : ℕ} {q : List (ℕ × ℕ)} (hO : QueueInOrder st)
    (hF : QueueIsFound g st) (hq : st.queue = (u, du) :: q) :
    u < g.n ∧ u ∉ st.left ∧ st.dist u = some du ∧ ∀ e ∈ st.queue, du ≤ e.2 ∧ e.2 ≤ du + 1 := by
  obtain ⟨hu, hul, hdu⟩ := hF.2.1 (u, du) (by simp [hq])
  refine ⟨hu, hul, hdu, fun e he => ⟨?_, hO.2.1 (u, du) (by simp [hq]) e he⟩⟩
  have h := hO.1
  rw [hq, List.map_cons, List.pairwise_cons] at h
  rw [hq] at he
  rcases List.mem_cons.1 he with rfl | he
  · exact le_rfl
  · exact h.1 _ (List.mem_map_of_mem he)

/-- **One step keeps the search legal.** -/
theorem valid_step (hN : g.WellFormed) (hs : s < g.n) {st : State} (h : Valid g s st)
    (hne : st.queue ≠ []) : Valid g s (step g st) := by
  obtain ⟨hA, hB, hO, hF, hR, hP, hS⟩ := h
  obtain ⟨⟨u, du⟩, q, hq⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨hun, hul, hdu, hfront⟩ := front_spec hO hF hq
  have hmarked : ∀ x ∈ st.left, ∃ d, st.dist x = some d := fun x hx =>
    Option.ne_none_iff_exists'.1 (hA.2 x hx).1
  have hstep : step g st = (g.out u).foldl (tryArrow u du)
      { st with left := st.left ++ [u], queue := q } := by
    unfold step; rw [hq]
  rw [hstep]
  have L := looks_foldl g u du (g.out u) { st with left := st.left ++ [u], queue := q }
    fun e he => (mem_out.1 he).1
  set st' := (g.out u).foldl (tryArrow u du) { st with left := st.left ++ [u], queue := q }
  have hL : st'.left = st.left ++ [u] := L.left
  have keep : ∀ x d, st.dist x = some d → st'.dist x = some d ∧ st'.prev x = st.prev x :=
    L.keeps
  obtain ⟨new, hq', hnew_nd, hnew, hnew_all⟩ := L.added
  -- the start is left first
  have hhead : (st.left ++ [u]).head? = some s := by
    cases hl : st.left with
    | nil =>
      obtain ⟨p, hp, -, ht, -⟩ := hP.2 u hun du hdu
      rw [hl] at ht
      rw [eq_nil_of_through_nil ht] at hp
      rw [isPath_nil_iff.1 hp]; rfl
    | cons a l =>
      have := hS (by simp [hl])
      rw [hl] at this; exact this
  have hsL : s ∈ st.left ++ [u] := List.mem_of_mem_head? hhead
  -- what an arrow out of the front vertex leaves its head with
  have row_u : ∀ e ∈ g.out u, ∃ d ∈ st'.dist e.1, d ≤ du + 1 := by
    intro e he
    cases hd : st.dist e.1 with
    | none =>
      rcases L.found e.1 hd with ⟨h1, -⟩ | ⟨h1, -, -⟩
      · exact absurd h1 (L.marks e he)
      · exact ⟨du + 1, h1, le_rfl⟩
    | some dw =>
      refine ⟨dw, (keep _ _ hd).1, ?_⟩
      by_cases hwl : e.1 ∈ st.left
      · have := hO.2.2 e.1 hwl dw hd (u, du) (by simp [hq]); omega
      · have := hF.2.2 e.1 (mem_out.1 he).1 hwl dw hd
        exact (hfront _ this).2
  have hsdist : ∀ x ∈ st.left ++ [u], ∃ d, st.dist x = some d := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hmarked x hx
    · rw [List.mem_singleton.1 hx]; exact ⟨du, hdu⟩
  -- the paths back
  have hP' : PreviousLeadsBack g s st' := by
    obtain ⟨d0, hd0⟩ := hsdist s hsL
    have hprev_s : st'.prev s = none := (keep s d0 hd0).2.trans hP.1
    refine ⟨hprev_s, fun v hv d hd => ?_⟩
    rw [hL]
    have hkeepl : ∀ b ∈ st.left ++ [u], st'.prev b = st.prev b := fun b hb => by
      obtain ⟨d, hd⟩ := hsdist b hb; exact (keep b d hd).2
    cases hdv : st.dist v with
    | some d' =>
      have := (keep v d' hdv).1
      rw [this, Option.mem_def, Option.some.injEq] at hd
      subst hd
      obtain ⟨p, hp, hc, ht, hl⟩ := hP.2 v hv d' hdv
      refine ⟨p, hp, hc, through_mono ht fun x hx => List.mem_append_left _ hx, hprev_s,
        hl.2.imp_of_mem_imp fun a b _ hb hab => ?_⟩
      rw [hp.visits_eq] at hb
      rcases List.mem_append.1 hb with hb | hb
      · rw [hkeepl b (List.mem_append_left _ (ht b hb))]; exact hab
      · rw [List.mem_singleton.1 hb, (keep v d' hdv).2]
        rw [List.mem_singleton.1 hb] at hab; exact hab
    | none =>
      rcases L.found v hdv with ⟨h1, -⟩ | ⟨h1, hpv, ⟨w, i⟩, he, hw⟩
      · rw [h1] at hd; exact absurd hd (by simp)
      simp only at hw
      subst hw
      rw [h1, Option.mem_def, Option.some.injEq] at hd
      subst hd
      have hi := (mem_out.1 he).2
      obtain ⟨p, hp, hc, ht, hl⟩ := hP.2 u hun du hdu
      have hwl : w ∉ st.left ++ [u] := fun hw => by
        obtain ⟨d, hd⟩ := hsdist w hw; rw [hdv] at hd; exact absurd hd (by simp)
      have hwp : w ∉ (unit g).visits s p := by
        rw [hp.visits_eq]
        intro hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hwl (List.mem_append_left _ (ht w hm))
        · exact hwl (List.mem_append_right _ hm)
      obtain ⟨hp', hv'⟩ := hp.snoc (N := unit g) hi hwp
      refine ⟨p ++ [i], hp', by simp [hc], fun x hx => ?_, hprev_s, ?_⟩
      · rw [hv', List.dropLast_concat, hp.visits_eq] at hx
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append_left _ (ht x hx)
        · exact List.mem_append_right _ hx
      · rw [hv']
        refine List.IsChain.append (hl.2.imp_of_mem_imp fun a b _ hb hab => ?_)
          (List.isChain_singleton w) ?_
        · have hb' : b ∈ st.left ++ [u] := by
            rw [hp.visits_eq] at hb
            rcases List.mem_append.1 hb with hb | hb
            · exact List.mem_append_left _ (ht b hb)
            · exact List.mem_append_right _ hb
          rw [hkeepl b hb']; exact hab
        · intro x hx y hy
          rw [hp.visits_eq] at hx
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
            Option.mem_def, Option.some.injEq] at hx
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          rw [← hx, ← hy, hpv]
  -- the queue after the step: the rest of the old one, then the new vertices, all at `du + 1`
  have hq'' : st'.queue = q ++ new := hq'
  have hq_old : ∀ e ∈ q, e ∈ st.queue := fun e he => by rw [hq]; exact List.mem_cons_of_mem _ he
  have hqu : ∀ e ∈ q, e.1 ≠ u := by
    intro e he heu
    have hnd := hF.1
    rw [hq, List.map_cons, List.nodup_cons] at hnd
    exact hnd.1 (List.mem_map.2 ⟨e, he, heu⟩)
  have hbounds : ∀ e ∈ st'.queue, du ≤ e.2 ∧ e.2 ≤ du + 1 := by
    intro e he
    rw [hq''] at he
    rcases List.mem_append.1 he with he | he
    · exact hfront e (hq_old e he)
    · rw [(hnew e he).1]; omega
  refine ⟨⟨?_, fun x hx => ?_⟩, fun w hw hwl => ⟨fun p hp ht => ?_, fun d hd => ?_⟩,
    ⟨?_, fun a _ b hb => ?_, fun x hx dx hdx e he => ?_⟩,
    ⟨?_, fun e he => ?_, fun v hv hvl d hd => ?_⟩,
    fun x hx e he dx hdx => ?_, hP', fun _ => hL ▸ hhead⟩
  · rw [hL]; exact hA.1.append (List.nodup_singleton u) (by simpa using hul)
  · -- the vertex just left has the fewest arrows
    rw [hL] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨d, hd⟩ := hmarked x hx
      rw [(keep x d hd).1]
      have := hA.2 x hx
      rw [hd] at this
      exact this
    rw [List.mem_singleton.1 hx, (keep u du hdu).1]
    refine ⟨by simp, fun p hp _ => ?_, fun d hd => ?_⟩
    · obtain ⟨q', r, y, rfl, hq', hyl, ht⟩ :=
        split_first_outside (N := unit g) hp ⟨u, hp.mem_visits, hul⟩
      have hy := hq'.lt (N := unit g) ⟨hN, by simp [unit]⟩ hs
      obtain ⟨dy, hdy, hdyq⟩ := (hB y hy hyl).1 q' hq' ht
      have := (hfront _ (hF.2.2 y hy hyl dy hdy)).1
      exact ⟨du, rfl, by simp only [List.length_append]; omega⟩
    · obtain ⟨p, hp, -, hc⟩ := (hB u hun hul).2 d (by rw [hdu]; exact hd)
      exact ⟨p, hp, trivial, hc⟩
  · -- a vertex not left: the fewest arrows through the vertices left
    rw [hL] at hwl
    rcases eq_or_ne p [] with rfl | hpne
    · rw [isPath_nil_iff.1 hp] at hwl; exact absurd hsL hwl
    obtain ⟨q', i, x, rfl, hq', hi, -, hvis⟩ := hp.eq_snoc hpne
    have ht' : ∀ y ∈ (unit g).visits s q', y ∈ st.left ++ [u] := by
      intro y hy
      exact hL ▸ ht y (by rw [hvis, List.dropLast_concat]; exact hy)
    have he : (w, i) ∈ g.out x := mem_out.2 ⟨hw, hi⟩
    rcases List.mem_append.1 (ht' x hq'.mem_visits) with hx | hx
    · obtain ⟨dx, hdx⟩ := hmarked x hx
      obtain ⟨dxq, hdxq, hle⟩ := (hA.2 x hx).2.1 q' hq' trivial
      rw [hdx, Option.mem_def, Option.some.injEq] at hdxq
      subst hdxq
      obtain ⟨dw, hdw, hdwle⟩ := hR x hx (w, i) he dx hdx
      exact ⟨dw, (keep w dw hdw).1, by simp only [List.length_append, List.length_singleton]; omega⟩
    · rw [List.mem_singleton.1 hx] at hq' he
      have hthrough : Through (unit g) st.left s q' := by
        intro y hy
        rcases List.mem_append.1 (ht' y ((List.dropLast_sublist _).subset hy)) with h | h
        · exact h
        · exact absurd (List.mem_singleton.1 h) (hq'.ne_of_mem_dropLast hy)
      obtain ⟨dq, hdq, hle⟩ := (hB u hun hul).1 q' hq' hthrough
      rw [hdu, Option.mem_def, Option.some.injEq] at hdq
      subst hdq
      obtain ⟨d, hd, hdle⟩ := row_u (w, i) he
      exact ⟨d, hd, by simp only [List.length_append, List.length_singleton]; omega⟩
  · obtain ⟨p, hp, hc, ht, -⟩ := hP'.2 w hw d hd
    exact ⟨p, hp, ht, hc⟩
  · -- the frontier
    rw [hq'', List.map_append, List.pairwise_append]
    have h := hO.1
    rw [hq, List.map_cons, List.pairwise_cons] at h
    refine ⟨h.2, ?_, fun a ha b hb => ?_⟩
    · refine List.pairwise_of_forall_mem_list fun a ha b hb => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
      rw [(hnew e he).1, (hnew e' he').1]
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
      rw [(hnew e' he').1]
      exact (hfront e (hq_old e he)).2
  · have := hbounds a ‹_›
    have := hbounds b hb
    omega
  · rw [hL] at hx
    have := (hbounds e he).1
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨d, hd⟩ := hmarked x hx
      rw [(keep x d hd).1, Option.mem_def, Option.some.injEq] at hdx
      subst hdx
      have := hO.2.2 x hx d hd (u, du) (by simp [hq])
      omega
    · rw [List.mem_singleton.1 hx, (keep u du hdu).1, Option.mem_def, Option.some.injEq] at hdx
      omega
  · -- the queue holds the vertices found and not left, once each
    rw [hq'', List.map_append, List.nodup_append]
    have hnd := hF.1
    rw [hq, List.map_cons, List.nodup_cons] at hnd
    refine ⟨hnd.2, hnew_nd, fun a ha b hb hab => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hb
    have := (hnew e' he').2.1
    rw [← hab, (hF.2.1 e (hq_old e he)).2.2] at this
    exact absurd this (by simp)
  · rw [hq''] at he
    rw [hL]
    rcases List.mem_append.1 he with he | he
    · obtain ⟨h1, h2, h3⟩ := hF.2.1 e (hq_old e he)
      refine ⟨h1, fun hm => ?_, (keep _ _ h3).1⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact h2 hm
      · exact hqu e he (List.mem_singleton.1 hm)
    · obtain ⟨h1, h2, h3, h4⟩ := hnew e he
      refine ⟨h4, fun hm => ?_, by rw [h3, h1]⟩
      obtain ⟨d, hd⟩ := hsdist e.1 hm
      rw [h2] at hd; exact absurd hd (by simp)
  · rw [hL] at hvl
    rw [hq'']
    cases hdv : st.dist v with
    | some d' =>
      rw [(keep v d' hdv).1, Option.mem_def, Option.some.injEq] at hd
      subst hd
      have := hF.2.2 v hv (fun h => hvl (List.mem_append_left _ h)) d' hdv
      rw [hq] at this
      rcases List.mem_cons.1 this with h | h
      · simp only [Prod.mk.injEq] at h
        exact absurd (List.mem_append_right _ (List.mem_singleton.2 h.1)) hvl
      · exact List.mem_append_left _ h
    | none => exact List.mem_append_right _ (hnew_all v d hdv hd)
  · -- every arrow out of a vertex left leads to a vertex found
    rw [hL] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨d, hd⟩ := hmarked x hx
      rw [(keep x d hd).1, Option.mem_def, Option.some.injEq] at hdx
      subst hdx
      obtain ⟨dw, hdw, hle⟩ := hR x hx e he d hd
      exact ⟨dw, (keep _ _ hdw).1, hle⟩
    · rw [List.mem_singleton.1 hx] at he
      rw [List.mem_singleton.1 hx, (keep u du hdu).1, Option.mem_def, Option.some.injEq] at hdx
      subst hdx
      exact row_u e he

/-! ## The whole search -/

theorem left_step {st : State} {u du : ℕ} {q : List (ℕ × ℕ)} (hq : st.queue = (u, du) :: q) :
    (step g st).left = st.left ++ [u] := by
  have : step g st = (g.out u).foldl (tryArrow u du)
      { st with left := st.left ++ [u], queue := q } := by
    unfold step; rw [hq]
  rw [this]
  exact (looks_foldl g u du (g.out u) _ fun e he => (mem_out.1 he).1).left

theorem runSteps_induct (P : State → Prop) (hstep : ∀ st, P st → st.queue ≠ [] → P (step g st)) :
    ∀ f st, P st → P (runSteps g f st)
  | 0, _, h => h
  | f + 1, st, h => by
    unfold runSteps
    split_ifs with hq
    · exact h
    · exact runSteps_induct P hstep f _ (hstep st h hq)

/-- Every vertex left is a vertex of the graph. -/
theorem lt_of_mem_left (hN : g.WellFormed) (hs : s < g.n) {st : State} (h : Valid g s st)
    {x : ℕ} (hx : x ∈ st.left) : x < g.n := by
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 (h.1.2 x hx).1
  obtain ⟨p, hp, -⟩ := (h.1.2 x hx).2.2 d hd
  exact hp.lt (N := unit g) ⟨hN, by simp [unit]⟩ hs

/-- **The search ends with the queue empty**: each step leaves one more vertex, and no vertex is
left twice. -/
theorem queue_runSteps (hN : g.WellFormed) (hs : s < g.n) :
    ∀ f st, Valid g s st → g.n ≤ st.left.length + f → (runSteps g f st).queue = []
  | 0, st, h, hf => by
    unfold runSteps
    by_contra hne
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨h1, h2, -⟩ := h.2.2.2.1.2.1 e he
    have := (List.nodup_cons.2 ⟨h2, h.1.1⟩).length_le_of_subset (l₂ := List.range g.n)
      fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_range.2 h1
        · exact List.mem_range.2 (lt_of_mem_left hN hs h hx)
    simp only [List.length_cons, List.length_range] at this
    omega
  | f + 1, st, h, hf => by
    unfold runSteps
    split_ifs with hq
    · exact hq
    · obtain ⟨⟨u, du⟩, q, hq'⟩ := List.exists_cons_of_ne_nil hq
      refine queue_runSteps hN hs f _ (valid_step hN hs h hq) ?_
      rw [left_step hq', List.length_append, List.length_singleton]
      omega

/-- The state the search ends in. -/
abbrev final (g : Digraph) (s : ℕ) : State := runSteps g g.n (start s)

theorem final_valid (hN : g.WellFormed) (hs : s < g.n) : Valid g s (final g s) :=
  runSteps_induct _ (fun _ h hq => valid_step hN hs h hq) _ _ (valid_start hs)

theorem final_queue (hN : g.WellFormed) (hs : s < g.n) : (final g s).queue = [] :=
  queue_runSteps hN hs _ _ (valid_start hs) (by simp)

/-! ## What the search promises -/

/-- **On a legal state with an empty queue, every vertex that can be reached has been left.** -/
theorem mem_left_of_reaches (hN : g.WellFormed) (hs : s < g.n) {st : State} (h : Valid g s st)
    (hq : st.queue = []) {v : ℕ} (hv : g.Reaches s v) : v ∈ st.left := by
  obtain ⟨hA, hB, -, hF, hR, -⟩ := h
  induction hv with
  | refl =>
    by_contra hsl
    obtain ⟨d, hd, -⟩ := (hB s hs hsl).1 [] (isPath_nil s) (through_nil _ _)
    have := hF.2.2 s hs hsl d hd
    rw [hq] at this
    exact absurd this List.not_mem_nil
  | @tail b c _ hbc ih =>
    by_contra hcl
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hbc
    have hc : c < g.n := (hN _ hbc).2
    obtain ⟨dx, hdx⟩ := Option.ne_none_iff_exists'.1 (hA.2 b ih).1
    obtain ⟨d, hd, -⟩ := hR b ih (c, i) (mem_out.2 ⟨hc, hi⟩) dx hdx
    have := hF.2.2 c hc hcl d hd
    rw [hq] at this
    exact absurd this List.not_mem_nil

/-- **Every vertex that can be reached gets the fewest arrows of any path to it.** -/
theorem bfs_reached (hN : g.WellFormed) (hs : s < g.n) {v : ℕ} (hv : g.Reaches s v) :
    ∃ d, (bfs g s).dist v = some d ∧ Fewest g s v (some d) := by
  have h := final_valid hN hs
  obtain ⟨hne, hc⟩ := h.1.2 v (mem_left_of_reaches hN hs h (final_queue hN hs) hv)
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hne
  exact ⟨d, hd, hd ▸ hc⟩

/-- **Following each previous vertex back to the start gives a path with exactly the distance's
number of arrows.** -/
theorem bfs_previous (hN : g.WellFormed) (hs : s < g.n) {v : ℕ} (hv : v < g.n) :
    ∀ d ∈ (bfs g s).dist v, ∃ p, (unit g).IsPath s p v ∧ p.length = d ∧
      LeadsBack (bfs g s).prev s ((unit g).visits s p) := by
  intro d hd
  obtain ⟨p, hp, hc, -, hl⟩ := (final_valid hN hs).2.2.2.2.2.1.2 v hv d hd
  exact ⟨p, hp, hc, hl⟩

/-- **A vertex that cannot be reached is reported as unreachable.** -/
theorem bfs_unreached (hN : g.WellFormed) (hs : s < g.n) {v : ℕ} (hv : v < g.n)
    (hr : ¬ g.Reaches s v) : (bfs g s).dist v = none := by
  by_contra hk
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hk
  obtain ⟨p, hp, -⟩ := bfs_previous hN hs hv d hd
  exact hr (reaches_of_ends hp.1)

end AlgoDesign.Paths.Bfs
