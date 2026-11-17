/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Loop

/-!
# Max flow: the search the path rules share

Sources: the Flow chapter, "Max flow"; Edmonds and Karp, "Theoretical improvements in algorithmic
efficiency for network flow problems" (1972), for the first-in-first-out search; Ahuja, Magnanti
and Orlin, *Network Flows* (1993), §7.3, for the residual network of paired arrows.

Each vertex lists its residual arrows in **adjacency order** (`Network.residualOut`): for each arrow
id in increasing order, `along i` if arrow `i` leaves the vertex, then `back i` if it enters it.
The search (`search`) labels vertices first in, first out from the source, over residual arrows
with room of at least a threshold, in adjacency order; the first vertex to label a vertex wins, and
the search stops as soon as the sink is labeled. Each labeled vertex keeps its level (the number
of arrows from the source) and the arrow that labeled it. The path back from the sink
(`pathBack`) follows those arrows.
-/

@[expose] public section

namespace AlgoDesign.Flows

namespace Network

/-- **The residual arrows leaving `v`**, in adjacency order: for each arrow id in increasing order,
`along i` if arrow `i` leaves `v`, then `back i` if it enters `v`. -/
def residualOut (N : Network) (v : ℕ) : List ResidualArrow :=
  N.ids.flatMap fun i =>
    (if N.tail i = v then [ResidualArrow.along i] else []) ++
      (if N.head i = v then [ResidualArrow.back i] else [])

end Network

/-- **A search's labels**: the vertices waiting their turn, first in first out, and each labeled
vertex's level and the arrow that labeled it. -/
structure Labels where
  /-- The labeled vertices whose arrows are not yet tried, in the order they were labeled. -/
  queue : List ℕ
  /-- The level of a labeled vertex: the number of arrows from the source. -/
  level : ℕ → Option ℕ
  /-- The residual arrow that labeled a vertex; none for the source. -/
  via : ℕ → Option ResidualArrow

/-- The labels before the search: the source alone, at level 0. -/
def Labels.start (N : Network) : Labels :=
  ⟨[N.source], Function.update (fun _ => none) N.source (some 0), fun _ => none⟩

/-- **Try one residual arrow** out of a vertex at level `lu`: unless the sink is already labeled,
an arrow with room of at least `Δ`, and some room, to a vertex not yet labeled labels it one level
deeper and queues it. -/
def labelOne (N : Network) (f : Flow) (Δ lu : ℕ) (L : Labels) (a : ResidualArrow) : Labels :=
  if (L.level N.sink).isSome then L
  else if 0 < a.residualCapacity N f ∧ Δ ≤ a.residualCapacity N f ∧ L.level (a.head N) = none then
    { queue := L.queue ++ [a.head N]
      level := Function.update L.level (a.head N) (some (lu + 1))
      via := Function.update L.via (a.head N) (some a) }
  else L

/-- At most `k` turns of the search: take the first queued vertex and try its residual arrows in
adjacency order; stop when the sink is labeled or nothing is queued. -/
def searchTurns (N : Network) (f : Flow) (Δ : ℕ) : ℕ → Labels → Labels
  | 0, L => L
  | k + 1, L =>
    if (L.level N.sink).isSome then L
    else
      match L.queue with
      | [] => L
      | u :: q =>
        searchTurns N f Δ k
          ((N.residualOut u).foldl (labelOne N f Δ ((L.level u).getD 0)) { L with queue := q })

/-- **The search** from the source over residual arrows with room of at least `Δ`, and some room:
one turn per vertex, which is enough for `n` vertices. -/
def search (N : Network) (f : Flow) (Δ : ℕ) : Labels :=
  searchTurns N f Δ N.g.n (Labels.start N)

/-- The path back from `v` to the source along the labeling arrows, put in front of `acc`, in at
most `k` steps; none if a vertex on the way has no labeling arrow. -/
def pathBack (N : Network) (via : ℕ → Option ResidualArrow) :
    ℕ → ℕ → List ResidualArrow → Option (List ResidualArrow)
  | 0, v, acc => if v = N.source then some acc else none
  | k + 1, v, acc =>
    if v = N.source then some acc
    else
      match via v with
      | none => none
      | some a => pathBack N via k (a.tail N) (a :: acc)

/-- **The bottleneck** of a path: the least room of its arrows under the flow `f`. -/
def bottleneck (N : Network) (f : Flow) (p : List ResidualArrow) : ℕ :=
  ((p.map (·.residualCapacity N f)).min?).getD 0

/-- The path, with its bottleneck as the amount. -/
def byBottleneck (N : Network) (f : Flow) (p : List ResidualArrow) : Augmentation :=
  ⟨p, bottleneck N f p⟩

/-- **The path the search finds** with threshold `Δ`: if it labels the sink, the path back from
the sink along the labeling arrows. -/
def shortestPath (N : Network) (f : Flow) (Δ : ℕ) : Option (List ResidualArrow) :=
  let L := search N f Δ
  if (L.level N.sink).isSome then pathBack N L.via N.g.n N.sink [] else none

/-! ## The residual arrows at a vertex -/

theorem mem_residualOut {N : Network} {v : ℕ} {a : ResidualArrow} :
    a ∈ N.residualOut v ↔ a.id < N.g.arrows.length ∧ a.tail N = v := by
  cases a <;> simp [Network.residualOut, Network.ids, ResidualArrow.id, ResidualArrow.tail]

/-! ## Paths that climb the levels -/

/-- **A path that climbs the levels**: from the source to `v`, the `k`-th vertex it visits on
level `k`, every arrow of it passing `ok`. -/
def Climbs (N : Network) (level : ℕ → Option ℕ) (ok : ResidualArrow → Prop)
    (p : List ResidualArrow) (v : ℕ) : Prop :=
  ends N N.source p = some v ∧
    (visits N N.source p).map level = (List.range (p.length + 1)).map some ∧ ∀ a ∈ p, ok a

theorem Climbs.nodup {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {p : List ResidualArrow} {v : ℕ} (h : Climbs N level ok p v) :
    (visits N N.source p).Nodup := by
  have : ((visits N N.source p).map level).Nodup := by
    rw [h.2.1]
    exact (List.nodup_range).map fun _ _ => Option.some.inj
  exact this.of_map level

theorem Climbs.isAugmentingPath {N : Network} {level : ℕ → Option ℕ} {f : Flow}
    {ok : ResidualArrow → Prop} {p : List ResidualArrow} (h : Climbs N level ok p N.sink)
    (hok : ∀ a, ok a → 0 < a.residualCapacity N f) : IsAugmentingPath N f p :=
  ⟨h.1, h.nodup, fun a ha => hok a (h.2.2 a ha)⟩

theorem ends_append (N : Network) :
    ∀ (p q : List ResidualArrow) (u : ℕ), ends N u (p ++ q) = (ends N u p).bind (ends N · q)
  | [], _, _ => rfl
  | a :: p, q, u => by
    simp only [List.cons_append, ends]
    split_ifs
    · exact ends_append N p q _
    · rfl

theorem ends_snoc {N : Network} {p : List ResidualArrow} {a : ResidualArrow} {u w : ℕ}
    (h : ends N u (p ++ [a]) = some w) : ∃ t, ends N u p = some t ∧
      a.id < N.g.arrows.length ∧ a.tail N = t ∧ a.head N = w := by
  rw [ends_append] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [ends] at h
  split_ifs at h with ha
  simp only [Option.some.injEq] at h
  exact ⟨t, ht, ha.1, ha.2, h⟩

/-- The two residual arrows of one arrow of the network share their ends, turned around. -/
theorem ResidualArrow.ends_of_id_eq (N : Network) {a c : ResidualArrow} (h : c.id = a.id) :
    c.head N = a.head N ∨ c.tail N = a.head N := by
  cases a <;> cases c <;> simp_all [ResidualArrow.id, ResidualArrow.head, ResidualArrow.tail]

/-- **Steps one level up**: its tail is labeled, and its head one level deeper. -/
def LevelUp (N : Network) (level : ℕ → Option ℕ) (a : ResidualArrow) : Prop :=
  ∃ l, level (a.tail N) = some l ∧ level (a.head N) = some (l + 1)

theorem LevelUp.not_of_id_eq {N : Network} {level : ℕ → Option ℕ} {a c : ResidualArrow}
    (ha : LevelUp N level a) (hc : LevelUp N level c) (h : c.id = a.id) (hne : c ≠ a) : False := by
  obtain ⟨l, hl, hl'⟩ := ha
  obtain ⟨k, hk, hk'⟩ := hc
  cases a <;> cases c <;>
    simp_all [ResidualArrow.id, ResidualArrow.head, ResidualArrow.tail] <;> omega

/-! ## What the search's labels mean -/

/-- **Fits the threshold `Δ`**: some room, and at least `Δ`. -/
def Fits (N : Network) (f : Flow) (Δ : ℕ) (a : ResidualArrow) : Prop :=
  0 < a.residualCapacity N f ∧ Δ ≤ a.residualCapacity N f

/-- **The labels are sound**: the source is on level 0, every queued vertex is labeled, and every
other labeled vertex was labeled by an arrow of the network that fits the threshold, from a
vertex one level up. -/
def Labels.Sound (N : Network) (f : Flow) (Δ : ℕ) (L : Labels) : Prop :=
  L.level N.source = some 0 ∧ (∀ u ∈ L.queue, (L.level u).isSome) ∧
    ∀ v l, L.level v = some l → v ≠ N.source → ∃ a l', L.via v = some a ∧ a.head N = v ∧
      a.id < N.g.arrows.length ∧ Fits N f Δ a ∧ l = l' + 1 ∧ L.level (a.tail N) = some l'

theorem Labels.sound_start (N : Network) (f : Flow) (Δ : ℕ) : (Labels.start N).Sound N f Δ := by
  refine ⟨by simp [Labels.start], by simp [Labels.start], fun v l hv hs => ?_⟩
  simp [Labels.start, Function.update_of_ne hs] at hv

theorem Labels.Sound.of_labelOne {N : Network} {f : Flow} {Δ lu u : ℕ} {L : Labels}
    (hL : L.Sound N f Δ) (hu : L.level u = some lu) {a : ResidualArrow}
    (ha : a ∈ N.residualOut u) : (labelOne N f Δ lu L a).Sound N f Δ := by
  obtain ⟨hid, htail⟩ := mem_residualOut.1 ha
  unfold labelOne
  split_ifs with h1 h2
  · exact hL
  · obtain ⟨hr0, hrΔ, hw⟩ := h2
    have hsw : N.source ≠ a.head N := fun e => by simp [← e, hL.1] at hw
    have huw : u ≠ a.head N := fun e => by simp [← e, hu] at hw
    refine ⟨by simp [Function.update_of_ne hsw, hL.1], fun x hx => ?_, fun v l hv hs => ?_⟩
    · by_cases hxw : x = a.head N
      · simp [hxw]
      · simp only [List.mem_append, List.mem_singleton, hxw, or_false] at hx
        simpa [Function.update_of_ne hxw] using hL.2.1 x hx
    · by_cases hvw : v = a.head N
      · subst hvw
        simp only [Function.update_self, Option.some.injEq] at hv
        refine ⟨a, lu, by simp, rfl, hid, ⟨hr0, hrΔ⟩, hv.symm, ?_⟩
        simp [htail, Function.update_of_ne huw, hu]
      · simp only [Function.update_of_ne hvw] at hv ⊢
        obtain ⟨b, l', hb, hbh, hbid, hbf, hl, hbt⟩ := hL.2.2 v l hv hs
        have htw : b.tail N ≠ a.head N := fun e => by simp [e, hw] at hbt
        exact ⟨b, l', hb, hbh, hbid, hbf, hl, by simp [Function.update_of_ne htw, hbt]⟩
  · exact hL

/-- A property kept by every step of a left fold over a list holds after the fold. -/
theorem foldl_keeps {α β : Type*} (P : β → Prop) (g : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ x ∈ l, ∀ b, P b → P (g b x)) → P (l.foldl g b)
  | [], _, hb, _ => hb
  | x :: l, b, hb, hg =>
    foldl_keeps P g l (g b x) (hg x (by simp) b hb) fun y hy => hg y (by simp [hy])

/-- A label, once given, stays. -/
theorem labelOne_level {N : Network} {f : Flow} {Δ lu : ℕ} {L : Labels} {a : ResidualArrow}
    {v l : ℕ} (hv : L.level v = some l) : (labelOne N f Δ lu L a).level v = some l := by
  unfold labelOne
  split_ifs with h1 h2
  · exact hv
  · have hvw : v ≠ a.head N := fun e => by simp [e ▸ hv] at h2
    simp [Function.update_of_ne hvw, hv]
  · exact hv

theorem foldl_labelOne_level {N : Network} {f : Flow} {Δ lu : ℕ} (as : List ResidualArrow)
    {L : Labels} {v l : ℕ} (hv : L.level v = some l) :
    (as.foldl (labelOne N f Δ lu) L).level v = some l :=
  foldl_keeps (fun L' : Labels => L'.level v = some l) _ as L hv fun _ _ _ h => labelOne_level h

theorem Labels.Sound.of_searchTurns {N : Network} {f : Flow} {Δ : ℕ} :
    ∀ (k : ℕ) (L : Labels), L.Sound N f Δ → (searchTurns N f Δ k L).Sound N f Δ
  | 0, _, hL => hL
  | k + 1, L, hL => by
    unfold searchTurns
    split_ifs
    · exact hL
    · split
      · exact hL
      · rename_i u q hq
        obtain ⟨lu, hu⟩ := Option.isSome_iff_exists.1 (hL.2.1 u (by simp [hq]))
        rw [hu, Option.getD_some]
        refine Labels.Sound.of_searchTurns k _ (foldl_keeps
          (fun L' : Labels => L'.Sound N f Δ ∧ L'.level u = some lu) _ _ _ ?_
          fun a ha L' hL' => ⟨hL'.1.of_labelOne hL'.2 ha, labelOne_level hL'.2⟩).1
        exact ⟨⟨hL.1, fun x hx => hL.2.1 x (by simp [hq, hx]), hL.2.2⟩, hu⟩

theorem Labels.sound_search (N : Network) (f : Flow) (Δ : ℕ) : (search N f Δ).Sound N f Δ :=
  Labels.Sound.of_searchTurns _ _ (Labels.sound_start N f Δ)

/-! ## The path back -/

theorem Labels.Sound.pathBack {N : Network} {f : Flow} {Δ : ℕ} {L : Labels}
    (hL : L.Sound N f Δ) : ∀ (l v k : ℕ) (acc : List ResidualArrow), L.level v = some l →
      l ≤ k → ∃ p, pathBack N L.via k v acc = some (p ++ acc) ∧
        Climbs N L.level (Fits N f Δ) p v ∧ p.length = l
  | 0, v, k, acc, hv, _ => by
    have hvs : v = N.source := by
      by_contra hs
      obtain ⟨_, _, _, _, _, _, h, _⟩ := hL.2.2 v 0 hv hs
      omega
    subst hvs
    refine ⟨[], by cases k <;> simp [AlgoDesign.Flows.pathBack], ⟨by simp [ends], ?_, by simp⟩,
      rfl⟩
    simp [visits, hL.1]
  | l + 1, v, k, acc, hv, hk => by
    have hs : v ≠ N.source := fun e => by simp [e, hL.1] at hv
    obtain ⟨a, l', hva, hh, hid, hfit, hl, ht⟩ := hL.2.2 v (l + 1) hv hs
    rw [show l' = l by omega] at ht
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨p, hp, hc, hlen⟩ := hL.pathBack l (a.tail N) k (a :: acc) ht (by omega)
    refine ⟨p ++ [a], ?_, ⟨?_, ?_, ?_⟩, by simp [hlen]⟩
    · simp [AlgoDesign.Flows.pathBack, hs, hva, hp]
    · rw [ends_append_one N a p _ _ hc.1 hid rfl, hh]
    · rw [visits_append_one, List.map_append, hc.2.1, List.length_append, List.length_singleton,
        List.map_singleton, hh, hv, hlen]
      simp [List.range_succ]
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hc.2.2 x hx
      · rw [List.mem_singleton.1 hx]; exact hfit

theorem ends_visits_lt {N : Network} (h : N.WellFormed) :
    ∀ (p : List ResidualArrow) (u v : ℕ), u < N.g.n → ends N u p = some v →
      ∀ w ∈ visits N u p, w < N.g.n
  | [], u, v, hu, _, w, hw => by simp [visits] at hw; omega
  | a :: p, u, v, hu, he, w, hw => by
    simp only [ends] at he
    split_ifs at he with ha
    have hah : a.head N < N.g.n := by
      cases a with
      | along i => exact (N.endpoints_lt h ha.1).2
      | back i => exact (N.endpoints_lt h ha.1).1
    simp only [visits, List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | rfl | hw
    · exact hu
    · exact hah
    · exact ends_visits_lt h p _ v hah he w (by simp [visits, hw])

/-- A path that climbs the levels has fewer arrows than the network has vertices. -/
theorem Climbs.length_lt {N : Network} (h : N.WellFormed) {level : ℕ → Option ℕ}
    {ok : ResidualArrow → Prop} {p : List ResidualArrow} {v : ℕ} (hc : Climbs N level ok p v) :
    p.length < N.g.n := by
  have hsub : visits N N.source p ⊆ List.range N.g.n := fun w hw =>
    List.mem_range.2 (ends_visits_lt h p _ v h.2.2.1 hc.1 w hw)
  have := (List.subperm_of_subset hc.nodup hsub).length_le
  simp [visits] at this
  omega

/-- **The path the search finds climbs its levels**, and every arrow of it fits the threshold. -/
theorem shortestPath_climbs {N : Network} (h : N.WellFormed) {f : Flow} {Δ : ℕ}
    {p : List ResidualArrow} (hp : shortestPath N f Δ = some p) :
    Climbs N (search N f Δ).level (Fits N f Δ) p N.sink := by
  have hL := Labels.sound_search N f Δ
  simp only [shortestPath] at hp
  split_ifs at hp with hs
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨p₀, -, hc₀, hlen₀⟩ := hL.pathBack l N.sink l [] hl le_rfl
  have hln : l ≤ N.g.n := by have := hc₀.length_lt h; omega
  obtain ⟨p₁, hp₁, hc₁, -⟩ := hL.pathBack l N.sink N.g.n [] hl hln
  rw [hp₁, List.append_nil, Option.some.injEq] at hp
  exact hp ▸ hc₁

/-- The search that labels the sink finds a path. -/
theorem shortestPath_isSome {N : Network} (h : N.WellFormed) {f : Flow} {Δ : ℕ}
    (hs : ((search N f Δ).level N.sink).isSome) : (shortestPath N f Δ).isSome := by
  have hL := Labels.sound_search N f Δ
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨p₀, -, hc₀, hlen₀⟩ := hL.pathBack l N.sink l [] hl le_rfl
  have hln : l ≤ N.g.n := by have := hc₀.length_lt h; omega
  obtain ⟨p₁, hp₁, -, -⟩ := hL.pathBack l N.sink N.g.n [] hl hln
  simp [shortestPath, hs, hp₁]

/-! ## The search misses the sink only when no path is left -/

/-- **Closed, except at `ex`**: every labeled vertex that is not queued, and not excepted, has
labeled the head of every residual arrow out of it that fits the threshold. -/
def Labels.ClosedBut (N : Network) (f : Flow) (Δ : ℕ) (ex : ℕ → Prop) (L : Labels) : Prop :=
  ∀ x, (L.level x).isSome → x ∉ L.queue → ¬ ex x → ∀ a ∈ N.residualOut x, Fits N f Δ a →
    (L.level (a.head N)).isSome

/-- How many vertices of the network are labeled. -/
def Labels.count (N : Network) (L : Labels) : ℕ :=
  (List.range N.g.n).countP fun v => (L.level v).isSome

theorem countP_range_flip {p q : ℕ → Bool} {w : ℕ} (hpq : ∀ v, v ≠ w → q v = p v)
    (hp : p w = false) (hq : q w = true) :
    ∀ n, w < n → (List.range n).countP q = (List.range n).countP p + 1
  | 0, hw => absurd hw (Nat.not_lt_zero w)
  | n + 1, hw => by
    rw [List.range_succ, List.countP_append, List.countP_append]
    by_cases hn : w = n
    · subst hn
      have : (List.range w).countP q = (List.range w).countP p :=
        List.countP_congr fun v hv => by
          rw [hpq v (Nat.ne_of_lt (List.mem_range.1 hv))]
      simp [this, hp, hq]
    · rw [countP_range_flip hpq hp hq n (by omega)]
      rw [List.countP_singleton, List.countP_singleton, hpq n (Ne.symm hn)]
      omega

theorem isSome_labelOne {N : Network} {f : Flow} {Δ lu : ℕ} {L : Labels} {a : ResidualArrow}
    {v : ℕ} (hv : (L.level v).isSome) : ((labelOne N f Δ lu L a).level v).isSome := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hv
  simp [labelOne_level (a := a) (lu := lu) (Δ := Δ) (f := f) hl]

theorem isSome_foldl_labelOne {N : Network} {f : Flow} {Δ lu : ℕ} (as : List ResidualArrow)
    {L : Labels} {v : ℕ} (hv : (L.level v).isSome) :
    ((as.foldl (labelOne N f Δ lu) L).level v).isSome :=
  foldl_keeps (fun L' : Labels => (L'.level v).isSome) _ as L hv fun _ _ _ h => isSome_labelOne h

/-- One arrow tried: it either changed nothing, or labeled its head, unlabeled before, and
queued it. -/
theorem labelOne_cases (N : Network) (f : Flow) (Δ lu : ℕ) (L : Labels) (a : ResidualArrow) :
    labelOne N f Δ lu L a = L ∨ (L.level (a.head N) = none ∧
      labelOne N f Δ lu L a = ⟨L.queue ++ [a.head N],
        Function.update L.level (a.head N) (some (lu + 1)),
        Function.update L.via (a.head N) (some a)⟩) := by
  unfold labelOne
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr ⟨h2.2.2, rfl⟩
  · exact Or.inl rfl

theorem labelOne_covers {N : Network} {f : Flow} {Δ lu : ℕ} {L : Labels} {a : ResidualArrow}
    (ha : Fits N f Δ a) : ((labelOne N f Δ lu L a).level N.sink).isSome ∨
      ((labelOne N f Δ lu L a).level (a.head N)).isSome := by
  unfold labelOne
  split_ifs with h1 h2
  · exact Or.inl h1
  · exact Or.inr (by simp)
  · refine Or.inr ?_
    have : L.level (a.head N) ≠ none := fun e => h2 ⟨ha.1, ha.2, e⟩
    exact Option.isSome_iff_ne_none.2 this

theorem foldl_labelOne_covers {N : Network} {f : Flow} {Δ lu : ℕ} :
    ∀ (as : List ResidualArrow) (L : Labels), ∀ a ∈ as, Fits N f Δ a →
      ((as.foldl (labelOne N f Δ lu) L).level N.sink).isSome ∨
        ((as.foldl (labelOne N f Δ lu) L).level (a.head N)).isSome
  | [], _, _, ha, _ => absurd ha List.not_mem_nil
  | b :: as, L, a, ha, hf => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · rcases labelOne_covers (lu := lu) (L := L) hf with h | h
      · exact Or.inl (isSome_foldl_labelOne as h)
      · exact Or.inr (isSome_foldl_labelOne as h)
    · exact foldl_labelOne_covers as _ a ha hf

theorem labelOne_queue_nodup {N : Network} {f : Flow} {Δ lu : ℕ} {L : Labels}
    {a : ResidualArrow} (hn : L.queue.Nodup) (hq : ∀ x ∈ L.queue, (L.level x).isSome) :
    (labelOne N f Δ lu L a).queue.Nodup := by
  rcases labelOne_cases N f Δ lu L a with h | ⟨hw, h⟩
  · rw [h]; exact hn
  · rw [h]
    refine List.nodup_append.2 ⟨hn, List.nodup_singleton _, fun x hx y hy => ?_⟩
    rintro rfl
    simp only [List.mem_singleton] at hy
    have := hq x hx
    simp [hy, hw] at this

theorem labelOne_closedBut {N : Network} {f : Flow} {Δ lu : ℕ} {ex : ℕ → Prop} {L : Labels}
    {a : ResidualArrow} (hc : L.ClosedBut N f Δ ex) :
    (labelOne N f Δ lu L a).ClosedBut N f Δ ex := by
  rcases labelOne_cases N f Δ lu L a with h | ⟨hw, h⟩
  · rw [h]; exact hc
  · intro x hx hxq hex b hb hfb
    have hxw : x ≠ a.head N := fun e => hxq (by rw [h]; simp [e])
    have hx' : (L.level x).isSome := by
      rw [h] at hx; dsimp only at hx; rwa [Function.update_of_ne hxw] at hx
    have hxq' : x ∉ L.queue := fun e => hxq (by rw [h]; simp [e])
    exact isSome_labelOne (hc x hx' hxq' hex b hb hfb)

theorem labelOne_count {N : Network} (h : N.WellFormed) {f : Flow} {Δ lu u : ℕ} {L : Labels}
    {a : ResidualArrow} (ha : a ∈ N.residualOut u) :
    (labelOne N f Δ lu L a).queue.length + L.count N ≤
      L.queue.length + (labelOne N f Δ lu L a).count N := by
  rcases labelOne_cases N f Δ lu L a with he | ⟨hw, he⟩
  · rw [he]
  · have hid := (mem_residualOut.1 ha).1
    have hlt : a.head N < N.g.n := by
      cases a with
      | along i => exact (N.endpoints_lt h hid).2
      | back i => exact (N.endpoints_lt h hid).1
    have hc := countP_range_flip (p := fun v => (L.level v).isSome)
      (q := fun v => (Function.update L.level (a.head N) (some (lu + 1)) v).isSome) (w := a.head N)
      (fun v hv => by simp [Function.update_of_ne hv]) (by simp [hw]) (by simp) _ hlt
    rw [he]
    simp only [Labels.count, List.length_append, List.length_singleton] at hc ⊢
    omega

theorem Labels.count_le (N : Network) (L : Labels) : L.count N ≤ N.g.n := by
  simpa [Labels.count] using List.countP_le_length (l := List.range N.g.n)
    (p := fun v => (L.level v).isSome)

theorem searchTurns_of_sink {N : Network} {f : Flow} {Δ : ℕ} {L : Labels}
    (hs : (L.level N.sink).isSome) : ∀ k, searchTurns N f Δ k L = L
  | 0 => rfl
  | _ + 1 => by simp [searchTurns, hs]

theorem searchTurns_done {N : Network} (h : N.WellFormed) {f : Flow} {Δ : ℕ} :
    ∀ (k : ℕ) (L : Labels), L.Sound N f Δ → L.queue.Nodup → L.ClosedBut N f Δ (fun _ => False) →
      N.g.n + L.queue.length ≤ k + L.count N →
      ((searchTurns N f Δ k L).level N.sink).isSome ∨
        ((searchTurns N f Δ k L).queue = [] ∧
          (searchTurns N f Δ k L).ClosedBut N f Δ (fun _ => False))
  | 0, L, _, _, hc, hk => by
    have := L.count_le N
    simp only [searchTurns]
    exact Or.inr ⟨List.eq_nil_of_length_eq_zero (by omega), hc⟩
  | k + 1, L, hL, hn, hc, hk => by
    by_cases hs : (L.level N.sink).isSome
    · rw [searchTurns_of_sink hs]; exact Or.inl hs
    match hq : L.queue with
    | [] => simp only [searchTurns, hs, hq]; exact Or.inr ⟨by simp [hq], hc⟩
    | u :: q =>
      obtain ⟨lu, hu⟩ := Option.isSome_iff_exists.1 (hL.2.1 u (by simp [hq]))
      have hstep : searchTurns N f Δ (k + 1) L = searchTurns N f Δ k
          ((N.residualOut u).foldl (labelOne N f Δ lu) { L with queue := q }) := by
        simp [searchTurns, hs, hq, hu]
      rw [hstep]
      set L₁ : Labels := { L with queue := q }
      set R := (N.residualOut u).foldl (labelOne N f Δ lu) L₁
      have hn' : q.Nodup := (hq ▸ hn).of_cons
      have hu' : u ∉ q := (List.nodup_cons.1 (hq ▸ hn)).1
      -- the invariants carried through the fold
      have hR : (R.Sound N f Δ ∧ R.level u = some lu) ∧ R.queue.Nodup ∧
          R.ClosedBut N f Δ (· = u) ∧ R.queue.length + L₁.count N ≤ q.length + R.count N := by
        refine foldl_keeps (fun L' : Labels => (L'.Sound N f Δ ∧ L'.level u = some lu) ∧
            L'.queue.Nodup ∧ L'.ClosedBut N f Δ (· = u) ∧
            L'.queue.length + L₁.count N ≤ q.length + L'.count N) _ _ _ ?_ ?_
        · refine ⟨⟨⟨hL.1, fun x hx => hL.2.1 x (by rw [hq]; exact List.mem_cons_of_mem _ hx),
            hL.2.2⟩, hu⟩, hn', ?_, le_rfl⟩
          intro x hx hxq hex b hb hfb
          exact hc x hx (by rw [hq]; exact fun hm => (List.mem_cons.1 hm).elim hex hxq) id b hb
            hfb
        · intro a ha L' ⟨⟨hs', hl'⟩, hn'', hc', hk'⟩
          refine ⟨⟨hs'.of_labelOne hl' ha, labelOne_level hl'⟩, labelOne_queue_nodup hn'' hs'.2.1,
            labelOne_closedBut hc', ?_⟩
          have := labelOne_count h (f := f) (Δ := Δ) (lu := lu) (L := L') ha
          omega
      obtain ⟨⟨hRs, hRu⟩, hRn, hRc, hRk⟩ := hR
      by_cases hsR : (R.level N.sink).isSome
      · rw [searchTurns_of_sink hsR]; exact Or.inl hsR
      refine searchTurns_done h k R hRs hRn ?_ ?_
      · intro x hx hxq _ b hb hfb
        by_cases hxu : x = u
        · subst hxu
          exact (foldl_labelOne_covers _ L₁ b hb hfb).resolve_left hsR
        · exact hRc x hx hxq hxu b hb hfb
      · have : L₁.count N = L.count N := rfl
        simp only [hq, List.length_cons] at hk
        omega

/-- **The search misses the sink only when no path is left**: if it ends without labeling the
sink, no path from the source to the sink has every arrow fitting the threshold. -/
theorem search_complete {N : Network} (h : N.WellFormed) {f : Flow} {Δ : ℕ}
    (hs : (search N f Δ).level N.sink = none) (p : List ResidualArrow)
    (hp : ends N N.source p = some N.sink) : ¬ ∀ a ∈ p, Fits N f Δ a := by
  intro hfit
  have hst : (Labels.start N).ClosedBut N f Δ (fun _ => False) := by
    intro x hx hxq
    by_cases e : x = N.source
    · exact absurd (by simp [Labels.start, e]) hxq
    · simp [Labels.start, Function.update_of_ne e] at hx
  have hcount : (Labels.start N).count N = 1 := by
    have := countP_range_flip (p := fun _ => false)
      (q := fun v => ((Labels.start N).level v).isSome) (w := N.source)
      (fun v hv => by simp [Labels.start, Function.update_of_ne hv]) rfl (by simp [Labels.start])
      N.g.n h.2.2.1
    simpa [Labels.count] using this
  rcases searchTurns_done h N.g.n (Labels.start N) (Labels.sound_start N f Δ)
    (by simp [Labels.start]) hst (by rw [hcount]; simp [Labels.start]) with hR | ⟨hq, hc⟩
  · simp [search] at hs; simp [hs] at hR
  · have hsrc := (Labels.sound_search N f Δ).1
    have walk : ∀ (p : List ResidualArrow) (u : ℕ), ((search N f Δ).level u).isSome →
        ends N u p = some N.sink → (∀ a ∈ p, Fits N f Δ a) →
        ((search N f Δ).level N.sink).isSome := by
      intro p
      induction p with
      | nil => intro u hu he _; simp only [ends, Option.some.injEq] at he; exact he ▸ hu
      | cons a p ih =>
        intro u hu he hf
        simp only [ends] at he
        split_ifs at he with ha
        refine ih _ ?_ he fun b hb => hf b (by simp [hb])
        exact hc u hu (by simp [hq]) id a (mem_residualOut.2 ha)
          (hf a (by simp))
    have := walk p N.source (by simp [hsrc]) hp hfit
    simp [hs] at this

/-! ## Sending along the path found -/

theorem bottleneck_le {N : Network} {f : Flow} {p : List ResidualArrow} {a : ResidualArrow}
    (ha : a ∈ p) : bottleneck N f p ≤ a.residualCapacity N f := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1
    (List.isSome_min?_of_mem (List.mem_map_of_mem (f := (·.residualCapacity N f)) ha))
  rw [bottleneck, hm, Option.getD_some]
  exact (List.min?_eq_some_iff.1 hm).2 _ (List.mem_map_of_mem ha)

theorem one_le_bottleneck {N : Network} {f : Flow} {p : List ResidualArrow} (hp : p ≠ [])
    (hr : ∀ a ∈ p, 0 < a.residualCapacity N f) : 1 ≤ bottleneck N f p := by
  obtain ⟨m, hm⟩ : ∃ m, (p.map (·.residualCapacity N f)).min? = some m :=
    Option.isSome_iff_exists.1 (List.isSome_min?_of_ne_nil (by simpa using hp))
  rw [bottleneck, hm, Option.getD_some]
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.min?_eq_some_iff.1 hm).1
  exact hr a ha

/-- A path from the source to the sink has an arrow. -/
theorem ne_nil_of_ends {N : Network} (h : N.WellFormed) {p : List ResidualArrow}
    (hp : ends N N.source p = some N.sink) : p ≠ [] := by
  rintro rfl
  simp only [ends, Option.some.injEq] at hp
  exact h.2.2.2.2 hp

/-- **Sending a climbing path by its bottleneck** sends along an augmenting path, an amount that
fits every arrow of it, and at least 1. -/
theorem byBottleneck_sends {N : Network} (h : N.WellFormed) {f : Flow} {level : ℕ → Option ℕ}
    {ok : ResidualArrow → Prop} {p : List ResidualArrow} (hc : Climbs N level ok p N.sink)
    (hok : ∀ a, ok a → 0 < a.residualCapacity N f) :
    (IsAugmentingPath N f (byBottleneck N f p).path ∧
      ∀ a ∈ (byBottleneck N f p).path, (byBottleneck N f p).amount ≤ a.residualCapacity N f) ∧
      1 ≤ (byBottleneck N f p).amount :=
  ⟨⟨hc.isAugmentingPath hok, fun _ ha => bottleneck_le ha⟩,
    one_le_bottleneck (ne_nil_of_ends h hc.1) fun a ha => hok a (hc.2.2 a ha)⟩

/-- The path the search finds, sent by its bottleneck. -/
theorem shortestPath_sends {N : Network} (h : N.WellFormed) {f : Flow} {Δ : ℕ}
    {p : List ResidualArrow} (hp : shortestPath N f Δ = some p) :
    (IsAugmentingPath N f (byBottleneck N f p).path ∧
      ∀ a ∈ (byBottleneck N f p).path, (byBottleneck N f p).amount ≤ a.residualCapacity N f) ∧
      1 ≤ (byBottleneck N f p).amount :=
  byBottleneck_sends h (shortestPath_climbs h hp) fun _ ha => ha.1

/-- **No path found, none left**: when the search finds no path, no path from the source to the
sink has every arrow fitting the threshold. -/
theorem shortestPath_none {N : Network} (h : N.WellFormed) {f : Flow} {Δ : ℕ}
    (hp : shortestPath N f Δ = none) (p : List ResidualArrow)
    (he : ends N N.source p = some N.sink) : ¬ ∀ a ∈ p, Fits N f Δ a := by
  refine search_complete h ?_ p he
  by_contra hs
  have := shortestPath_isSome h (Option.isSome_iff_ne_none.2 hs)
  simp [hp] at this

/-- With a threshold of 1 or less, an arrow fits it exactly when it has room. -/
theorem fits_of_le_one {N : Network} {f : Flow} {Δ : ℕ} (hΔ : Δ ≤ 1) {a : ResidualArrow}
    (ha : 0 < a.residualCapacity N f) : Fits N f Δ a :=
  ⟨ha, by omega⟩

/-! ## More on climbing paths -/

theorem Climbs.nil {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    (h : level N.source = some 0) : Climbs N level ok [] N.source :=
  ⟨by simp [ends], by simp [visits, h], by simp⟩

theorem Climbs.snoc {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {p : List ResidualArrow} {w : ℕ} (hc : Climbs N level ok p w) {a : ResidualArrow}
    (hid : a.id < N.g.arrows.length) (ht : a.tail N = w)
    (hl : level (a.head N) = some (p.length + 1)) (hok : ok a) :
    Climbs N level ok (p ++ [a]) (a.head N) := by
  refine ⟨ends_append_one N a p _ _ hc.1 hid ht, ?_, ?_⟩
  · rw [visits_append_one, List.map_append, hc.2.1, List.length_append, List.length_singleton,
      List.map_singleton, hl]
    simp [List.range_succ]
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hc.2.2 x hx
    · rw [List.mem_singleton.1 hx]; exact hok

theorem Climbs.dropLast {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {p : List ResidualArrow} {a : ResidualArrow} {w : ℕ} (hc : Climbs N level ok (p ++ [a]) w) :
    Climbs N level ok p (a.tail N) ∧ a.id < N.g.arrows.length ∧ a.head N = w ∧
      level (a.head N) = some (p.length + 1) ∧ ok a := by
  obtain ⟨t, ht, hid, hat, hah⟩ := ends_snoc hc.1
  have hm := hc.2.1
  rw [visits_append_one, List.map_append, List.length_append, List.length_singleton,
    List.range_succ, List.map_append] at hm
  have hlen : ((visits N N.source p).map level).length =
      ((List.range (p.length + 1)).map some).length := by simp [visits]
  obtain ⟨h1, h2⟩ := List.append_inj hm hlen
  simp only [List.map_singleton, List.cons.injEq, and_true] at h2
  exact ⟨⟨hat ▸ ht, h1, fun x hx => hc.2.2 x (by simp [hx])⟩, hid, hah, h2, hc.2.2 a (by simp)⟩

theorem Climbs.level_end {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {p : List ResidualArrow} {w : ℕ} (hc : Climbs N level ok p w) : level w = some p.length := by
  rcases List.eq_nil_or_concat p with rfl | ⟨q, a, rfl⟩
  · have := hc.1
    simp only [ends, Option.some.injEq] at this
    subst this
    simpa [visits] using hc.2.1
  · rw [List.concat_eq_append] at hc
    obtain ⟨-, -, hh, hl, -⟩ := hc.dropLast
    simpa [hh] using hl

/-- Every vertex a climbing path visits is on a level no deeper than its end. -/
theorem Climbs.level_le {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {p : List ResidualArrow} {w : ℕ} (hc : Climbs N level ok p w) {x : ℕ}
    (hx : x ∈ visits N N.source p) : ∃ j ≤ p.length, level x = some j := by
  have : level x ∈ (List.range (p.length + 1)).map some := hc.2.1 ▸ List.mem_map_of_mem hx
  obtain ⟨j, hj, e⟩ := List.mem_map.1 this
  exact ⟨j, by simp at hj; omega, e.symm⟩

theorem mem_visits_tail {N : Network} :
    ∀ {p : List ResidualArrow} {u v : ℕ}, ends N u p = some v → ∀ a ∈ p,
      a.tail N ∈ visits N u p
  | [], _, _, _, a, ha => absurd ha List.not_mem_nil
  | b :: p, u, v, he, a, ha => by
    simp only [ends] at he
    split_ifs at he with hb
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [visits, hb.2]
    · have := mem_visits_tail he a ha
      simp only [visits, List.map_cons, List.mem_cons] at this ⊢
      tauto

/-- Every arrow of a climbing path steps one level up. -/
theorem Climbs.levelUp {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop} :
    ∀ {p : List ResidualArrow} {w : ℕ}, Climbs N level ok p w → ∀ a ∈ p, LevelUp N level a := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro _ _ a ha; exact absurd ha List.not_mem_nil
  | append_singleton q b ih =>
    intro w hc a ha
    obtain ⟨hq, -, -, hl, -⟩ := hc.dropLast
    rcases List.mem_append.1 ha with ha | ha
    · exact ih hq a ha
    · rw [List.mem_singleton.1 ha]
      exact ⟨q.length, hq.level_end, hl⟩

/-- The tail of an arrow on a climbing path is not where the path ends. -/
theorem Climbs.tail_ne {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop}
    {p : List ResidualArrow} {w : ℕ} (hc : Climbs N level ok p w) {a : ResidualArrow}
    (ha : a ∈ p) : a.tail N ≠ w := by
  intro e
  obtain ⟨l, hl, hl'⟩ := hc.levelUp a ha
  obtain ⟨j, hj, hj'⟩ := hc.level_le (x := a.head N)
    (by unfold visits; exact List.mem_cons_of_mem _ (List.mem_map_of_mem ha))
  rw [e, hc.level_end] at hl
  rw [hl'] at hj'
  simp at hl hj'
  omega

/-- No two arrows of a climbing path belong to the same arrow of the network. -/
theorem Climbs.ids_nodup {N : Network} {level : ℕ → Option ℕ} {ok : ResidualArrow → Prop} :
    ∀ {p : List ResidualArrow} {w : ℕ}, Climbs N level ok p w → (p.map (·.id)).Nodup := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro _ _; simp
  | append_singleton q a ih =>
    intro w hc
    obtain ⟨hq, -, -, hl, -⟩ := hc.dropLast
    rw [List.map_append, List.nodup_append]
    refine ⟨ih hq, by simp, fun x hx y hy => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
    obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hx
    subst hy
    intro e
    have deep : ∀ z ∈ visits N N.source q, level z ≠ some (q.length + 1) := by
      intro z hz e'
      obtain ⟨j, hj, hj'⟩ := hq.level_le hz
      rw [e'] at hj'
      simp at hj'
      omega
    rcases ResidualArrow.ends_of_id_eq N e with h | h
    · exact deep _ (by unfold visits; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hc'))
        (h ▸ hl)
    · exact deep _ (mem_visits_tail hq.1 c hc') (h ▸ hl)

/-! ## What sending along a path does to each arrow -/

theorem ResidualArrow.residualCapacity_congr (N : Network) {g g' : Flow} {a : ResidualArrow}
    (h : g.on a.id = g'.on a.id) : a.residualCapacity N g = a.residualCapacity N g' := by
  cases a <;> simp_all [ResidualArrow.residualCapacity, ResidualArrow.id]

theorem length_sendOne (x : ℕ) (g : Flow) (a : ResidualArrow) :
    (sendOne x g a).length = g.length := by
  cases a <;> simp [sendOne]

theorem sendOne_on_self (x : ℕ) {g : Flow} {a : ResidualArrow} (h : a.id < g.length) :
    (sendOne x g a).on a.id = match a with
      | .along i => g.on i + x
      | .back i => g.on i - x := by
  cases a with
  | along i => simp [sendOne, ResidualArrow.id, Flow.on_modify _ _ (show i < g.length from h)]
  | back i => simp [sendOne, ResidualArrow.id, Flow.on_modify _ _ (show i < g.length from h)]

theorem residualCapacity_sendOne_self (N : Network) (x : ℕ) {g : Flow} {a : ResidualArrow}
    (h : a.id < g.length) : a.residualCapacity N (sendOne x g a) = a.residualCapacity N g - x := by
  have e := sendOne_on_self x h
  cases a with
  | along i =>
    simp only [ResidualArrow.residualCapacity, ResidualArrow.id] at e ⊢
    rw [e]; omega
  | back i =>
    simp only [ResidualArrow.residualCapacity, ResidualArrow.id] at e ⊢
    exact e

theorem length_foldl_sendOne (x : ℕ) :
    ∀ (p : List ResidualArrow) (g : Flow), (p.foldl (sendOne x) g).length = g.length
  | [], _ => rfl
  | a :: p, g => by rw [List.foldl_cons, length_foldl_sendOne x p, length_sendOne]

/-- Sending along a path leaves every arrow off it as it was. -/
theorem foldl_sendOne_on_not_mem (x : ℕ) :
    ∀ (p : List ResidualArrow) (g : Flow), (∀ c ∈ p, c.id < g.length) → ∀ j,
      j ∉ p.map (·.id) → (p.foldl (sendOne x) g).on j = g.on j
  | [], _, _, _, _ => rfl
  | a :: p, g, hl, j, hj => by
    simp only [List.map_cons, List.mem_cons, not_or] at hj
    rw [List.foldl_cons, foldl_sendOne_on_not_mem x p _ (fun c hc => by
      rw [length_sendOne]; exact hl c (by simp [hc])) j hj.2,
      sendOne_on_ne x (hl a (by simp)) hj.1]

/-- Sending along a path that uses each arrow of the network at most once changes each arrow on
it as sending along that arrow alone would. -/
theorem foldl_sendOne_on_mem (x : ℕ) :
    ∀ (p : List ResidualArrow) (g : Flow), (∀ c ∈ p, c.id < g.length) →
      (p.map (·.id)).Nodup → ∀ c ∈ p, (p.foldl (sendOne x) g).on c.id = (sendOne x g c).on c.id
  | [], _, _, _, c, hc => absurd hc List.not_mem_nil
  | a :: p, g, hl, hn, c, hc => by
    rw [List.map_cons, List.nodup_cons] at hn
    have hl' : ∀ c ∈ p, c.id < (sendOne x g a).length := fun c hc => by
      rw [length_sendOne]; exact hl c (by simp [hc])
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact foldl_sendOne_on_not_mem x p _ hl' _ hn.1
    · rw [foldl_sendOne_on_mem x p _ hl' hn.2 c hc]
      have hne : c.id ≠ a.id := fun e => hn.1 (e ▸ List.mem_map_of_mem hc)
      have hc' : c.id < g.length := hl c (by simp [hc])
      have hca : c.id < (sendOne x g a).length := by rw [length_sendOne]; exact hc'
      have e := sendOne_on_ne x (hl a (by simp)) hne
      rw [sendOne_on_self x hca, sendOne_on_self x hc']
      cases c <;> simp only [ResidualArrow.id] at e ⊢ <;> rw [e]

/-- **The room each arrow of the path has after sending along it**: what it had, less the amount. -/
theorem residualCapacity_apply_mem (N : Network) {x : Augmentation} {g : Flow}
    (hl : ∀ c ∈ x.path, c.id < g.length) (hn : (x.path.map (·.id)).Nodup) {c : ResidualArrow}
    (hc : c ∈ x.path) : c.residualCapacity N (x.apply g) = c.residualCapacity N g - x.amount := by
  rw [← residualCapacity_sendOne_self N x.amount (hl c hc)]
  exact ResidualArrow.residualCapacity_congr N (foldl_sendOne_on_mem x.amount x.path g hl hn c hc)

/-- An arrow none of whose network arrow is on the path keeps its room. -/
theorem residualCapacity_apply_not_mem (N : Network) {x : Augmentation} {g : Flow}
    (hl : ∀ c ∈ x.path, c.id < g.length) {a : ResidualArrow} (ha : a.id ∉ x.path.map (·.id)) :
    a.residualCapacity N (x.apply g) = a.residualCapacity N g :=
  ResidualArrow.residualCapacity_congr N (foldl_sendOne_on_not_mem x.amount x.path g hl a.id ha)

theorem bottleneck_mem {N : Network} {f : Flow} {p : List ResidualArrow} (hp : p ≠ []) :
    ∃ b ∈ p, b.residualCapacity N f = bottleneck N f p := by
  obtain ⟨m, hm⟩ : ∃ m, (p.map (·.residualCapacity N f)).min? = some m :=
    Option.isSome_iff_exists.1 (List.isSome_min?_of_ne_nil (by simpa using hp))
  obtain ⟨b, hb, e⟩ := List.mem_map.1 (List.min?_eq_some_iff.1 hm).1
  exact ⟨b, hb, by rw [bottleneck, hm, Option.getD_some, e]⟩

theorem mem_visits_end {N : Network} :
    ∀ {p : List ResidualArrow} {u v : ℕ}, ends N u p = some v → v ∈ visits N u p
  | [], u, v, he => by simp only [ends, Option.some.injEq] at he; simp [visits, he]
  | a :: p, u, v, he => by
    simp only [ends] at he
    split_ifs at he with ha
    have := mem_visits_end he
    simp only [visits, List.map_cons, List.mem_cons] at this ⊢
    tauto

theorem ends_ids_lt {N : Network} :
    ∀ {p : List ResidualArrow} {u v : ℕ}, ends N u p = some v → ∀ a ∈ p,
      a.id < N.g.arrows.length
  | [], _, _, _, a, ha => absurd ha List.not_mem_nil
  | b :: p, u, v, he, a, ha => by
    simp only [ends] at he
    split_ifs at he with hb
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hb.1
    · exact ends_ids_lt he a ha

theorem fitInTurn_append_one {N : Network} {x : Augmentation} :
    ∀ {f : Flow} {xs : List Augmentation}, FitInTurn N f xs →
      (IsAugmentingPath N (applyAll f xs) x.path ∧
        ∀ a ∈ x.path, x.amount ≤ a.residualCapacity N (applyAll f xs)) → FitInTurn N f (xs ++ [x])
  | _, [], _, hx => ⟨hx, trivial⟩
  | _, _ :: _, h, hx => ⟨h.1, fitInTurn_append_one h.2 hx⟩

theorem applyAll_append_one (f : Flow) (xs : List Augmentation) (x : Augmentation) :
    applyAll f (xs ++ [x]) = x.apply (applyAll f xs) := by
  simp [applyAll, List.foldl_append]

/-! ## The search goes level by level -/

/-- The level of `x`, read as 0 when unlabeled. -/
def Labels.lev (L : Labels) (x : ℕ) : ℕ := (L.level x).getD 0

/-- **The search goes level by level**: the queued vertices are in order of level and span at
most two levels; a vertex taken off the queue is on no deeper level than any queued one, and
labeled the head of each of its arrows that fits the threshold, on a level at most one deeper. -/
def Labels.Layered (N : Network) (f : Flow) (Δ : ℕ) (L : Labels) : Prop :=
  L.queue.Pairwise (fun x y => L.lev x ≤ L.lev y) ∧
    (∀ x ∈ L.queue, ∀ y ∈ L.queue, L.lev y ≤ L.lev x + 1) ∧
    (∀ x, (L.level x).isSome → x ∉ L.queue → ∀ y ∈ L.queue, L.lev x ≤ L.lev y) ∧
    (∀ x, (L.level x).isSome → x ∉ L.queue → ∀ c ∈ N.residualOut x, Fits N f Δ c →
      ∃ l, L.level (c.head N) = some l ∧ l ≤ L.lev x + 1)

/-- **Tight below the sink**: every vertex labeled on a level at least two above `ls` labeled the
head of each of its arrows that fits the threshold, on a level at most one deeper. -/
def Labels.Tight (N : Network) (f : Flow) (Δ : ℕ) (L : Labels) (ls : ℕ) : Prop :=
  ∀ x l, L.level x = some l → l + 1 < ls → ∀ c ∈ N.residualOut x, Fits N f Δ c →
    ∃ l', L.level (c.head N) = some l' ∧ l' ≤ l + 1

/-- What one turn's arrows do: the queue grows by new vertices, all one level below the vertex
taken, and the labels given before stay. -/
def Labels.Grows (L : Labels) (q : List ℕ) (lu : ℕ) (L' : Labels) : Prop :=
  ∃ new, L'.queue = q ++ new ∧ (∀ x ∈ new, L'.level x = some (lu + 1)) ∧
    (∀ x l, L.level x = some l → L'.level x = some l) ∧
    (∀ x, (L'.level x).isSome → (L.level x).isSome ∨ x ∈ new)

theorem Labels.Grows.labelOne {N : Network} {f : Flow} {Δ lu : ℕ} {L L' : Labels} {q : List ℕ}
    (hg : L.Grows q lu L') (a : ResidualArrow) : L.Grows q lu (labelOne N f Δ lu L' a) := by
  obtain ⟨new, hq, hn, hold, hnew⟩ := hg
  rcases labelOne_cases N f Δ lu L' a with he | ⟨hw, he⟩
  · rw [he]; exact ⟨new, hq, hn, hold, hnew⟩
  · rw [he]
    refine ⟨new ++ [a.head N], by simp [hq], fun x hx => ?_, fun x l hx => ?_, fun x hx => ?_⟩
    · by_cases hxw : x = a.head N
      · simp [hxw]
      · simp only [List.mem_append, List.mem_singleton, hxw, or_false] at hx
        simp [Function.update_of_ne hxw, hn x hx]
    · have h' := hold x l hx
      have hxw : x ≠ a.head N := fun e => by simp [e ▸ h'] at hw
      simp [Function.update_of_ne hxw, h']
    · by_cases hxw : x = a.head N
      · simp [hxw]
      · simp only [Function.update_of_ne hxw] at hx
        rcases hnew x hx with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem Labels.lev_of_level {L : Labels} {x l : ℕ} (h : L.level x = some l) : L.lev x = l := by
  simp [Labels.lev, h]

/-- **One turn keeps the search level by level**, or labels the sink and leaves it tight below. -/
theorem Labels.Layered.turn {N : Network} {f : Flow} {Δ : ℕ} {L : Labels} {u lu : ℕ}
    {q : List ℕ} (hL : L.Layered N f Δ) (hq : L.queue = u :: q) (hu : L.level u = some lu)
    (hql : ∀ x ∈ L.queue, (L.level x).isSome) (hs : L.level N.sink = none) :
    let R := (N.residualOut u).foldl (labelOne N f Δ lu) { L with queue := q }
    (R.level N.sink = none → R.Layered N f Δ) ∧
      ∀ ls, R.level N.sink = some ls → R.Tight N f Δ ls := by
  intro R
  have hg : L.Grows q lu R := foldl_keeps (fun L' => L.Grows q lu L') _ _ _
    ⟨[], by simp, by simp, fun _ _ h => h, fun _ h => Or.inl h⟩ fun a _ L' h => h.labelOne a
  obtain ⟨new, hRq, hnew, hold, hlab⟩ := hg
  obtain ⟨hpw, hspan, hpop, hclose⟩ := hL
  rw [hq] at hpw hspan hpop
  have hlu : L.lev u = lu := Labels.lev_of_level hu
  have hRlev : ∀ x, (L.level x).isSome → R.lev x = L.lev x := fun x hx => by
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hx
    rw [Labels.lev_of_level hl, Labels.lev_of_level (hold x l hl)]
  -- every queued vertex is between `lu` and `lu + 1`
  have hqlev : ∀ x ∈ q, lu ≤ L.lev x ∧ L.lev x ≤ lu + 1 := fun x hx =>
    ⟨hlu ▸ List.rel_of_pairwise_cons hpw hx, hlu ▸ hspan u (by simp) x (by simp [hx])⟩
  -- labels of `L` are at most `lu + 1`
  have hall : ∀ x, (L.level x).isSome → L.lev x ≤ lu + 1 := by
    intro x hx
    by_cases hxq : x ∈ u :: q
    · exact hlu ▸ hspan u (by simp) x hxq
    · have := hpop x hx (hq ▸ hxq) u (by simp); omega
  have hqlab : ∀ x ∈ q, (L.level x).isSome := fun x hx => hql x (by simp [hq, hx])
  have hnewlev : ∀ x ∈ new, R.lev x = lu + 1 := fun x hx => Labels.lev_of_level (hnew x hx)
  have hRrange : ∀ x ∈ R.queue, lu ≤ R.lev x ∧ R.lev x ≤ lu + 1 := by
    intro x hx
    rw [hRq] at hx
    rcases List.mem_append.1 hx with hx | hx
    · rw [hRlev x (hqlab x hx)]; exact hqlev x hx
    · rw [hnewlev x hx]; omega
  -- a vertex labeled before this turn that is not queued now is `u` or was taken off earlier
  have hpopR : ∀ x, (L.level x).isSome → x ∉ q → L.lev x ≤ lu := by
    intro x hx hxq
    by_cases hxu : x = u
    · rw [hxu, hlu]
    · have := hpop x hx (by simp [hxu, hxq]) u (by simp); omega
  refine ⟨fun hRs => ⟨?_, ?_, ?_, ?_⟩, fun ls hls => ?_⟩
  · rw [hRq, List.pairwise_append]
    refine ⟨(List.pairwise_cons.1 hpw).2.imp_of_mem fun hx hy hxy => ?_,
      List.pairwise_of_forall_mem_list fun x hx y hy => by rw [hnewlev x hx, hnewlev y hy],
      fun x hx y hy => ?_⟩
    · rw [hRlev _ (hqlab _ hx), hRlev _ (hqlab _ hy)]; exact hxy
    · rw [hRlev x (hqlab x hx), hnewlev y hy]; exact (hqlev x hx).2
  · intro x hx y hy
    have := hRrange x hx; have := hRrange y hy; omega
  · intro x hx hxq y hy
    have hxL : (L.level x).isSome := by
      rcases hlab x hx with h | h
      · exact h
      · exact absurd (by rw [hRq]; simp [h]) hxq
    have hxq' : x ∉ q := fun h => hxq (by rw [hRq]; simp [h])
    rw [hRlev x hxL]
    have := hpopR x hxL hxq'; have := hRrange y hy; omega
  · intro x hx hxq c hc hfit
    have hxL : (L.level x).isSome := by
      rcases hlab x hx with h | h
      · exact h
      · exact absurd (by rw [hRq]; simp [h]) hxq
    have hxq' : x ∉ q := fun h => hxq (by rw [hRq]; simp [h])
    rw [hRlev x hxL]
    by_cases hxu : x = u
    · subst hxu
      have hcov := (foldl_labelOne_covers (lu := lu) (N.residualOut x) { L with queue := q } c hc
        hfit).resolve_left (by simp [R] at hRs ⊢; simp [hRs])
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hcov
      change R.level _ = some l at hl
      refine ⟨l, hl, ?_⟩
      rw [hlu]
      rcases hlab _ hcov with h | h
      · obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 h
        have := hall _ h
        rw [Labels.lev_of_level hl'] at this
        rw [hold _ _ hl', Option.some.injEq] at hl
        omega
      · rw [hnew _ h, Option.some.injEq] at hl; omega
    · obtain ⟨l, hl, hle⟩ := hclose x hxL (by rw [hq]; simp [hxu, hxq']) c hc hfit
      exact ⟨l, hold _ _ hl, hle⟩
  · intro x l hx hl c hc hfit
    have hsnew : N.sink ∈ new := by
      rcases hlab N.sink (by simp [hls]) with h | h
      · simp [hs] at h
      · exact h
    rw [hnew _ hsnew, Option.some.injEq] at hls
    subst hls
    have hxnew : x ∉ new := fun h => by rw [hnew x h, Option.some.injEq] at hx; omega
    have hxL : (L.level x).isSome := (hlab x (by simp [hx])).resolve_right hxnew
    obtain ⟨l₀, hl₀⟩ := Option.isSome_iff_exists.1 hxL
    have e := hold x l₀ hl₀
    rw [hx, Option.some.injEq] at e
    subst e
    have hxu : x ∉ u :: q := by
      intro hm
      have := (hqlev x ?_).1
      · rw [Labels.lev_of_level hl₀] at this; omega
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [hu, Option.some.injEq] at hl₀; omega
      · exact hm
    obtain ⟨l', hl', hle⟩ := hclose x hxL (hq ▸ hxu) c hc hfit
    rw [Labels.lev_of_level hl₀] at hle
    exact ⟨l', hold _ _ hl', hle⟩

theorem Labels.layered_start (N : Network) (f : Flow) (Δ : ℕ) :
    (Labels.start N).Layered N f Δ := by
  refine ⟨by simp [Labels.start], by simp [Labels.start], fun x hx hxq => ?_,
    fun x hx hxq => ?_⟩ <;>
  · by_cases e : x = N.source
    · simp [Labels.start, e] at hxq
    · simp [Labels.start, Function.update_of_ne e] at hx

theorem searchTurns_tight {N : Network} {f : Flow} {Δ : ℕ} :
    ∀ (k : ℕ) (L : Labels), L.Sound N f Δ → L.Layered N f Δ → L.level N.sink = none →
      ∀ ls, (searchTurns N f Δ k L).level N.sink = some ls →
        (searchTurns N f Δ k L).Tight N f Δ ls
  | 0, L, _, _, hs, ls, hls => by simp [searchTurns, hs] at hls
  | k + 1, L, hL, hlay, hs, ls, hls => by
    match hq : L.queue with
    | [] => simp [searchTurns, hs, hq] at hls
    | u :: q =>
      obtain ⟨lu, hu⟩ := Option.isSome_iff_exists.1 (hL.2.1 u (by simp [hq]))
      have hstep : searchTurns N f Δ (k + 1) L = searchTurns N f Δ k
          ((N.residualOut u).foldl (labelOne N f Δ lu) { L with queue := q }) := by
        simp [searchTurns, hs, hq, hu]
      rw [hstep] at hls ⊢
      have hturn := hlay.turn hq hu hL.2.1 hs
      set R := (N.residualOut u).foldl (labelOne N f Δ lu) { L with queue := q }
      have hRs : R.Sound N f Δ := (foldl_keeps
          (fun L' : Labels => L'.Sound N f Δ ∧ L'.level u = some lu) _ _ { L with queue := q }
          ⟨⟨hL.1, fun x hx => hL.2.1 x (by rw [hq]; exact List.mem_cons_of_mem _ hx), hL.2.2⟩, hu⟩
          fun a ha L' hL' => ⟨hL'.1.of_labelOne hL'.2 ha, labelOne_level hL'.2⟩).1
      cases hRk : R.level N.sink with
      | some ls' =>
        have hsR : (R.level N.sink).isSome := by simp [hRk]
        rw [searchTurns_of_sink hsR] at hls ⊢
        exact hturn.2 ls hls
      | none => exact searchTurns_tight k R hRs (hturn.1 hRk) hRk ls hls

/-- **The search's levels are tight below the sink**. -/
theorem search_tight {N : Network} (h : N.WellFormed) {f : Flow} {Δ ls : ℕ}
    (hls : (search N f Δ).level N.sink = some ls) : (search N f Δ).Tight N f Δ ls := by
  refine searchTurns_tight _ _ (Labels.sound_start N f Δ) (Labels.layered_start N f Δ) ?_ ls hls
  simp [Labels.start, Function.update_of_ne (Ne.symm h.2.2.2.2)]

/-! ## Levels as lower bounds -/

/-- **A labeling that rises by at most one along every arrow passing `ok`** bounds the length of
every path of such arrows: the end is at most as high as the start plus the arrows. -/
theorem le_of_rises {N : Network} {ok : ResidualArrow → Prop} {T : ℕ → ℕ}
    (hT : ∀ c, c.id < N.g.arrows.length → ok c → T (c.head N) ≤ T (c.tail N) + 1) :
    ∀ (q : List ResidualArrow) (w v : ℕ), ends N w q = some v → (∀ c ∈ q, ok c) →
      T v ≤ T w + q.length
  | [], w, v, he, _ => by simp only [ends, Option.some.injEq] at he; simp [he]
  | c :: q, w, v, he, hq => by
    simp only [ends] at he
    split_ifs at he with hc
    have h1 := hT c hc.1 (hq c (by simp))
    have h2 := le_of_rises hT q _ v he fun d hd => hq d (by simp [hd])
    rw [hc.2] at h1
    simp only [List.length_cons]
    omega

/-- The search's levels, cut at the sink's level `ls`: unlabeled vertices count as `ls`. -/
def Labels.cut (L : Labels) (ls v : ℕ) : ℕ := min ((L.level v).getD ls) ls

/-- **The cut levels rise by at most one along every arrow that fits the threshold.** -/
theorem search_cut_rises {N : Network} (h : N.WellFormed) {f : Flow} {Δ ls : ℕ}
    (hls : (search N f Δ).level N.sink = some ls) (c : ResidualArrow)
    (hc : c.id < N.g.arrows.length) (hfit : Fits N f Δ c) :
    (search N f Δ).cut ls (c.head N) ≤ (search N f Δ).cut ls (c.tail N) + 1 := by
  unfold Labels.cut
  cases ht : (search N f Δ).level (c.tail N) with
  | none => simp
  | some l =>
    by_cases hl : l + 1 < ls
    · obtain ⟨l', hl', hle⟩ := search_tight h hls (c.tail N) l ht hl c
        (mem_residualOut.2 ⟨hc, rfl⟩) hfit
      simp [hl']; omega
    · simp; omega

/-- **No path that fits the threshold reaches a vertex in fewer arrows than its cut level.** -/
theorem search_cut_le {N : Network} (h : N.WellFormed) {f : Flow} {Δ ls : ℕ}
    (hls : (search N f Δ).level N.sink = some ls) {q : List ResidualArrow} {v : ℕ}
    (he : ends N N.source q = some v) (hq : ∀ c ∈ q, Fits N f Δ c) :
    (search N f Δ).cut ls v ≤ q.length := by
  have := le_of_rises (search_cut_rises h hls) q _ v he hq
  have h0 : (search N f Δ).cut ls N.source = 0 := by
    simp [Labels.cut, (Labels.sound_search N f Δ).1]
  omega

/-! ## Sums over the vertices -/

theorem sum_range_bump {g : ℕ → ℕ} {v : ℕ} :
    ∀ n, v < n → ((List.range n).map (Function.update g v (g v + 1))).sum =
      ((List.range n).map g).sum + 1
  | 0, hv => absurd hv (Nat.not_lt_zero v)
  | n + 1, hv => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    by_cases hn : v = n
    · subst hn
      have : (List.range v).map (Function.update g v (g v + 1)) = (List.range v).map g :=
        List.map_congr_left fun w hw =>
          Function.update_of_ne (Nat.ne_of_lt (List.mem_range.1 hw)) _ _
      simp [this]
      omega
    · rw [sum_range_bump n (by omega)]
      simp [Function.update_of_ne (Ne.symm hn)]
      omega

theorem sum_range_le {g : ℕ → ℕ} {b : ℕ} (hg : ∀ v, g v ≤ b) (n : ℕ) :
    ((List.range n).map g).sum ≤ n * b := by
  have := List.sum_le_length_nsmul ((List.range n).map g) b (by
    intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact hg v)
  simpa using this

/-! ## Sending along the path found keeps every vertex as far -/

/-- **`v` is at least `K` arrows away** under the flow `g`: every path with room from the source
to `v` has at least `K` arrows. -/
def FarAtLeast (N : Network) (g : Flow) (v K : ℕ) : Prop :=
  ∀ q, ends N N.source q = some v → (∀ c ∈ q, 0 < c.residualCapacity N g) → K ≤ q.length

theorem FarAtLeast.mono {N : Network} {g : Flow} {v K K' : ℕ} (h : FarAtLeast N g v K)
    (hK : K' ≤ K) : FarAtLeast N g v K' := fun q he hq => hK.trans (h q he hq)

/-- A vertex the search labeled on level `k` is reached by a path with room of `k` arrows. -/
theorem search_near {N : Network} {g : Flow} {w k : ℕ} (hw : (search N g 1).level w = some k) :
    ∃ r, ends N N.source r = some w ∧ (∀ c ∈ r, 0 < c.residualCapacity N g) ∧ r.length = k := by
  obtain ⟨r, -, hc, hl⟩ := (Labels.sound_search N g 1).pathBack k w k [] hw le_rfl
  exact ⟨r, hc.1, fun c hc' => (hc.2.2 c hc').1, hl⟩

/-- A vertex the search labeled on level `k`, no deeper than the sink, is at least `k` arrows
away. -/
theorem search_far {N : Network} (h : N.WellFormed) {g : Flow} {ls w k : ℕ}
    (hls : (search N g 1).level N.sink = some ls) (hw : (search N g 1).level w = some k)
    (hk : k ≤ ls) : FarAtLeast N g w k := by
  intro q he hq
  have := search_cut_le h hls he fun c hc => fits_of_le_one le_rfl (hq c hc)
  simp only [Labels.cut, hw, Option.getD_some] at this
  omega

/-- After sending along a climbing path, an arrow with room had room before, or is the way back
of an arrow of the path. -/
theorem residualCapacity_apply_grow_mem {N : Network} {level : ℕ → Option ℕ}
    {ok : ResidualArrow → Prop}
    {x : Augmentation} {g : Flow} {v : ℕ} (hp : Climbs N level ok x.path v)
    (hl : ∀ c ∈ x.path, c.id < g.length) {a : ResidualArrow}
    (ha : 0 < a.residualCapacity N (x.apply g)) :
    0 < a.residualCapacity N g ∨ ∃ d ∈ x.path, d ≠ a ∧ d.id = a.id := by
  by_cases hm : a.id ∈ x.path.map (·.id)
  · obtain ⟨d, hd, hda⟩ := List.mem_map.1 hm
    by_cases e : d = a
    · subst e
      rw [residualCapacity_apply_mem N hl hp.ids_nodup hd] at ha
      exact Or.inl (by omega)
    · exact Or.inr ⟨d, hd, e, hda⟩
  · rw [residualCapacity_apply_not_mem N hl hm] at ha
    exact Or.inl ha

theorem ResidualArrow.ends_of_partner (N : Network) {c d : ResidualArrow} (hne : d ≠ c)
    (h : d.id = c.id) : c.tail N = d.head N ∧ c.head N = d.tail N := by
  cases c <;> cases d <;> simp_all [ResidualArrow.id, ResidualArrow.head, ResidualArrow.tail]

/-- Every vertex on the path the search finds is labeled no deeper than the sink. -/
theorem shortestPath_levels {N : Network} (h : N.WellFormed) {g : Flow} {p : List ResidualArrow}
    (hp : shortestPath N g 1 = some p) {ls : ℕ} (hls : (search N g 1).level N.sink = some ls)
    {d : ResidualArrow} (hd : d ∈ p) : ∃ k, (search N g 1).level (d.tail N) = some k ∧
      (search N g 1).level (d.head N) = some (k + 1) ∧ k + 1 ≤ ls := by
  have hc := shortestPath_climbs h hp
  obtain ⟨k, hk, hk'⟩ := hc.levelUp d hd
  obtain ⟨j, hj, hj'⟩ := hc.level_le (x := d.head N)
    (by unfold visits; exact List.mem_cons_of_mem _ (List.mem_map_of_mem hd))
  have hpl : p.length = ls := by
    have := hc.level_end; rw [hls, Option.some.injEq] at this; exact this.symm
  rw [hk', Option.some.injEq] at hj'
  exact ⟨k, hk, hk', by omega⟩

/-- **A path with room after sending is no shorter than some path with room before**, when the
path sent along was the one the search found. -/
theorem shortestPath_shorter {N : Network} (h : N.WellFormed) {g : Flow}
    (hlen : g.length = N.g.arrows.length) {p : List ResidualArrow}
    (hp : shortestPath N g 1 = some p) {ls : ℕ} (hls : (search N g 1).level N.sink = some ls) :
    ∀ (q : List ResidualArrow) (v : ℕ), ends N N.source q = some v →
      (∀ c ∈ q, 0 < c.residualCapacity N ((byBottleneck N g p).apply g)) →
      ∃ r, ends N N.source r = some v ∧ (∀ c ∈ r, 0 < c.residualCapacity N g) ∧
        r.length ≤ q.length := by
  have hc := shortestPath_climbs h hp
  have hids : ∀ c ∈ (byBottleneck N g p).path, c.id < g.length := fun c hc' =>
    hlen ▸ ends_ids_lt hc.1 c hc'
  intro q
  induction q using List.reverseRecOn with
  | nil =>
    intro v hv _
    exact ⟨[], hv, by simp, le_rfl⟩
  | append_singleton q c ih =>
    intro v hv hr
    obtain ⟨t, ht, hid, htail, hhead⟩ := ends_snoc hv
    obtain ⟨r, hre, hrr, hrl⟩ := ih t ht fun e he => hr e (by simp [he])
    rcases residualCapacity_apply_grow_mem (x := byBottleneck N g p) hc hids (hr c (by simp)) with
      h0 | ⟨d, hd, hne, hdid⟩
    · refine ⟨r ++ [c], hhead ▸ ends_append_one N c r _ _ hre hid htail, ?_, by simp; omega⟩
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hrr e he
      · rw [List.mem_singleton.1 he]; exact h0
    · obtain ⟨hct, hch⟩ := ResidualArrow.ends_of_partner N hne hdid
      obtain ⟨k, hk, hk', hkl⟩ := shortestPath_levels h hp hls hd
      have hfar := search_far h hls hk' hkl r (by rw [hre, ← htail, hct]) hrr
      obtain ⟨r', hre', hrr', hrl'⟩ := search_near hk
      refine ⟨r', by rw [hre', ← hhead, hch], hrr', ?_⟩
      simp only [List.length_append, List.length_singleton]
      omega

/-- **Sending along the path the search finds keeps every vertex at least as far.** -/
theorem shortestPath_far {N : Network} (h : N.WellFormed) {g : Flow}
    (hlen : g.length = N.g.arrows.length) {p : List ResidualArrow}
    (hp : shortestPath N g 1 = some p) {ls : ℕ} (hls : (search N g 1).level N.sink = some ls)
    {v K : ℕ} (hK : FarAtLeast N g v K) : FarAtLeast N ((byBottleneck N g p).apply g) v K := by
  intro q he hq
  obtain ⟨r, hre, hrr, hrl⟩ := shortestPath_shorter h hlen hp hls q v he hq
  exact (hK r hre hrr).trans hrl

/-! ## Bounds per round add up -/

/-- If every round of a rule that keeps the promise adds at most `B` paths, every round of the
loop does. -/
theorem PathRule.runRounds_each {r : PathRule} (hr : r.Promise) {N : Network} (h : N.WellFormed)
    {B : ℕ} (hB : ∀ m g, IsFlow N g → (r.round N m g).2.length ≤ B) :
    ∀ (k : ℕ) (m : r.Memory) (g : Flow), IsFlow N g → ∀ xs ∈ (r.runRounds N k m g).1,
      xs.length ≤ B
  | 0, _, _, _, xs, hxs => by simp [PathRule.runRounds] at hxs
  | k + 1, m, g, hg, xs, hxs => by
    rcases hround : r.round N m g with ⟨m', _ | ⟨x, ys⟩⟩
    · rw [r.runRounds_nil N k hround] at hxs
      simp at hxs
    · rw [r.runRounds_cons N k hround] at hxs
      rcases List.mem_cons.1 hxs with rfl | hxs
      · have := hB m g hg; rw [hround] at this; exact this
      · have hfit := hr.sendsAlong N h m g hg
        rw [hround] at hfit
        exact PathRule.runRounds_each hr h hB k m' _ (applyAll_isFlow h hg hfit).1 xs hxs

/-- The paths of all the rounds number at most the rounds times the most one round adds. -/
theorem length_flatten_le {xss : List (List Augmentation)} {B : ℕ}
    (h : ∀ xs ∈ xss, xs.length ≤ B) : xss.flatten.length ≤ xss.length * B := by
  rw [List.length_flatten]
  have := List.sum_le_length_nsmul (xss.map List.length) B (by
    intro x hx
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.1 hx
    exact h xs hxs)
  simpa using this

end AlgoDesign.Flows
