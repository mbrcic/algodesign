/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Finish
public import AlgoDesign.Geometry.GraphIndex.Greedy

/-!
# The graph index: the search's walk

Malkov–Yashunin Alg. 5 as the Rust runs it. The walk starts at the entry and descends the layers
above 0, from the entry's top layer down to 1, each by the layer search with a beam of one
(Alg. 2, SEARCH-LAYER, at width 1), starting where the layer above stopped. On layer 0 it runs the
layer search at width `max ef k`, and the search ends with `finish` on the beam it holds. A
search for no neighbors, or on a graph with no points, answers nothing.

The layer search keeps its two heaps as lists in `ByDistance` order, nearest first (`sorted_weigh`,
`sorted_searchLayer`): the candidates, whose nearest is expanded next (a heap's pop is the head),
and the beam, whose farthest is the last (a heap's peek and pop of the worst). Each layer starts
with a fresh visited list. From the start node, it expands the nearest candidate, stopping when
there is none or when that candidate is strictly farther than the beam's farthest; it weighs the
expanded node's list on that layer in list order, skipping every node already visited, marks each
one visited, and pushes it to both lists when it is strictly nearer than the beam's farthest or the
beam has room, then drops the beam's farthest when the beam is over its width. An empty beam has no
farthest: nothing stops, everything is pushed.

The layer search ends because every push visits a node some list of the graph names, never
visited before (`weigh_measure`): `2 · unvisited + candidates` falls with every expansion.

Proved here: on a valid graph, the search answers what `finish` answers on a beam of stored nodes,
each once, not empty when `k` is positive and the graph has nodes, and at most `max ef k` long
(`search_eq_finish`). And the layer search with a beam of one is the greedy walk: it ends holding
just the first fixed point that repeated greedy steps from its start reach (`searchLayer_one`,
`descend_cons`). Rust: `Hnsw::search`, `Hnsw::walk`, `Hnsw::search_layer_found`.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace HNSW

variable {d : ℕ} {α : Type} [CommRing α] [LinearOrder α]

/-- Every node some list of the graph names. -/
def linked (g : HNSW d α) : List ℕ := g.links.flatten.flatten

/-- How many of `us` are not in `vs`. -/
def unvisited (us vs : List ℕ) : ℕ := us.countP fun u => u ∉ vs

/-- The layer search's state: the candidates to expand, nearest first; the beam, nearest first;
and the nodes visited on this layer. -/
structure LayerState (α : Type) where
  /-- The nodes reached and not yet expanded, nearest first. -/
  cands : List (Neighbor α)
  /-- The beam: the nearest nodes reached, at most its width, nearest first. -/
  found : List (Neighbor α)
  /-- The nodes weighed on this layer, the start included. -/
  visited : List ℕ

/-- `x` is strictly nearer than the beam's farthest; true when the beam is empty. -/
def nearerThanFarthest (found : List (Neighbor α)) (x : α) : Bool :=
  match found.getLast? with
  | none => true
  | some f => decide (x < f.sqDist)

/-- `x` is strictly farther than the beam's farthest; false when the beam is empty. -/
def fartherThanFarthest (found : List (Neighbor α)) (x : α) : Bool :=
  match found.getLast? with
  | none => false
  | some f => decide (f.sqDist < x)

/-- Visiting a node of `us` not visited before leaves fewer of `us` unvisited. -/
theorem unvisited_cons_lt {us vs : List ℕ} {e : ℕ} (he : e ∈ us) (hv : e ∉ vs) :
    unvisited us (e :: vs) < unvisited us vs := by
  induction us with
  | nil => simp at he
  | cons u us ih =>
    simp only [unvisited, List.countP_cons] at ih ⊢
    rcases List.mem_cons.mp he with rfl | h
    · have := List.countP_mono_left (l := us) (p := fun u => decide (u ∉ e :: vs))
        (q := fun u => decide (u ∉ vs)) (by
          intro x _ hx
          simp only [List.mem_cons, not_or, decide_eq_true_eq] at hx ⊢
          exact hx.2)
      simp only [List.mem_cons_self, not_true_eq_false, decide_false, hv, not_false_eq_true,
        decide_true, Bool.false_eq_true, ite_false, ite_true]
      omega
    · have := ih h
      by_cases hu : u ∈ vs
      · have hu' : u ∈ e :: vs := List.mem_cons_of_mem e hu
        simp only [hu, hu', not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
        omega
      · by_cases hue : u = e
        · subst hue
          simp only [List.mem_cons_self, hu, not_true_eq_false, not_false_eq_true,
            decide_false, decide_true, Bool.false_eq_true, ite_false, ite_true]
          omega
        · have hu' : u ∉ e :: vs := by simp [hu, hue]
          simp only [hu, hu', not_false_eq_true, decide_true, ite_true]
          omega

/-- Weigh the nodes `es` of an expanded node's list, in list order, for the query `q` at beam width
`ef`: skip a node already visited; else mark it visited, and push it to the candidates and the
beam when it is strictly nearer than the beam's farthest or the beam has room, dropping the
beam's farthest when the beam is then over `ef`. -/
def weigh (g : HNSW d α) (q : Point d α) (ef : ℕ) : List ℕ → LayerState α → LayerState α
  | [], s => s
  | e :: es, s =>
    if e ∈ s.visited then weigh g q ef es s
    else
      let n : Neighbor α := ⟨sqDist g.points[e]! q, e⟩
      if nearerThanFarthest s.found n.sqDist || decide (s.found.length < ef) then
        let found := s.found.orderedInsert ByDistance n
        weigh g q ef es ⟨s.cands.orderedInsert ByDistance n,
          if ef < found.length then found.dropLast else found, e :: s.visited⟩
      else weigh g q ef es ⟨s.cands, s.found, e :: s.visited⟩

/-- Each node `weigh` visits is named by some list of the graph and was not visited before, and
each node it pushes it visits, so `2 · unvisited + candidates` does not grow. -/
theorem weigh_measure (g : HNSW d α) (q : Point d α) (ef : ℕ) (es : List ℕ)
    (hes : ∀ e ∈ es, e ∈ g.linked) (s : LayerState α) :
    2 * unvisited g.linked (weigh g q ef es s).visited + (weigh g q ef es s).cands.length ≤
      2 * unvisited g.linked s.visited + s.cands.length := by
  induction es generalizing s with
  | nil => simp [weigh]
  | cons e es ih =>
    have hes' : ∀ x ∈ es, x ∈ g.linked := fun x hx => hes x (List.mem_cons_of_mem e hx)
    have hlt := fun (h : e ∉ s.visited) => unvisited_cons_lt (hes e List.mem_cons_self) h
    simp only [weigh]
    by_cases hv : e ∈ s.visited
    · simp only [hv, ite_true]
      exact ih hes' s
    · have h2 := hlt hv
      simp only [hv, ite_false]
      split
      · refine (ih hes' _).trans ?_
        simp only [List.orderedInsert_length]
        omega
      · refine (ih hes' _).trans ?_
        dsimp only
        omega

omit [CommRing α] [LinearOrder α] in
/-- A node a neighbor list names is in `linked`. -/
theorem mem_linked {g : HNSW d α} {v l x : ℕ} (h : x ∈ g.neighbors v l) : x ∈ g.linked := by
  unfold neighbors at h
  unfold linked
  simp only [List.mem_flatten]
  by_cases hv : v < g.links.length
  · by_cases hl : l < (g.links[v]).length
    · refine ⟨g.links[v][l], ⟨g.links[v], List.getElem_mem hv, List.getElem_mem hl⟩, ?_⟩
      simpa [List.getD_eq_getElem?_getD, hv, hl] using h
    · simp [List.getD_eq_getElem?_getD, hv, hl] at h
  · simp [List.getD_eq_getElem?_getD, hv] at h

/-- The layer search's loop: expand the nearest candidate unless it is strictly farther than the
beam's farthest, weighing its list on layer `l`; stop when no candidate is left. Returns the
beam. -/
def expand (g : HNSW d α) (q : Point d α) (ef l : ℕ) (s : LayerState α) : List (Neighbor α) :=
  match _hc : s.cands with
  | [] => s.found
  | c :: cs =>
    if fartherThanFarthest s.found c.sqDist then s.found
    else expand g q ef l (weigh g q ef (g.neighbors c.id l) ⟨cs, s.found, s.visited⟩)
termination_by 2 * unvisited g.linked s.visited + s.cands.length
decreasing_by
  have := weigh_measure g q ef (g.neighbors c.id l) (fun _ hx => mem_linked hx)
    ⟨cs, s.found, s.visited⟩
  simp only [_hc, List.length_cons] at this ⊢
  omega

/-- SEARCH-LAYER (Malkov and Yashunin, Alg. 2) from the one start node `ep` on layer `l` at beam
width `ef`: the beam it ends with. The start is visited, a candidate and in the beam, and the beam
is cut to `ef` before the loop. Rust: `Hnsw::search_layer_found`. -/
def searchLayer (g : HNSW d α) (q : Point d α) (ep : Neighbor α) (ef l : ℕ) : List (Neighbor α) :=
  expand g q ef l ⟨[ep], [ep].take ef, [ep.id]⟩

/-- The greedy descent through the layers `ls`, top first: on each, the layer search with a beam
of one from where the layer above stopped, and the nearest node it found (the sorted beam's
first) is where the next layer starts. -/
def descend (g : HNSW d α) (q : Point d α) (ep : Neighbor α) : List ℕ → Neighbor α
  | [] => ep
  | l :: ls => descend g q (((searchLayer g q ep 1 l).insertionSort ByDistance).headD ep) ls

/-- The walk at beam width `ef`: from the entry, the descent from the entry's top layer down to
layer 1, then the layer search at width `ef` on layer 0; the nodes of the beam it ends with. No
entry, no beam. Rust: `Hnsw::walk`. -/
def walk (g : HNSW d α) (q : Point d α) (ef : ℕ) : List ℕ :=
  match g.entry with
  | none => []
  | some e =>
    let ep := descend g q ⟨sqDist g.points[e]! q, e⟩
      ((List.range (g.layers e - 1)).reverse.map (· + 1))
    (searchLayer g q ep ef 0).map Neighbor.id

/-- The search for the `k` nearest to `q` at beam width `ef`: nothing when `k` is 0 or the graph
has no points; else `finish` on the beam of the walk at width `max ef k`. Rust: `Hnsw::search`. -/
def search (g : HNSW d α) (q : Point d α) (k ef : ℕ) : List (Neighbor α) :=
  if k = 0 ∨ g.points.length = 0 then [] else finish g.points q k (walk g q (max ef k))

/-! ## The beam holds what `SearchSpec` asks -/

/-- A beam of width `ef` over nodes that meet `P`: each node once, each meeting `P`, at most `ef`
of them, and not empty when `ef` is positive. -/
structure BeamOk (P : ℕ → Prop) (ef : ℕ) (found : List (Neighbor α)) : Prop where
  nodup : (found.map Neighbor.id).Nodup
  good : ∀ n ∈ found, P n.id
  width : found.length ≤ ef
  nonempty : 0 < ef → found ≠ []

/-- What the layer search keeps true along its loop: the beam is `BeamOk`, and visited. -/
def StateOk (P : ℕ → Prop) (ef : ℕ) (s : LayerState α) : Prop :=
  BeamOk P ef s.found ∧ ∀ n ∈ s.found, n.id ∈ s.visited

/-- Weighing a list of nodes that meet `P` keeps `StateOk`. -/
theorem stateOk_weigh (g : HNSW d α) (q : Point d α) {P : ℕ → Prop} {ef : ℕ} (es : List ℕ)
    (hes : ∀ e ∈ es, P e) (s : LayerState α) (hs : StateOk P ef s) :
    StateOk P ef (weigh g q ef es s) := by
  induction es generalizing s with
  | nil => exact hs
  | cons e es ih =>
    have hes' : ∀ x ∈ es, P x := fun x hx => hes x (List.mem_cons_of_mem e hx)
    obtain ⟨⟨hnd, hgood, hw, hne⟩, hvis⟩ := hs
    by_cases hv : e ∈ s.visited
    · simp only [weigh, hv, ite_true]
      exact ih hes' s ⟨⟨hnd, hgood, hw, hne⟩, hvis⟩
    · simp only [weigh, hv, ite_false]
      split
      · apply ih hes'
        set n : Neighbor α := ⟨sqDist g.points[e]! q, e⟩
        set found := s.found.orderedInsert ByDistance n
        have hperm : found.Perm (n :: s.found) := List.perm_orderedInsert _ _ _
        have hlen : found.length = s.found.length + 1 := by
          simp [found, List.orderedInsert_length]
        have hsub : (if ef < found.length then found.dropLast else found).Sublist found := by
          split
          · exact List.dropLast_sublist _
          · exact List.Sublist.refl _
        have hmem : ∀ m ∈ (if ef < found.length then found.dropLast else found),
            m = n ∨ m ∈ s.found := fun m hm =>
          List.mem_cons.mp (hperm.subset (hsub.subset hm))
        have hen : e ∉ s.found.map Neighbor.id := fun he => by
          obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
          exact hv (hvis m hm)
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · refine List.Nodup.sublist (hsub.map _) ?_
          rw [(hperm.map Neighbor.id).nodup_iff]
          exact List.nodup_cons.mpr ⟨hen, hnd⟩
        · intro m hm
          rcases hmem m hm with rfl | hm
          · exact hes e List.mem_cons_self
          · exact hgood m hm
        · dsimp only
          split
          · rw [List.length_dropLast]; omega
          · omega
        · intro hef
          dsimp only
          split
          · rw [← List.length_pos_iff, List.length_dropLast]; omega
          · rw [← List.length_pos_iff]; omega
        · intro m hm
          rcases hmem m hm with rfl | hm
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hvis m hm)
      · exact ih hes' _ ⟨⟨hnd, hgood, hw, hne⟩, fun m hm => List.mem_cons_of_mem _ (hvis m hm)⟩

/-- The layer search's loop, weighing only lists of nodes that meet `P`, ends with a `BeamOk`
beam. -/
theorem beamOk_expand (g : HNSW d α) (q : Point d α) {P : ℕ → Prop} {ef l : ℕ}
    (hP : ∀ v, ∀ x ∈ g.neighbors v l, P x) (s : LayerState α) (hs : StateOk P ef s) :
    BeamOk P ef (expand g q ef l s) := by
  fun_induction expand g q ef l s with
  | case1 s _ => exact hs.1
  | case2 s c cs _ _ => exact hs.1
  | case3 s c cs h _ ih =>
    exact ih (stateOk_weigh g q _ (hP c.id) _ ⟨hs.1, hs.2⟩)

/-- Weighing keeps both lists nearest first, so the head of the candidates is a min-heap's pop
and the last of the beam a max-heap's peek. -/
theorem sorted_weigh (g : HNSW d α) (q : Point d α) (ef : ℕ) (es : List ℕ) (s : LayerState α)
    (hc : s.cands.Pairwise ByDistance) (hf : s.found.Pairwise ByDistance) :
    (weigh g q ef es s).cands.Pairwise ByDistance ∧
      (weigh g q ef es s).found.Pairwise ByDistance := by
  induction es generalizing s with
  | nil => exact ⟨hc, hf⟩
  | cons e es ih =>
    unfold weigh
    split
    · exact ih s hc hf
    · dsimp only
      split
      · apply ih
        · exact hc.orderedInsert _ _
        · dsimp only
          split
          · exact (hf.orderedInsert _ _).sublist (List.dropLast_sublist _)
          · exact hf.orderedInsert _ _
      · exact ih _ hc hf

/-- The layer search ends with its beam nearest first. -/
theorem sorted_searchLayer (g : HNSW d α) (q : Point d α) (ep : Neighbor α) (ef l : ℕ) :
    (searchLayer g q ep ef l).Pairwise ByDistance := by
  suffices h : ∀ s : LayerState α, s.cands.Pairwise ByDistance → s.found.Pairwise ByDistance →
      (expand g q ef l s).Pairwise ByDistance from
    h _ (List.pairwise_singleton _ _)
      ((List.pairwise_singleton _ _).sublist (List.take_sublist _ _))
  intro s hc hf
  fun_induction expand g q ef l s with
  | case1 => exact hf
  | case2 => exact hf
  | case3 s c cs h _ ih =>
    have hcs : cs.Pairwise ByDistance := by rw [h] at hc; exact hc.of_cons
    have hw := sorted_weigh g q ef (g.neighbors c.id l) ⟨cs, s.found, s.visited⟩ hcs hf
    exact ih hw.1 hw.2

/-- The layer search from a start that meets `P`, on a layer whose lists name only nodes that
meet `P`, ends with a `BeamOk` beam. -/
theorem beamOk_searchLayer (g : HNSW d α) (q : Point d α) {P : ℕ → Prop} {ef l : ℕ}
    (hP : ∀ v, ∀ x ∈ g.neighbors v l, P x) (ep : Neighbor α) (hep : P ep.id) :
    BeamOk P ef (searchLayer g q ep ef l) := by
  refine beamOk_expand g q hP _ ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (List.nodup_singleton ep.id).sublist ((List.take_sublist _ _).map _)
  · intro n hn
    rw [List.mem_singleton.mp ((List.take_sublist _ _).subset hn)]
    exact hep
  · simp
  · intro hef
    simp [List.take_eq_nil_iff]
    omega
  · intro n hn
    rw [List.mem_singleton.mp ((List.take_sublist _ _).subset hn)]
    exact List.mem_singleton_self _

/-- The descent from a start that meets `P`, through layers whose lists name only nodes that meet
`P`, stops at a node that meets `P`. -/
theorem descend_good (g : HNSW d α) (q : Point d α) {P : ℕ → Prop}
    (hP : ∀ v l, ∀ x ∈ g.neighbors v l, P x) (ls : List ℕ) (ep : Neighbor α) (hep : P ep.id) :
    P (descend g q ep ls).id := by
  induction ls generalizing ep with
  | nil => exact hep
  | cons l ls ih =>
    apply ih
    have hok := beamOk_searchLayer g q (ef := 1) (hP · l) ep hep
    rcases h : (searchLayer g q ep 1 l).insertionSort ByDistance with _ | ⟨n, ns⟩
    · exact hep
    · have hn : n ∈ searchLayer g q ep 1 l := by
        rw [← List.mem_insertionSort ByDistance, h]
        exact List.mem_cons_self
      exact hok.good n hn

omit [CommRing α] [LinearOrder α] in
/-- On a valid graph every list names stored nodes. -/
theorem lt_size_of_mem_neighbors {g : HNSW d α} (hg : Valid g) {v l x : ℕ}
    (h : x ∈ g.neighbors v l) : x < g.size := by
  have hl : l < g.layers v := by
    by_contra hl
    rw [neighbors, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)] at h
    simp at h
  have hv : v < g.size := by
    by_contra hv
    rw [layers, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show g.links.length ≤ v from Nat.le_of_not_lt hv)] at hl
    simp at hl
  exact (hg.2.1.2 v hv l hl x h).1

/-- **The search is `finish` on a beam the walk ends with**: on a valid graph, a beam of stored
nodes, each once, not empty when `k` is positive and the graph has nodes, and at most `max ef k`
long. -/
theorem search_eq_finish (g : HNSW d α) (q : Point d α) (k ef : ℕ) (hg : Valid g) :
    ∃ beam : List ℕ, beam.Nodup ∧ (∀ i ∈ beam, i < g.size) ∧
      (0 < k → 0 < g.size → beam ≠ []) ∧ beam.length ≤ max ef k ∧
      search g q k ef = finish g.points q k beam := by
  have hpts : g.points.length = g.size := hg.2.2.2.2.2
  by_cases h0 : k = 0 ∨ g.points.length = 0
  · refine ⟨[], List.nodup_nil, by simp, fun hk hs => ?_, by simp, ?_⟩
    · omega
    · simp only [search, h0, ↓reduceIte]
      simp [finish]
  · have hent := hg.2.2.2.2.1
    unfold EntryOnTop at hent
    rcases he : g.entry with _ | e
    · rw [he] at hent; omega
    rw [he] at hent
    have hP : ∀ v l, ∀ x ∈ g.neighbors v l, x < g.size :=
      fun _ _ _ hx => lt_size_of_mem_neighbors hg hx
    set ep := descend g q ⟨sqDist g.points[e]! q, e⟩
      ((List.range (g.layers e - 1)).reverse.map (· + 1))
    have hep : ep.id < g.size := descend_good g q hP _ _ hent.1
    have hok := beamOk_searchLayer g q (ef := max ef k) (hP · 0) ep hep
    refine ⟨(searchLayer g q ep (max ef k) 0).map Neighbor.id, hok.nodup, ?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hi
      exact hok.good n hn
    · intro hk _
      simpa using hok.nonempty (by omega)
    · simpa using hok.width
    · simp only [search, h0, ↓reduceIte]
      rw [walk, he]

/-! ## A beam of one is the greedy walk -/

/-- Weighing at width 1, from a beam holding just node `j`, with every visited node no nearer
than `j` and every candidate `j` itself or strictly farther: the beam ends holding just the node
the greedy fold over the weighed list reaches from `j`, and the same holds of it. Either nothing
was pushed, or that node is among the candidates. -/
theorem weigh_one (g : HNSW d α) (q : Point d α) (es : List ℕ) (j : ℕ) (s : LayerState α)
    (hf : s.found = [⟨sqDist g.points[j]! q, j⟩])
    (hv : ∀ v ∈ s.visited, sqDist g.points[j]! q ≤ sqDist g.points[v]! q)
    (hc : ∀ c ∈ s.cands, c = ⟨sqDist g.points[j]! q, j⟩ ∨ sqDist g.points[j]! q < c.sqDist) :
    (weigh g q 1 es s).found =
        [⟨sqDist g.points[es.foldl (nearer g q) j]! q, es.foldl (nearer g q) j⟩] ∧
      (∀ v ∈ (weigh g q 1 es s).visited,
        sqDist g.points[es.foldl (nearer g q) j]! q ≤ sqDist g.points[v]! q) ∧
      (∀ c ∈ (weigh g q 1 es s).cands,
        c = ⟨sqDist g.points[es.foldl (nearer g q) j]! q, es.foldl (nearer g q) j⟩ ∨
          sqDist g.points[es.foldl (nearer g q) j]! q < c.sqDist) ∧
      ((es.foldl (nearer g q) j = j ∧ (weigh g q 1 es s).cands = s.cands) ∨
        (⟨sqDist g.points[es.foldl (nearer g q) j]! q, es.foldl (nearer g q) j⟩ : Neighbor α) ∈
          (weigh g q 1 es s).cands) := by
  induction es generalizing j s with
  | nil => exact ⟨hf, hv, hc, Or.inl ⟨rfl, rfl⟩⟩
  | cons e es ih =>
    by_cases hev : e ∈ s.visited
    · have hn : nearer g q j e = j := by
        simp only [nearer, not_lt.mpr (hv e hev), ite_false]
      simp only [weigh, hev, ite_true, List.foldl_cons, hn]
      exact ih j s hf hv hc
    · by_cases hlt : sqDist g.points[e]! q < sqDist g.points[j]! q
      · have hn : nearer g q j e = e := by simp only [nearer, hlt, ite_true]
        have hb : ByDistance (⟨sqDist g.points[e]! q, e⟩ : Neighbor α)
            ⟨sqDist g.points[j]! q, j⟩ := Or.inl hlt
        have hins : [(⟨sqDist g.points[j]! q, j⟩ : Neighbor α)].orderedInsert ByDistance
            ⟨sqDist g.points[e]! q, e⟩ =
              [⟨sqDist g.points[e]! q, e⟩, ⟨sqDist g.points[j]! q, j⟩] := by
          rw [List.orderedInsert_cons]; simp only [hb, ite_true]
        have hdrop : ∀ x y : Neighbor α,
            (if 1 < [x, y].length then [x, y].dropLast else [x, y]) = [x] := by
          intro x y; simp
        simp only [weigh, hev, ite_false, hf, nearerThanFarthest, List.getLast?_singleton, hlt,
          decide_true, Bool.true_or, ite_true, hins, hdrop, List.foldl_cons, hn]
        obtain ⟨h1, h2, h3, h4⟩ := ih e
          ⟨s.cands.orderedInsert ByDistance ⟨sqDist g.points[e]! q, e⟩,
            [⟨sqDist g.points[e]! q, e⟩], e :: s.visited⟩ (by simp) (by
            intro v hv'
            rcases List.mem_cons.mp hv' with rfl | hv'
            · exact le_rfl
            · exact hlt.le.trans (hv v hv')) (by
            intro c hc'
            rcases List.mem_cons.mp ((List.perm_orderedInsert _ _ _).subset hc') with rfl | hc'
            · exact Or.inl rfl
            · rcases hc c hc' with rfl | h
              · exact Or.inr hlt
              · exact Or.inr (hlt.trans h))
        refine ⟨by simpa using h1, h2, h3, Or.inr ?_⟩
        rcases h4 with ⟨he, hcs⟩ | h
        · rw [hcs, he]
          exact (List.perm_orderedInsert _ _ _).symm.subset List.mem_cons_self
        · exact h
      · have hn : nearer g q j e = j := by simp only [nearer, hlt, ite_false]
        simp only [weigh, hev, ite_false, hf, nearerThanFarthest, List.getLast?_singleton, hlt,
          decide_false, List.length_singleton, Nat.lt_irrefl, Bool.false_or, Bool.false_eq_true,
          List.foldl_cons, hn]
        exact ih j _ rfl (by
          intro v hv'
          rcases List.mem_cons.mp hv' with rfl | hv'
          · exact not_lt.mp hlt
          · exact hv v hv') hc

/-- The layer search's loop at width 1, from a beam holding just node `i`, with every visited node
no nearer than `i`, the candidates nearest first and each `i` itself or strictly farther, and `i`
a fixed point of the greedy step unless it is still a candidate: the beam it ends with holds just
the node the greedy steps from `i` reach, a fixed point of the step. -/
theorem expand_one (g : HNSW d α) (q : Point d α) (l : ℕ) (s : LayerState α) (i : ℕ)
    (hf : s.found = [⟨sqDist g.points[i]! q, i⟩])
    (hv : ∀ v ∈ s.visited, sqDist g.points[i]! q ≤ sqDist g.points[v]! q)
    (hc : ∀ c ∈ s.cands, c = ⟨sqDist g.points[i]! q, i⟩ ∨ sqDist g.points[i]! q < c.sqDist)
    (hs : s.cands.Pairwise ByDistance)
    (hfix : (⟨sqDist g.points[i]! q, i⟩ : Neighbor α) ∉ s.cands → greedyNode g q l i = i) :
    ∃ n, expand g q 1 l s =
        [⟨sqDist g.points[(greedyNode g q l)^[n] i]! q, (greedyNode g q l)^[n] i⟩] ∧
      greedyNode g q l ((greedyNode g q l)^[n] i) = (greedyNode g q l)^[n] i := by
  fun_induction expand g q 1 l s generalizing i with
  | case1 s hcs =>
    exact ⟨0, hf, hfix (by simp [hcs])⟩
  | case2 s c cs hcs hfar =>
    refine ⟨0, hf, hfix ?_⟩
    simp only [hf, fartherThanFarthest, List.getLast?_singleton, decide_eq_true_eq] at hfar
    rw [hcs]
    intro hm
    rcases List.mem_cons.mp hm with h | h
    · rw [← h] at hfar; exact lt_irrefl _ hfar
    · rw [hcs] at hs
      rcases List.rel_of_pairwise_cons hs h with h' | ⟨h', _⟩
      · exact lt_asymm h' hfar
      · rw [h'] at hfar; exact lt_irrefl _ hfar
  | case3 s c cs hcs hnear ih =>
    simp only [hf, fartherThanFarthest, List.getLast?_singleton, decide_eq_true_eq,
      not_lt] at hnear
    have hci : c = ⟨sqDist g.points[i]! q, i⟩ := by
      rcases hc c (by rw [hcs]; exact List.mem_cons_self) with h | h
      · exact h
      · exact absurd hnear (not_le.mpr h)
    subst hci
    rw [hcs] at hs hc
    obtain ⟨h1, h2, h3, h4⟩ := weigh_one g q (g.neighbors i l) i ⟨cs, s.found, s.visited⟩ hf hv
      (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
    have hsort := (sorted_weigh g q 1 (g.neighbors i l) ⟨cs, s.found, s.visited⟩ hs.of_cons
      (by rw [hf]; exact List.pairwise_singleton _ _)).1
    obtain ⟨n, hn, hfx⟩ := ih (greedyNode g q l i) h1 h2 h3 hsort (by
      intro hm
      rcases h4 with ⟨he, _⟩ | h
      · change greedyNode g q l i = i at he
        rw [he]; exact he
      · exact absurd h hm)
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Function.iterate_succ_apply]; exact hn
    · rw [Function.iterate_succ_apply]; exact hfx

/-- **SEARCH-LAYER at width 1 is the greedy walk.** From a start `ep` carrying its own squared
distance, the layer search on layer `l` with a beam of one ends with the beam holding just the
node that repeated greedy steps from `ep` reach (`greedyNode`, which moves as `greedyStep` does:
`points_greedyNode`), with its squared distance, and that node is a fixed point of the step: it
is the first fixed point the steps from `ep` reach. Ties as the walk breaks them: a step moves
only to a strictly nearer node, the first in list order among the nearest. -/
theorem searchLayer_one (g : HNSW d α) (q : Point d α) (ep : Neighbor α) (l : ℕ)
    (hep : ep.sqDist = sqDist g.points[ep.id]! q) :
    ∃ n, searchLayer g q ep 1 l =
        [⟨sqDist g.points[(greedyNode g q l)^[n] ep.id]! q, (greedyNode g q l)^[n] ep.id⟩] ∧
      greedyNode g q l ((greedyNode g q l)^[n] ep.id) = (greedyNode g q l)^[n] ep.id := by
  obtain ⟨x, i⟩ := ep
  simp only at hep
  subst hep
  apply expand_one
  · simp
  · simp
  · simp
  · exact List.pairwise_singleton _ _
  · simp

/-- The greedy descent's first layer is the greedy walk on it: from a start carrying its own
squared distance, the descent through `l :: ls` goes on through `ls` from the first fixed point
the greedy steps on layer `l` reach. -/
theorem descend_cons (g : HNSW d α) (q : Point d α) (ep : Neighbor α) (l : ℕ) (ls : List ℕ)
    (hep : ep.sqDist = sqDist g.points[ep.id]! q) :
    ∃ n, descend g q ep (l :: ls) = descend g q
        ⟨sqDist g.points[(greedyNode g q l)^[n] ep.id]! q, (greedyNode g q l)^[n] ep.id⟩ ls ∧
      greedyNode g q l ((greedyNode g q l)^[n] ep.id) = (greedyNode g q l)^[n] ep.id := by
  obtain ⟨n, hn, hfx⟩ := searchLayer_one g q ep l hep
  exact ⟨n, by simp [descend, hn], hfx⟩

end HNSW

end AlgoDesign.Geometry
