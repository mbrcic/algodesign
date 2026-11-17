/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Select
public import AlgoDesign.Geometry.GraphIndex.Finish

/-!
# The graph index: insertion keeps `Valid` and `WellFormed`

Malkov–Yashunin Alg. 1 as the Rust runs it. A new point arrives as node `n` (the next id) with
its top layer and, for each layer it shares with the graph, the candidates the layer search found.
On each such layer it picks its list from the candidates, nearest first, by the picking rule at
cap `m`; each picked neighbor gets a back-link to `n`, and a list that goes over its cap (`m0` on
layer 0, `m` above) is re-picked by the same rule from its own entries, nearest first. The entry
moves to `n` when `n` reaches above the old top. The graph carries its points, so every node the
insertion measures is a stored point, the new one included.

Insertion takes its candidates as an input. Proved here: for any candidates
that are stored nodes on their layer, insertion keeps `Valid` and `WellFormed` (`valid_insert`), so
every graph built by insertions from an empty one is `Valid` and `WellFormed` (`valid_build`,
`wellFormed_build`), at caps with `m ≤ m0`; and it
stores the new point after the old ones (`points_insert`). On every layer it is given
candidates for, the new node's list is what the picking rule keeps of them (`picks_insert`). The
picking is the rule of `Select.lean` on ids (`selectIds_map`). Rust: `Hnsw::insert`.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace HNSW

variable {d : ℕ} {α : Type}

section Picking

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ## The picking rule on ids -/

/-- `selectNeighbors` on node ids, read in `pts`. -/
def selectIds (pts : List (Point d α)) (M : ℕ) (base : Point d α) :
    List ℕ → List ℕ → List ℕ
  | kept, [] => kept
  | kept, c :: cs =>
      if kept.length < M ∧
          kept.all (fun k => decide (sqDist base pts[c]! ≤ sqDist pts[k]! pts[c]!)) then
        selectIds pts M base (kept ++ [c]) cs
      else selectIds pts M base kept cs

omit [IsStrictOrderedRing α] in
/-- On ids, the rule picks the points `selectNeighbors` picks. -/
theorem selectIds_map (pts : List (Point d α)) (M : ℕ) (base : Point d α) (kept cs : List ℕ) :
    (selectIds pts M base kept cs).map (pts[·]!) =
      selectNeighbors M base (kept.map (pts[·]!)) (cs.map (pts[·]!)) := by
  induction cs generalizing kept with
  | nil => rfl
  | cons c cs ih =>
    simp only [selectIds, List.map_cons, selectNeighbors, List.length_map, List.all_map]
    split_ifs with h1 h2 h2
    · rw [ih]; simp
    · exact absurd h1 (by simpa [Function.comp_def] using h2)
    · exact absurd h2 (by simpa [Function.comp_def] using h1)
    · exact ih kept

omit [IsStrictOrderedRing α] in
theorem selectIds_length_le (pts : List (Point d α)) (M : ℕ) (base : Point d α)
    (kept cs : List ℕ) (h : kept.length ≤ M) : (selectIds pts M base kept cs).length ≤ M := by
  induction cs generalizing kept with
  | nil => exact h
  | cons c cs ih =>
    simp only [selectIds]
    split_ifs with hc
    · exact ih _ (by simp only [List.length_append, List.length_singleton]; omega)
    · exact ih _ h

omit [IsStrictOrderedRing α] in
theorem selectIds_sublist (pts : List (Point d α)) (M : ℕ) (base : Point d α)
    (kept cs : List ℕ) : (selectIds pts M base kept cs).Sublist (kept ++ cs) := by
  induction cs generalizing kept with
  | nil => simp [selectIds]
  | cons c cs ih =>
    simp only [selectIds]
    split_ifs with hc
    · simpa using ih (kept ++ [c])
    · exact (ih kept).trans (List.Sublist.append (List.Sublist.refl kept)
        (List.sublist_cons_self c cs))

/-- Nodes sorted nearest to `base` first, ties by node: the order the Rust's lists come in. -/
def sortByDist (pts : List (Point d α)) (base : Point d α) (cs : List ℕ) : List ℕ :=
  ((cs.map fun i => { sqDist := sqDist pts[i]! base, id := i }).insertionSort ByDistance).map
    Neighbor.id

omit [IsStrictOrderedRing α] in
theorem sortByDist_perm (pts : List (Point d α)) (base : Point d α) (cs : List ℕ) :
    (sortByDist pts base cs).Perm cs := by
  have := ((List.perm_insertionSort ByDistance
    (cs.map fun i => (⟨sqDist pts[i]! base, i⟩ : Neighbor α))).map Neighbor.id)
  simpa [sortByDist, Function.comp_def] using this

/-- What a picking from `cs` for the point `base` at cap `c` keeps: the rule over the candidates
nearest first. -/
def pick (pts : List (Point d α)) (c : ℕ) (base : Point d α) (cs : List ℕ) : List ℕ :=
  selectIds pts c base [] (sortByDist pts base cs)

omit [IsStrictOrderedRing α] in
theorem pick_length_le (pts : List (Point d α)) (c : ℕ) (base : Point d α) (cs : List ℕ) :
    (pick pts c base cs).length ≤ c :=
  selectIds_length_le pts c base [] _ (by simp)

omit [IsStrictOrderedRing α] in
theorem pick_subperm (pts : List (Point d α)) (c : ℕ) (base : Point d α) (cs : List ℕ) :
    (pick pts c base cs).Subperm cs := by
  have h := selectIds_sublist pts c base [] (sortByDist pts base cs)
  rw [List.nil_append] at h
  exact List.Subperm.trans h.subperm (sortByDist_perm pts base cs).subperm

omit [IsStrictOrderedRing α] in
theorem pick_nodup {pts : List (Point d α)} {c : ℕ} {base : Point d α} {cs : List ℕ}
    (h : cs.Nodup) : (pick pts c base cs).Nodup := by
  obtain ⟨l, hp, hs⟩ := pick_subperm pts c base cs
  exact hp.nodup_iff.mp (hs.nodup h)

omit [IsStrictOrderedRing α] in
theorem mem_of_mem_pick {pts : List (Point d α)} {c : ℕ} {base : Point d α} {cs : List ℕ}
    {x : ℕ} (h : x ∈ pick pts c base cs) : x ∈ cs :=
  List.Subperm.subset (pick_subperm pts c base cs) h
end Picking

/-! ## Writing one list -/

/-- The graph with node `v`'s list on layer `l` replaced by `ns` (no change off the graph). -/
def setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) : HNSW d α :=
  { g with links := g.links.modify v (fun node => node.modify l (fun _ => ns)) }

@[simp] theorem m_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) : (g.setList v l ns).m = g.m := rfl

@[simp] theorem m0_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) : (g.setList v l ns).m0 = g.m0 :=
  rfl

@[simp] theorem size_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) :
    (g.setList v l ns).size = g.size := by
  simp [setList, size]

@[simp] theorem points_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) :
    (g.setList v l ns).points = g.points := rfl

@[simp] theorem entry_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) :
    (g.setList v l ns).entry = g.entry := rfl

@[simp] theorem layers_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) (u : ℕ) :
    (g.setList v l ns).layers u = g.layers u := by
  simp only [layers, setList, List.getD_eq_getElem?_getD, List.getElem?_modify]
  cases g.links[u]? <;> simp only [Option.map_eq_map, Option.map_none, Option.map_some,
    Option.getD_none, Option.getD_some]
  split_ifs <;> simp

theorem neighbors_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) (u k : ℕ) :
    (g.setList v l ns).neighbors u k =
      if u = v ∧ k = l ∧ g.OnLayer v l then ns else g.neighbors u k := by
  simp only [neighbors, setList, OnLayer, layers, size, List.getD_eq_getElem?_getD,
    List.getElem?_modify]
  rcases h : g.links[u]? with _ | node
  · have hu : g.links.length ≤ u := List.getElem?_eq_none_iff.mp h
    simp only [Option.map_eq_map, Option.map_none, Option.getD_none, List.getElem?_nil]
    split_ifs with hc
    · obtain ⟨rfl, -, hv, -⟩ := hc; omega
    · rfl
  · have hu : u < g.links.length := (List.getElem?_eq_some_iff.mp h).1
    simp only [Option.map_eq_map, Option.map_some, Option.getD_some]
    by_cases hv : v = u
    · subst hv
      simp only [ite_true, List.getElem?_modify, h, Option.getD_some]
      rcases hk : node[k]? with _ | x
      · have : node.length ≤ k := List.getElem?_eq_none_iff.mp hk
        simp only [Option.map_eq_map, Option.map_none, Option.getD_none]
        split_ifs with hc
        · obtain ⟨-, rfl, -, hl⟩ := hc; omega
        · rfl
      · have hk' : k < node.length := (List.getElem?_eq_some_iff.mp hk).1
        simp only [Option.map_eq_map, Option.map_some, Option.getD_some]
        by_cases hl : l = k
        · subst hl; simp [hu, hk']
        · simp [hl, Ne.symm hl]
    · simp [hv, Ne.symm hv]

@[simp] theorem onLayer_setList (g : HNSW d α) (v l : ℕ) (ns : List ℕ) (u k : ℕ) :
    (g.setList v l ns).OnLayer u k ↔ g.OnLayer u k := by
  simp [OnLayer]

/-- Writing one list keeps `Valid` and `WellFormed` when the new list is within its cap, does not
name its own node or any node twice, and names only nodes on its layer. -/
theorem valid_setList {g : HNSW d α} {v l : ℕ} {ns : List ℕ} (hg : Valid g ∧ WellFormed g)
    (hv : g.OnLayer v l) (hlen : ns.length ≤ cap g.m g.m0 l) (hself : v ∉ ns) (hnd : ns.Nodup)
    (hon : ∀ u ∈ ns, g.OnLayer u l) :
    Valid (g.setList v l ns) ∧ WellFormed (g.setList v l ns) := by
  obtain ⟨⟨hD, ⟨h0, hL⟩⟩, hS, hR, hE, hP⟩ := hg
  refine ⟨⟨?_, ⟨?_, ?_⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro u hu k hk
    simp only [size_setList, layers_setList] at hu hk
    rw [neighbors_setList]
    split_ifs with h
    · obtain ⟨-, rfl, -⟩ := h; exact hlen
    · exact hD u hu k hk
  · intro u hu
    simpa using h0 u (by simpa using hu)
  · intro u hu k hk w hw
    simp only [size_setList, layers_setList] at hu hk
    rw [neighbors_setList] at hw
    rw [onLayer_setList]
    split_ifs at hw with h
    · obtain ⟨-, rfl, -⟩ := h; exact hon w hw
    · exact hL u hu k hk w hw
  · intro u hu k hk
    simp only [size_setList, layers_setList] at hu hk
    rw [neighbors_setList]
    split_ifs with h
    · obtain ⟨rfl, rfl, -⟩ := h; exact hself
    · exact hS u hu k hk
  · intro u hu k hk
    simp only [size_setList, layers_setList] at hu hk
    rw [neighbors_setList]
    split_ifs with h
    · exact hnd
    · exact hR u hu k hk
  · unfold EntryOnTop at hE ⊢
    simpa only [entry_setList, size_setList, layers_setList] using hE
  · unfold OneNodePerPoint at hP ⊢
    simpa only [points_setList, size_setList] using hP

/-! ## A new node -/

/-- The graph with the point `p` added as node `g.size`, on layers `0, …, top`, its lists empty;
the entry moves to it when it reaches above the old top (or the graph was empty). -/
def addNode (g : HNSW d α) (p : Point d α) (top : ℕ) : HNSW d α :=
  { g with
    points := g.points ++ [p]
    links := g.links ++ [List.replicate (top + 1) []]
    entry := match g.entry with
      | none => some g.size
      | some e => if g.layers e < top + 1 then some g.size else some e }

@[simp] theorem m_addNode (g : HNSW d α) (p : Point d α) (top : ℕ) :
    (g.addNode p top).m = g.m := rfl

@[simp] theorem m0_addNode (g : HNSW d α) (p : Point d α) (top : ℕ) :
    (g.addNode p top).m0 = g.m0 := rfl

@[simp] theorem points_addNode (g : HNSW d α) (p : Point d α) (top : ℕ) :
    (g.addNode p top).points = g.points ++ [p] := rfl

@[simp] theorem size_addNode (g : HNSW d α) (p : Point d α) (top : ℕ) :
    (g.addNode p top).size = g.size + 1 := by
  simp [addNode, size]

theorem getElem?_links_addNode (g : HNSW d α) (p : Point d α) (top u : ℕ) :
    (g.addNode p top).links[u]? =
      if u < g.size then g.links[u]? else if u = g.size then some (List.replicate (top + 1) [])
      else none := by
  change (g.links ++ [List.replicate (top + 1) []])[u]? = _
  unfold size
  by_cases h1 : u < g.links.length
  · rw [ite_eq_left h1]; exact List.getElem?_append_left h1
  · rw [ite_eq_right h1]
    by_cases h2 : u = g.links.length
    · subst h2; rw [ite_eq_left rfl, List.getElem?_append_right le_rfl]; simp
    · rw [ite_eq_right h2, List.getElem?_append_right (by omega)]
      exact List.getElem?_eq_none (by simp; omega)

theorem layers_addNode (g : HNSW d α) (p : Point d α) (top u : ℕ) :
    (g.addNode p top).layers u =
      if u < g.size then g.layers u else if u = g.size then top + 1 else 0 := by
  simp only [layers, List.getD_eq_getElem?_getD, getElem?_links_addNode]
  split_ifs <;> simp

theorem neighbors_addNode (g : HNSW d α) (p : Point d α) (top u k : ℕ) :
    (g.addNode p top).neighbors u k = if u < g.size then g.neighbors u k else [] := by
  simp only [neighbors, List.getD_eq_getElem?_getD, getElem?_links_addNode]
  split_ifs <;> simp [List.getElem?_replicate]
  split_ifs <;> rfl

theorem entry_addNode (g : HNSW d α) (p : Point d α) (top : ℕ) :
    (g.addNode p top).entry = match g.entry with
      | none => some g.size
      | some e => if g.layers e < top + 1 then some g.size else some e := rfl

/-- Adding a node keeps `Valid` and `WellFormed`. -/
theorem valid_addNode {g : HNSW d α} (hg : Valid g ∧ WellFormed g) (p : Point d α) (top : ℕ) :
    Valid (g.addNode p top) ∧ WellFormed (g.addNode p top) := by
  obtain ⟨⟨hD, ⟨h0, hL⟩⟩, hS, hR, hE, hP⟩ := hg
  have hlay := layers_addNode g p top
  have hnb := neighbors_addNode g p top
  refine ⟨⟨?_, ⟨?_, ?_⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro u hu k hk
    rw [hnb]; rw [hlay] at hk
    by_cases h : u < g.size
    · rw [ite_eq_left h] at hk ⊢; exact hD u h k hk
    · rw [ite_eq_right h]; simp
  · intro u hu
    rw [hlay]; rw [size_addNode] at hu
    by_cases h : u < g.size
    · rw [ite_eq_left h]; exact h0 u h
    · rw [ite_eq_right h, ite_eq_left (by omega)]; omega
  · intro u hu k hk w hw
    rw [hnb] at hw; rw [hlay] at hk
    by_cases h : u < g.size
    · rw [ite_eq_left h] at hk hw
      obtain ⟨hw1, hw2⟩ := hL u h k hk w hw
      refine ⟨by rw [size_addNode]; omega, ?_⟩
      rw [hlay, ite_eq_left hw1]; exact hw2
    · rw [ite_eq_right h] at hw; simp at hw
  · intro u hu k hk
    rw [hnb]
    by_cases h : u < g.size
    · rw [ite_eq_left h]; rw [hlay, ite_eq_left h] at hk; exact hS u h k hk
    · rw [ite_eq_right h]; simp
  · intro u hu k hk
    rw [hnb]
    by_cases h : u < g.size
    · rw [ite_eq_left h]; rw [hlay, ite_eq_left h] at hk; exact hR u h k hk
    · rw [ite_eq_right h]; simp
  · unfold EntryOnTop at hE ⊢
    rw [entry_addNode]
    rcases he : g.entry with _ | e
    · rw [he] at hE
      simp only [size_addNode]
      refine ⟨by omega, fun v hv => ?_⟩
      rw [hlay, hlay]
      have : v = g.size := by omega
      simp [this]
    · rw [he] at hE
      obtain ⟨he1, he2⟩ := hE
      by_cases hlt : g.layers e < top + 1
      · simp only [ite_eq_left hlt, size_addNode]
        refine ⟨by omega, fun v hv => ?_⟩
        rw [hlay, hlay, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
        by_cases h1 : v < g.size
        · rw [ite_eq_left h1]; exact (he2 v h1).trans hlt.le
        · rw [ite_eq_right h1, ite_eq_left (by omega)]
      · simp only [ite_eq_right hlt, size_addNode]
        refine ⟨by omega, fun v hv => ?_⟩
        rw [hlay, hlay, ite_eq_left he1]
        by_cases h1 : v < g.size
        · rw [ite_eq_left h1]; exact he2 v h1
        · rw [ite_eq_right h1, ite_eq_left (by omega)]; omega
  · unfold OneNodePerPoint at hP ⊢
    simp only [points_addNode, size_addNode, List.length_append, List.length_singleton, hP]

/-- The new node is in no list of the grown graph: every old link names an old node. -/
theorem fresh_addNode {g : HNSW d α} (hg : Valid g) (p : Point d α) (top u k : ℕ) :
    g.size ∉ (g.addNode p top).neighbors u k := by
  rw [neighbors_addNode]
  split_ifs with h
  · intro hm
    by_cases hk : k < g.layers u
    · have := (hg.2.2 u h k hk _ hm).1; omega
    · simp only [neighbors, layers] at hm hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hm
      simp at hm
  · simp

variable [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]

/-! ## Back-links and the layers -/

/-- `e`'s back-link to the new node `n` on layer `l`: `n` joins `e`'s list, and a list over its
cap is re-picked from its own entries, nearest `e` first. -/
def backlink (pts : List (Point d α)) (n l : ℕ) (g : HNSW d α) (e : ℕ) : HNSW d α :=
  let ns := g.neighbors e l ++ [n]
  g.setList e l
    (if cap g.m g.m0 l < ns.length then pick pts (cap g.m g.m0 l) pts[e]! ns else ns)

/-- One layer of the insertion: the new node `n`, at the point `base`, picks its list from the
candidates `cs` at cap `m`, and each pick gets its back-link, in the order picked. -/
def insertLevel (pts : List (Point d α)) (n : ℕ) (base : Point d α) (g : HNSW d α) (l : ℕ)
    (cs : List ℕ) : HNSW d α :=
  (pick pts g.m base cs).foldl (backlink pts n l) (g.setList n l (pick pts g.m base cs))

/-- **Insertion** (Alg. 1), at the graph's caps: the point `p` arrives as node `g.size` on layers
`0, …, top`; `cands` gives, per layer it shares with the graph, the candidates the layer search
found. Every distance it measures is between stored points, the new one included. -/
def insert (g : HNSW d α) (p : Point d α) (top : ℕ) (cands : List Candidates) : HNSW d α :=
  cands.foldl (fun h c => insertLevel (g.addNode p top).points g.size p h c.layer c.nodes)
    (g.addNode p top)

omit [IsStrictOrderedRing α] in
theorem frame_backlink (pts : List (Point d α)) (n l : ℕ) (g : HNSW d α) (e u k : ℕ)
    (h : ¬(u = e ∧ k = l)) : (backlink pts n l g e).neighbors u k = g.neighbors u k := by
  simp only [backlink, neighbors_setList]
  rw [ite_eq_right (fun hc => h ⟨hc.1, hc.2.1⟩)]

omit [IsStrictOrderedRing α] in
theorem valid_backlink {pts : List (Point d α)} {n l : ℕ} {g : HNSW d α} {e : ℕ}
    (hg : Valid g ∧ WellFormed g) (hn : g.OnLayer n l) (he : g.OnLayer e l) (hen : e ≠ n)
    (hfresh : n ∉ g.neighbors e l) :
    Valid (backlink pts n l g e) ∧ WellFormed (backlink pts n l g e) := by
  have hR := hg.2.2.1 e he.1 l he.2
  have hS := hg.2.1 e he.1 l he.2
  have hL := hg.1.2.2 e he.1 l he.2
  have hnd : (g.neighbors e l ++ [n]).Nodup :=
    List.nodup_append.mpr ⟨hR, List.nodup_singleton n, fun x hx y hy => by
      rw [List.mem_singleton.mp hy]; rintro rfl; exact hfresh hx⟩
  have hon : ∀ u ∈ g.neighbors e l ++ [n], g.OnLayer u l := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hL u hu
    · rw [List.mem_singleton.mp hu]; exact hn
  have hself : e ∉ g.neighbors e l ++ [n] := by
    simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hS, hen⟩
  dsimp only [backlink]
  split_ifs with hc
  · exact valid_setList hg he (pick_length_le _ _ _ _) (fun h => hself (mem_of_mem_pick h))
      (pick_nodup hnd) (fun u hu => hon u (mem_of_mem_pick hu))
  · exact valid_setList hg he (by omega) hself hnd hon

omit [IsStrictOrderedRing α] in
theorem valid_backlinks {pts : List (Point d α)} {n l : ℕ} (es : List ℕ) :
    ∀ {g : HNSW d α}, Valid g ∧ WellFormed g → g.OnLayer n l → es.Nodup →
      (∀ e ∈ es, g.OnLayer e l ∧ e ≠ n ∧ n ∉ g.neighbors e l) →
      Valid (es.foldl (backlink pts n l) g) ∧ WellFormed (es.foldl (backlink pts n l) g) := by
  induction es with
  | nil => intro g hg _ _ _; exact hg
  | cons e es ih =>
    intro g hg hn hnd hes
    obtain ⟨he, hen, hfresh⟩ := hes e (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.mp hnd
    refine ih (valid_backlink hg hn he hen hfresh) ?_ hnd'.2 ?_
    · simpa [backlink] using hn
    · intro e' he'
      obtain ⟨h1, h2, h3⟩ := hes e' (List.mem_cons_of_mem _ he')
      have hne : e' ≠ e := fun h => hnd'.1 (h ▸ he')
      refine ⟨by simpa [backlink] using h1, h2, ?_⟩
      rw [frame_backlink _ _ _ _ _ _ _ (fun h => hne h.1)]; exact h3

omit [IsStrictOrderedRing α] in
theorem frame_backlinks (pts : List (Point d α)) (n l : ℕ) (es : List ℕ) (u k : ℕ)
    (hk : k ≠ l) :
    ∀ g : HNSW d α, (es.foldl (backlink pts n l) g).neighbors u k = g.neighbors u k := by
  induction es with
  | nil => intro g; rfl
  | cons e es ih =>
    intro g
    rw [List.foldl_cons, ih, frame_backlink _ _ _ _ _ _ _ (fun h => hk h.2)]

omit [IsStrictOrderedRing α] in
theorem layers_backlinks (pts : List (Point d α)) (n l : ℕ) (es : List ℕ) (u : ℕ) :
    ∀ g : HNSW d α, (es.foldl (backlink pts n l) g).layers u = g.layers u ∧
      (es.foldl (backlink pts n l) g).size = g.size := by
  induction es with
  | nil => intro g; exact ⟨rfl, rfl⟩
  | cons e es ih =>
    intro g
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (backlink pts n l g e)
    simp only [backlink, layers_setList, size_setList] at h1 h2
    exact ⟨h1, h2⟩

omit [IsStrictOrderedRing α] in
/-- Back-links keep the graph's caps. -/
theorem caps_backlinks (pts : List (Point d α)) (n l : ℕ) (es : List ℕ) :
    ∀ g : HNSW d α, (es.foldl (backlink pts n l) g).m = g.m ∧
      (es.foldl (backlink pts n l) g).m0 = g.m0 := by
  induction es with
  | nil => intro g; exact ⟨rfl, rfl⟩
  | cons e es ih =>
    intro g
    rw [List.foldl_cons]
    exact ih (backlink pts n l g e)

theorem le_cap {m m0 : ℕ} (hm : m ≤ m0) (l : ℕ) : m ≤ cap m m0 l := by
  unfold cap; split_ifs <;> omega

omit [IsStrictOrderedRing α] in
theorem valid_insertLevel {pts : List (Point d α)} {n l : ℕ} {base : Point d α} {g : HNSW d α}
    {cs : List ℕ}
    (hg : Valid g ∧ WellFormed g) (hm : g.m ≤ g.m0) (hn : g.OnLayer n l) (hnd : cs.Nodup)
    (hcs : ∀ u ∈ cs, g.OnLayer u l ∧ u ≠ n) (hfresh : ∀ u, n ∉ g.neighbors u l) :
    Valid (insertLevel pts n base g l cs) ∧ WellFormed (insertLevel pts n base g l cs) := by
  have hpick : ∀ u ∈ pick pts g.m base cs, g.OnLayer u l ∧ u ≠ n :=
    fun u hu => hcs u (mem_of_mem_pick hu)
  have h1 : Valid (g.setList n l (pick pts g.m base cs)) ∧
      WellFormed (g.setList n l (pick pts g.m base cs)) :=
    valid_setList hg hn ((pick_length_le _ _ _ _).trans (le_cap hm l))
      (fun h => (hpick n h).2 rfl) (pick_nodup hnd) (fun u hu => (hpick u hu).1)
  refine valid_backlinks _ h1 (by simpa using hn) (pick_nodup hnd) (fun e he => ?_)
  obtain ⟨he1, he2⟩ := hpick e he
  refine ⟨by simpa using he1, he2, ?_⟩
  rw [neighbors_setList, ite_eq_right (fun h => he2 h.1)]
  exact hfresh e

omit [IsStrictOrderedRing α] in
theorem frame_insertLevel (pts : List (Point d α)) (n : ℕ) (base : Point d α) (g : HNSW d α) (l : ℕ)
    (cs : List ℕ) (u k : ℕ) (hk : k ≠ l) :
    (insertLevel pts n base g l cs).neighbors u k = g.neighbors u k := by
  unfold insertLevel
  rw [frame_backlinks _ _ _ _ _ _ hk, neighbors_setList, ite_eq_right (fun h => hk h.2.1)]

omit [IsStrictOrderedRing α] in
theorem layers_insertLevel (pts : List (Point d α)) (n : ℕ) (base : Point d α) (g : HNSW d α)
    (l : ℕ) (cs : List ℕ) (u : ℕ) :
    (insertLevel pts n base g l cs).layers u = g.layers u ∧
      (insertLevel pts n base g l cs).size = g.size := by
  unfold insertLevel
  obtain ⟨h1, h2⟩ := layers_backlinks pts n l (pick pts g.m base cs) u
    (g.setList n l (pick pts g.m base cs))
  simp only [layers_setList, size_setList] at h1 h2
  exact ⟨h1, h2⟩

omit [IsStrictOrderedRing α] in
/-- One layer of the insertion keeps the graph's caps. -/
theorem caps_insertLevel (pts : List (Point d α)) (n : ℕ) (base : Point d α) (g : HNSW d α) (l : ℕ)
    (cs : List ℕ) :
    (insertLevel pts n base g l cs).m = g.m ∧ (insertLevel pts n base g l cs).m0 = g.m0 :=
  caps_backlinks pts n l _ _

omit [IsStrictOrderedRing α] in
theorem valid_insertLevels {pts : List (Point d α)} {n : ℕ} {base : Point d α}
    (cands : List Candidates) :
    ∀ {g : HNSW d α}, Valid g ∧ WellFormed g → g.m ≤ g.m0 → (cands.map Candidates.layer).Nodup →
      (∀ c ∈ cands, g.OnLayer n c.layer ∧ c.nodes.Nodup ∧
        (∀ u ∈ c.nodes, g.OnLayer u c.layer ∧ u ≠ n) ∧ ∀ u, n ∉ g.neighbors u c.layer) →
      Valid (cands.foldl (fun h c => insertLevel pts n base h c.layer c.nodes) g) ∧
        WellFormed (cands.foldl (fun h c => insertLevel pts n base h c.layer c.nodes) g) := by
  induction cands with
  | nil => intro g hg _ _ _; exact hg
  | cons c cands ih =>
    intro g hg hm hnd hc
    obtain ⟨hn, hcnd, hcs, hfr⟩ := hc c (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    have hon : ∀ u k, (insertLevel pts n base g c.layer c.nodes).OnLayer u k ↔ g.OnLayer u k := by
      intro u k
      simp only [OnLayer, (layers_insertLevel pts n base g c.layer c.nodes u).1,
        (layers_insertLevel pts n base g c.layer c.nodes u).2]
    have hcaps := caps_insertLevel pts n base g c.layer c.nodes
    refine ih (valid_insertLevel hg hm hn hcnd hcs hfr) (by rw [hcaps.1, hcaps.2]; exact hm)
      hnd.2 (fun c' hc' => ?_)
    obtain ⟨h1, h2, h3, h4⟩ := hc c' (List.mem_cons_of_mem _ hc')
    have hne : c'.layer ≠ c.layer := fun h => hnd.1 (h ▸ List.mem_map_of_mem hc')
    refine ⟨(hon _ _).mpr h1, h2, fun u hu => ⟨(hon _ _).mpr (h3 u hu).1, (h3 u hu).2⟩,
      fun u => ?_⟩
    rw [frame_insertLevel _ _ _ _ _ _ _ _ hne]; exact h4 u

omit [IsStrictOrderedRing α] in
/-- **Insertion keeps `Valid` and `WellFormed`**: for any candidates the layer search returns
that are stored nodes on their layer (`CandidatesOk`), at caps with `m ≤ m0`. -/
theorem valid_insert {g : HNSW d α} {p : Point d α} {top : ℕ} {cands : List Candidates}
    (hm : g.m ≤ g.m0) (hg : Valid g) (hw : WellFormed g) (hc : CandidatesOk g top cands) :
    Valid (insert g p top cands) ∧ WellFormed (insert g p top cands) := by
  obtain ⟨hnd, hcs⟩ := hc
  have hlay := layers_addNode g p top
  refine valid_insertLevels cands (valid_addNode ⟨hg, hw⟩ p top) hm hnd (fun c hcm => ?_)
  obtain ⟨htop, hcnd, hon⟩ := hcs c hcm
  refine ⟨⟨by simp, ?_⟩, hcnd, fun u hu => ?_, fun u => fresh_addNode hg p top u c.layer⟩
  · rw [hlay, ite_eq_right (lt_irrefl _), ite_eq_left rfl]; omega
  · obtain ⟨hu1, hu2⟩ := hon u hu
    refine ⟨⟨by simp; omega, ?_⟩, by omega⟩
    rw [hlay, ite_eq_left hu1]; exact hu2

omit [IsStrictOrderedRing α] in
/-- One layer of the insertion keeps the stored points. -/
theorem points_insertLevel (pts : List (Point d α)) (n : ℕ) (base : Point d α) (g : HNSW d α)
    (l : ℕ) (cs : List ℕ) : (insertLevel pts n base g l cs).points = g.points := by
  unfold insertLevel
  suffices ∀ (es : List ℕ) (h : HNSW d α), (es.foldl (backlink pts n l) h).points = h.points from
    this _ _
  intro es
  induction es with
  | nil => intro h; rfl
  | cons e es ih => intro h; rw [List.foldl_cons, ih]; rfl

omit [IsStrictOrderedRing α] in
/-- Insertion keeps the graph's caps. -/
theorem caps_insert (g : HNSW d α) (p : Point d α) (top : ℕ) (cands : List Candidates) :
    (insert g p top cands).m = g.m ∧ (insert g p top cands).m0 = g.m0 := by
  unfold insert
  generalize (g.addNode p top).points = pts
  suffices ∀ (cs : List Candidates) (h : HNSW d α),
      (cs.foldl (fun h c => insertLevel pts g.size p h c.layer c.nodes) h).m = h.m ∧
        (cs.foldl (fun h c => insertLevel pts g.size p h c.layer c.nodes) h).m0 = h.m0 from
    this cands (g.addNode p top)
  intro cs
  induction cs with
  | nil => intro h; exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    intro h
    rw [List.foldl_cons, (ih _).1, (ih _).2]
    exact caps_insertLevel pts g.size p h c.layer c.nodes

omit [IsStrictOrderedRing α] in
/-- **Insertion stores the new point** after the old ones. -/
theorem points_insert (g : HNSW d α) (p : Point d α) (top : ℕ) (cands : List Candidates) :
    (insert g p top cands).points = g.points ++ [p] := by
  unfold insert
  generalize hpts : (g.addNode p top).points = pts
  suffices ∀ (cs : List Candidates) (h : HNSW d α),
      (cs.foldl (fun h c => insertLevel pts g.size p h c.layer c.nodes) h).points = h.points by
    rw [this, points_addNode]
  intro cs
  induction cs with
  | nil => intro h; rfl
  | cons c cs ih =>
    intro h
    rw [List.foldl_cons, ih, points_insertLevel]

/-! ## The new node's lists are pickings -/

omit [IsStrictOrderedRing α] in
/-- `sortByDist` puts the candidates nearest `base` first. -/
theorem sortByDist_sorted (pts : List (Point d α)) (base : Point d α) (cs : List ℕ) :
    ((sortByDist pts base cs).map (pts[·]!)).Pairwise
      (fun a b => sqDist base a ≤ sqDist base b) := by
  unfold sortByDist
  rw [List.map_map, List.pairwise_map]
  have hp := List.pairwise_insertionSort ByDistance
    (cs.map fun i => (⟨sqDist pts[i]! base, i⟩ : Neighbor α))
  refine hp.imp_of_mem (fun {a b} ha hb hab => ?_)
  rw [List.mem_insertionSort, List.mem_map] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  simp only [Function.comp_apply, sqDist_comm base]
  rcases hab with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

omit [IsStrictOrderedRing α] in
/-- Back-links to `n` never write `n`'s own lists. -/
theorem own_backlinks (pts : List (Point d α)) (n l : ℕ) (es : List ℕ) (k : ℕ)
    (hes : ∀ e ∈ es, e ≠ n) :
    ∀ g : HNSW d α, (es.foldl (backlink pts n l) g).neighbors n k = g.neighbors n k := by
  induction es with
  | nil => intro g; rfl
  | cons e es ih =>
    intro g
    rw [List.foldl_cons, ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he')),
      frame_backlink _ _ _ _ _ _ _ (fun h => hes e (List.mem_cons_self ..) h.1.symm)]

omit [IsStrictOrderedRing α] in
/-- One layer of the insertion leaves the new node's list on that layer as the picking from its
candidates. -/
theorem own_insertLevel (pts : List (Point d α)) (n : ℕ) (base : Point d α) (g : HNSW d α)
    (l : ℕ) (cs : List ℕ) (hn : g.OnLayer n l) (hcs : ∀ u ∈ cs, u ≠ n) :
    (insertLevel pts n base g l cs).neighbors n l = pick pts g.m base cs := by
  unfold insertLevel
  rw [own_backlinks _ _ _ _ _ (fun e he => hcs e (mem_of_mem_pick he)), neighbors_setList,
    ite_eq_left ⟨rfl, rfl, hn⟩]

omit [IsStrictOrderedRing α] in
/-- Over the layers, each new list is the picking from its layer's candidates at cap `m`: later
layers never write it. -/
theorem own_insertLevels (pts : List (Point d α)) (n : ℕ) (base : Point d α) (m : ℕ)
    (cands : List Candidates) :
    ∀ g : HNSW d α, g.m = m → (cands.map Candidates.layer).Nodup →
      (∀ c ∈ cands, g.OnLayer n c.layer ∧ ∀ u ∈ c.nodes, u ≠ n) →
      ∀ c ∈ cands, (cands.foldl (fun h c => insertLevel pts n base h c.layer c.nodes) g).neighbors
        n c.layer = pick pts m base c.nodes := by
  induction cands with
  | nil => intro g _ _ _ c hc; simp at hc
  | cons c0 cands ih =>
    intro g hm hnd hc c hcm
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    set g' := insertLevel pts n base g c0.layer c0.nodes
    have hm' : g'.m = m := (caps_insertLevel pts n base g c0.layer c0.nodes).1.trans hm
    have hon : ∀ u k, g'.OnLayer u k ↔ g.OnLayer u k := by
      intro u k
      simp only [g', OnLayer, (layers_insertLevel pts n base g c0.layer c0.nodes u).1,
        (layers_insertLevel pts n base g c0.layer c0.nodes u).2]
    rcases List.mem_cons.mp hcm with rfl | hcm
    · suffices hfr : ∀ (cs : List Candidates) (h : HNSW d α), c.layer ∉ cs.map Candidates.layer →
          (cs.foldl (fun h c => insertLevel pts n base h c.layer c.nodes) h).neighbors n c.layer =
            h.neighbors n c.layer by
        rw [hfr cands g' hnd.1, own_insertLevel _ _ _ _ _ _ (hc c (List.mem_cons_self ..)).1
          (hc c (List.mem_cons_self ..)).2, hm]
      intro cs
      induction cs with
      | nil => intro h _; rfl
      | cons c1 cs ih' =>
        intro h hnot
        rw [List.map_cons, List.mem_cons, not_or] at hnot
        rw [List.foldl_cons, ih' _ hnot.2, frame_insertLevel _ _ _ _ _ _ _ _ hnot.1]
    · refine ih g' hm' hnd.2 (fun c' hc' => ?_) c hcm
      obtain ⟨h1, h2⟩ := hc c' (List.mem_cons_of_mem _ hc')
      exact ⟨(hon _ _).mpr h1, h2⟩

omit [IsStrictOrderedRing α] in
/-- **Insertion picks by the rule** (box invariant 2 at insertion): on every layer it is given
candidates for, the new node's list is what the picking rule keeps of them, nearest first, at the
graph's cap `m`. -/
theorem picks_insert (g : HNSW d α) (p : Point d α) (top : ℕ) (cands : List Candidates)
    (hc : CandidatesOk g top cands) : ∀ c ∈ cands,
    ∃ cs : List (Point d α), cs.Perm (c.nodes.map ((g.points ++ [p])[·]!)) ∧
      PicksDiverse ⟨g.m, p, cs,
        ((insert g p top cands).neighbors g.size c.layer).map ((g.points ++ [p])[·]!)⟩ := by
  intro c hcm
  obtain ⟨hnd, hcs⟩ := hc
  have hlay := layers_addNode g p top
  have hown := own_insertLevels (g.addNode p top).points g.size p g.m cands (g.addNode p top) rfl
    hnd (fun c' hc' => by
      obtain ⟨htop, -, hon⟩ := hcs c' hc'
      refine ⟨⟨by simp, ?_⟩, fun u hu => ?_⟩
      · rw [hlay, ite_eq_right (lt_irrefl _), ite_eq_left rfl]; omega
      · have := (hon u hu).1; omega) c hcm
  unfold insert
  rw [hown, points_addNode]
  refine ⟨(sortByDist (g.points ++ [p]) p c.nodes).map ((g.points ++ [p])[·]!),
    (sortByDist_perm _ _ _).map _, ?_⟩
  unfold pick
  rw [selectIds_map, List.map_nil]
  exact picksDiverse_selectNeighbors _ _ _ (sortByDist_sorted _ _ _)

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
/-- The graph with no nodes is valid and well formed, at any caps. -/
theorem valid_wellFormed_empty (m m0 : ℕ) :
    Valid (empty m m0 : HNSW d α) ∧ WellFormed (empty m m0 : HNSW d α) := by
  refine ⟨⟨?_, ⟨?_, ?_⟩⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [empty, size, EntryOnTop, DegreeBounded, NoSelfLinks, NoRepeatedLinks, OneNodePerPoint]

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
/-- The graph with no nodes is valid, at any caps. -/
theorem valid_empty (m m0 : ℕ) : Valid (empty m m0 : HNSW d α) := (valid_wellFormed_empty m m0).1

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
/-- The graph with no nodes is well formed, at any caps. -/
theorem wellFormed_empty (m m0 : ℕ) : WellFormed (empty m m0 : HNSW d α) :=
  (valid_wellFormed_empty m m0).2

omit [CommRing α] [LinearOrder α] [IsStrictOrderedRing α] in
/-- **The pieces split into the box's and the rest**: the six pieces of the stored graph are
exactly `Valid` and `WellFormed`. -/
theorem pieces_iff_valid_wellFormed (g : HNSW d α) :
    (DegreeBounded g ∧ NestedLayers g ∧ NoSelfLinks g ∧ NoRepeatedLinks g ∧ EntryOnTop g ∧
      OneNodePerPoint g) ↔ Valid g ∧ WellFormed g := by
  simp only [Valid, WellFormed, and_assoc]

/-- The graphs the library's build makes: `Builds` of its insertion. -/
abbrev Built : HNSW d α → Prop := Builds insert

omit [IsStrictOrderedRing α] in
/-- **Every built graph is `Valid` and `WellFormed`**, at caps with `m ≤ m0`. -/
theorem valid_wellFormed_build {g : HNSW d α} (h : Built g) (hm : g.m ≤ g.m0) :
    Valid g ∧ WellFormed g := by
  unfold Built at h
  induction h with
  | empty m m0 => exact valid_wellFormed_empty m m0
  | @insert g' p top cands _ hc ih =>
    have hcaps := caps_insert g' p top cands
    have hm' := hm
    rw [hcaps.1, hcaps.2] at hm'
    exact valid_insert hm' (ih hm').1 (ih hm').2 hc

omit [IsStrictOrderedRing α] in
/-- **Every built graph is `Valid`**, at caps with `m ≤ m0`. -/
theorem valid_build {g : HNSW d α} (h : Built g) (hm : g.m ≤ g.m0) : Valid g :=
  (valid_wellFormed_build h hm).1

omit [IsStrictOrderedRing α] in
/-- **Every built graph is `WellFormed`**, at caps with `m ≤ m0`. -/
theorem wellFormed_build {g : HNSW d α} (h : Built g) (hm : g.m ≤ g.m0) : WellFormed g :=
  (valid_wellFormed_build h hm).2

end HNSW

end AlgoDesign.Geometry
