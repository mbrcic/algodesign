/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.TopoOrder.Basic

/-!
# The DFS order and the named cycle

Sources: Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), §20.4,
`TOPOLOGICAL-SORT` and Theorem 20.12 (the reverse finishing order of a depth-first search of a
graph without cycles is a topological order); Sedgewick and Wayne, *Algorithms* (4th ed.),
`DirectedCycle` (pp. 577–581), for returning the cycle a back arrow closes; the cycle is written
`w, …, v, w` as cp-algorithms ("Checking a graph for acyclicity and finding a cycle") and Laaksonen,
*Competitive Programmer's Handbook*, print it; Tarjan and Zwick, *European Journal of
Combinatorics* 119 (2024), §6.1, for the explicit frames.

The walk keeps a stack of frames, each a vertex and the position of the next entry of its row to
look at. Roots are tried from vertex 0 upward. A vertex is marked entered when its frame is pushed.
The top frame looks at one entry at a time: an arrow to a vertex not yet entered pushes that
vertex's frame; an arrow to a vertex whose frame is on the stack is a back arrow, and the walk
returns the cycle from that vertex up the stack to the top and back; an arrow to a finished vertex
is passed over. A frame whose row is done is popped and its vertex finishes. The answer is the
finishing order reversed; the walk keeps it reversed as it goes, each finished vertex put in front.

The walk runs on explicit fuel, enough for every push, look and pop (`dfsFuel`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.TopoOrder

open Digraph

/-- **The state of the DFS walk.** -/
structure DfsState where
  /-- Whether each vertex has been entered. -/
  entered : ℕ → Bool
  /-- The frames, top first: each a vertex and the position of the next entry of its row. -/
  stack : List (ℕ × ℕ)
  /-- The finished vertices, the latest first: the finishing order reversed. -/
  order : List ℕ
  /-- The next vertex to try as a root. -/
  root : ℕ

/-- The cycle a back arrow from the top of the stack to `w` closes: `w`, the vertices of the frames
above `w`'s from the bottom up, and `w` again. -/
def cycleAt (w : ℕ) (stack : List (ℕ × ℕ)) : List ℕ :=
  w :: ((stack.map Prod.fst).takeWhile (· ≠ w)).reverse ++ [w]

/-- The start: nothing entered, no frames, nothing finished, roots from vertex 0. -/
def dfsStart : DfsState := ⟨fun _ => false, [], [], 0⟩

/-- The DFS walk, for at most `f` moves: an answer `.ok` the finishing order reversed, or
`.error` a named cycle. -/
def dfsRun (g : Digraph) : ℕ → DfsState → Except (List ℕ) (List ℕ)
  | 0, st => .ok st.order
  | f + 1, st =>
    match st.stack with
    | [] =>
      if st.root < g.n then
        if st.entered st.root then dfsRun g f { st with root := st.root + 1 }
        else
          dfsRun g f { st with entered := Function.update st.entered st.root true,
                               stack := [(st.root, 0)] }
      else .ok st.order
    | (v, i) :: rest =>
      match (g.out v)[i]? with
      | none => dfsRun g f { st with stack := rest, order := v :: st.order }
      | some (w, _) =>
        if !st.entered w then
          dfsRun g f { st with entered := Function.update st.entered w true,
                               stack := (w, 0) :: (v, i + 1) :: rest }
        else if w ∈ st.stack.map Prod.fst then .error (cycleAt w st.stack)
        else dfsRun g f { st with stack := (v, i + 1) :: rest }

/-- A weight above the length of any row: the total length of all rows, plus 2. -/
def rowWeight (g : Digraph) : ℕ := ((List.range g.n).map fun w => (g.out w).length).sum + 2

/-- Fuel for the whole walk: each vertex entered at most once, each entry of its row looked at
once, its frame popped once, and each root tried once. -/
def dfsFuel (g : Digraph) : ℕ := (rowWeight g + 1) * g.n

/-- **The DFS order**: the reverse finishing order of a depth-first walk from roots `0` upward, or
the cycle the first back arrow closes. -/
def dfsOrder (g : Digraph) : Except (List ℕ) (List ℕ) := dfsRun g (dfsFuel g) dfsStart

/-! ## What the walk keeps -/

/-- The first `k` entries of `v`'s row lead to finished vertices. -/
def RowDone (g : Digraph) (order : List ℕ) (v k : ℕ) : Prop :=
  ∀ j < k, ∀ e, (g.out v)[j]? = some e → e.1 ∈ order

/-- **The frames, top first, are where the walk left them.** Each frame's position is within its
row; every entry before it leads to a finished vertex, except that below the top, the last entry
looked at leads to the vertex of the frame just above (`above`). -/
def Frames (g : Digraph) (order : List ℕ) : Option ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | none, (v, i) :: rest =>
    i ≤ (g.out v).length ∧ RowDone g order v i ∧ Frames g order (some v) rest
  | some w, (v, i) :: rest =>
    0 < i ∧ i ≤ (g.out v).length ∧ ((g.out v)[i - 1]?).map Prod.fst = some w ∧
      RowDone g order v (i - 1) ∧ Frames g order (some v) rest

/-- **What the DFS walk keeps.** The vertices of the frames are different and, from the bottom up,
each has an arrow to the next; a vertex is entered exactly when it is finished or on the stack, and
never both; finished vertices are listed once; entered vertices are vertices of the graph; every
arrow from a finished vertex leads to a vertex that finished before it; the frames are where the
walk left them; and every root tried so far is entered. -/
structure DfsInv (g : Digraph) (st : DfsState) : Prop where
  nodup : (st.stack.map Prod.fst).Nodup
  chain : (st.stack.map Prod.fst).reverse.IsChain g.Arrow
  entered : ∀ w, st.entered w = true ↔ w ∈ st.order ∨ w ∈ st.stack.map Prod.fst
  order_nodup : st.order.Nodup
  disjoint : ∀ w ∈ st.order, w ∉ st.stack.map Prod.fst
  lt : ∀ w, st.entered w = true → w < g.n
  finished : ∀ u ∈ st.order, ∀ e ∈ g.out u, Before st.order u e.1
  frames : Frames g st.order none st.stack
  roots : ∀ r < st.root, st.entered r = true

/-- The number of vertices not yet entered. -/
def unentered (g : Digraph) (st : DfsState) : ℕ :=
  (List.range g.n).countP fun w => !st.entered w

/-- What the frames have left to do: for each, the entries of its row not yet looked at, and its
pop. -/
def frameWork (g : Digraph) (stack : List (ℕ × ℕ)) : ℕ :=
  (stack.map fun f => (g.out f.1).length + 1 - f.2).sum

/-- **A bound on the moves left**: each vertex not entered may still cost its whole row, a push and
a pop; each frame its remaining entries and its pop; each root not yet tried, one move. -/
def potential (g : Digraph) (st : DfsState) : ℕ :=
  rowWeight g * unentered g st + frameWork g st.stack + (g.n - st.root)

/-! ## Facts the proof uses -/

theorem RowDone.mono {g : Digraph} {o o' : List ℕ} (ho : ∀ x ∈ o, x ∈ o') {v k : ℕ}
    (h : RowDone g o v k) : RowDone g o' v k :=
  fun j hj e he => ho _ (h j hj e he)

theorem Frames.mono {g : Digraph} {o o' : List ℕ} (ho : ∀ x ∈ o, x ∈ o') :
    ∀ {a : Option ℕ} {s : List (ℕ × ℕ)}, Frames g o a s → Frames g o' a s
  | _, [], _ => trivial
  | none, (_, _) :: _, ⟨h1, h2, h3⟩ => ⟨h1, h2.mono ho, Frames.mono ho h3⟩
  | some _, (_, _) :: _, ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, h3.mono ho, Frames.mono ho h4⟩

theorem Frames.le_length {g : Digraph} {o : List ℕ} {a : Option ℕ} {v i : ℕ}
    {rest : List (ℕ × ℕ)} (h : Frames g o a ((v, i) :: rest)) : i ≤ (g.out v).length := by
  cases a with
  | none => exact h.1
  | some _ => exact h.2.1

/-- Every arrow to a vertex of the graph is in its tail's row. -/
theorem exists_mem_out {g : Digraph} {u x : ℕ} (ha : g.Arrow u x) (hx : x < g.n) :
    ∃ i, (x, i) ∈ g.out u := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
  refine ⟨i, ?_⟩
  simp only [out, idsBetween, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  exact ⟨x, hx, i, ⟨(List.getElem?_eq_some_iff.1 hi).1, hi⟩, rfl, rfl⟩

theorem out_length_add_two_le {g : Digraph} {w : ℕ} (hw : w < g.n) :
    (g.out w).length + 2 ≤ rowWeight g := by
  unfold rowWeight
  suffices ∀ m, w < m → (g.out w).length ≤ ((List.range m).map fun w => (g.out w).length).sum by
    have := this g.n hw
    omega
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hm : w < m
    · have := ih hm
      omega
    · have : w = m := by omega
      subst this
      simp

theorem unentered_update {g : Digraph} {st : DfsState} {w : ℕ} (hw : w < g.n)
    (he : st.entered w = false) :
    (List.range g.n).countP (fun x => !Function.update st.entered w true x) + 1 =
      unentered g st := by
  unfold unentered
  have hnd : ∀ l : List ℕ, w ∈ l → l.Nodup →
      l.countP (fun x => !Function.update st.entered w true x) + 1 =
        l.countP (fun x => !st.entered x) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hw hnd
      rw [List.countP_cons, List.countP_cons]
      by_cases haw : a = w
      · subst haw
        have hal : a ∉ l := (List.nodup_cons.1 hnd).1
        have : l.countP (fun x => !Function.update st.entered a true x) =
            l.countP (fun x => !st.entered x) :=
          List.countP_congr fun x hx => by
            have hxa : x ≠ a := fun h => hal (by rw [← h]; exact hx)
            rw [Function.update_of_ne hxa]
        simp [this, he]
      · have := ih (by simpa [Ne.symm haw] using hw) (List.nodup_cons.1 hnd).2
        simp only [Function.update_of_ne haw]
        omega
  exact hnd _ (List.mem_range.2 hw) List.nodup_range

/-! ## The cycle branch -/

theorem dropWhile_ne_of_mem {w : ℕ} :
    ∀ {P : List ℕ}, w ∈ P → ∃ D, P.dropWhile (· ≠ w) = w :: D
  | a :: P, h => by
    by_cases ha : a = w
    · subst ha
      exact ⟨P, by simp⟩
    · have : w ∈ P := by simpa [Ne.symm ha] using h
      obtain ⟨D, hD⟩ := dropWhile_ne_of_mem this
      exact ⟨D, by rw [List.dropWhile_cons, decide_eq_true ha]; exact hD⟩

/-- **A back arrow names a cycle**: from the top frame's vertex `v` to a vertex `w` on the stack,
the vertices of the frames from `w` up to `v`, closed by `w`, form a named cycle. -/
theorem isCycle_cycleAt {g : Digraph} {st : DfsState} (h : DfsInv g st) {v i w : ℕ}
    {rest : List (ℕ × ℕ)} (hs : st.stack = (v, i) :: rest) (harr : g.Arrow v w)
    (hw : w ∈ st.stack.map Prod.fst) : IsCycle g (cycleAt w st.stack) := by
  unfold cycleAt
  set P := st.stack.map Prod.fst with hP
  set T := P.takeWhile (· ≠ w)
  obtain ⟨D, hD⟩ := dropWhile_ne_of_mem hw
  have hsplit : P = T ++ w :: D := by
    rw [← hD]
    exact (List.takeWhile_append_dropWhile).symm
  have hhead : P.head? = some v := by simp [hP, hs]
  have hlast : (w :: T.reverse).getLast? = some v := by
    have : w :: T.reverse = (T ++ [w]).reverse := by simp
    rw [this, List.getLast?_reverse, ← hhead, hsplit]
    cases T <;> simp
  have hnd : (w :: T.reverse).Nodup := by
    have hsub : (T ++ [w]).Sublist P := by
      rw [hsplit]
      exact List.Sublist.append_left (List.singleton_sublist.2 (by simp)) T
    have : (w :: T.reverse).Perm (T ++ [w]) := by
      have := List.reverse_perm (T ++ [w])
      simpa using this
    exact this.nodup_iff.2 (h.nodup.sublist hsub)
  have hch : (w :: T.reverse).IsChain g.Arrow := by
    have hrev : P.reverse = D.reverse ++ w :: T.reverse := by
      rw [hsplit]
      simp
    have := h.chain
    rw [← hP, hrev] at this
    exact this.infix (List.suffix_append _ _).isInfix
  refine ⟨by simp, by rw [List.getLast?_concat]; rfl, ?_, ?_⟩
  · rw [List.cons_append, ← List.cons_append, List.isChain_append]
    refine ⟨hch, List.isChain_singleton w, fun x hx y hy => ?_⟩
    rw [hlast] at hx
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
    exact hx ▸ hy ▸ harr
  · rw [List.cons_append, ← List.cons_append, List.dropLast_concat]
    exact hnd

/-! ## The order branch -/

/-- **A finished walk's answer is a topological order** (Cormen, Leiserson, Rivest and Stein,
Theorem 20.12): every vertex entered and finished, and every arrow from a finished vertex leads to
one that finished before it. -/
theorem isTopoOrder_of_done {g : Digraph} (hg : g.WellFormed) {st : DfsState} (h : DfsInv g st)
    (hs : st.stack = []) (hr : g.n ≤ st.root) : IsTopoOrder g st.order := by
  have hmem : ∀ x, x ∈ st.order ↔ x < g.n := by
    intro x
    constructor
    · intro hx
      exact h.lt x ((h.entered x).2 (Or.inl hx))
    · intro hx
      rcases (h.entered x).1 (h.roots x (by omega)) with hx | hx
      · exact hx
      · simp [hs] at hx
  refine ⟨(List.perm_ext_iff_of_nodup h.order_nodup List.nodup_range).2 fun x => ?_,
    fun a ha => ?_⟩
  · rw [hmem, List.mem_range]
  · obtain ⟨i, hi⟩ := exists_mem_out ha (hg a ha).2
    exact h.finished a.1 ((hmem _).2 (hg a ha).1) _ hi

/-! ## Each move keeps what the walk keeps -/

/-- When the top frame is popped, the frame below it has its last entry finished. -/
theorem Frames.pop {g : Digraph} {o o' : List ℕ} {v : ℕ} (hv : v ∈ o') (ho : ∀ x ∈ o, x ∈ o') :
    ∀ {rest : List (ℕ × ℕ)}, Frames g o (some v) rest → Frames g o' none rest
  | [], _ => trivial
  | (u, j) :: rest, ⟨_, h1, h2, h3, h4⟩ => by
    refine ⟨h1, fun j' hj' e he => ?_, h4.mono ho⟩
    by_cases hj : j' < j - 1
    · exact ho _ (h3 j' hj e he)
    · have : j' = j - 1 := by omega
      subst this
      rw [he] at h2
      simp only [Option.map_some, Option.some.injEq] at h2
      exact h2 ▸ hv

/-- The start keeps what the walk keeps. -/
theorem dfsInv_start (g : Digraph) : DfsInv g dfsStart where
  nodup := List.nodup_nil
  chain := List.IsChain.nil
  entered _ := by simp [dfsStart]
  order_nodup := List.nodup_nil
  disjoint _ h := by simp [dfsStart] at h
  lt _ h := by simp [dfsStart] at h
  finished _ h := by simp [dfsStart] at h
  frames := trivial
  roots _ h := by simp [dfsStart] at h

/-- **The walk's promise from any state it keeps**, given fuel for the moves left. -/
theorem dfsRun_spec {g : Digraph} (hg : g.WellFormed) (f : ℕ) :
    ∀ st : DfsState, DfsInv g st → potential g st ≤ f → DfsPromise g (dfsRun g f st) := by
  induction f with
  | zero =>
    intro st h hp
    have hs : st.stack = [] := by
      rcases hs : st.stack with _ | ⟨⟨v, i⟩, rest⟩
      · rfl
      · have hle : i ≤ (g.out v).length := by
          have := h.frames
          rw [hs] at this
          exact this.le_length
        unfold potential frameWork at hp
        rw [hs] at hp
        simp only [List.map_cons, List.sum_cons] at hp
        omega
    have hr : g.n ≤ st.root := by
      unfold potential at hp
      omega
    exact isTopoOrder_of_done hg h hs hr
  | succ f ih =>
    intro st h hp
    obtain ⟨ent, stack, order, root⟩ := st
    cases stack with
    | nil =>
      simp only [dfsRun]
      split
      · next hr =>
        split
        · next he =>
          refine ih _ ⟨h.nodup, h.chain, h.entered, h.order_nodup, h.disjoint, h.lt, h.finished,
            h.frames, fun r hr' => ?_⟩ ?_
          · dsimp only at hr'
            by_cases hrr : r < root
            · exact h.roots r hrr
            · have : r = root := by omega
              exact this ▸ he
          · simp only [potential, unentered] at hp ⊢
            omega
        · next he =>
          have he' : ent root = false := by simpa using he
          refine ih _ ⟨by simp, by simp, fun x => ?_, h.order_nodup, fun x hx => ?_,
            fun x hx => ?_, h.finished, ?_, fun r hr' => ?_⟩ ?_
          · dsimp only
            by_cases hx : x = root
            · subst hx
              simp
            · rw [Function.update_of_ne hx, h.entered x]
              simp [hx]
          · simp only [List.map_cons, List.map_nil, List.mem_singleton]
            rintro rfl
            exact absurd ((h.entered _).2 (Or.inl hx)) (by simp [he'])
          · dsimp only at hx
            by_cases hxr : x = root
            · exact hxr ▸ hr
            · rw [Function.update_of_ne hxr] at hx
              exact h.lt x hx
          · simp only [Frames]
            exact ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j), trivial⟩
          · dsimp only
            by_cases hrr : r = root
            · subst hrr
              simp
            · rw [Function.update_of_ne hrr]
              exact h.roots r hr'
          · have hU := unentered_update (st := ⟨ent, [], order, root⟩) hr he'
            have hW := out_length_add_two_le hr
            unfold potential at hp ⊢
            change (List.range g.n).countP (fun x => !Function.update ent root true x) + 1 =
              unentered g ⟨ent, [], order, root⟩ at hU
            unfold unentered
            rw [← hU, Nat.mul_succ] at hp
            simp only [frameWork, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hp ⊢
            omega
      · next hr =>
        exact isTopoOrder_of_done hg h rfl (by dsimp only; omega)
    | cons fr rest =>
      obtain ⟨v, i⟩ := fr
      have hnd := h.nodup
      simp only [List.map_cons, List.nodup_cons] at hnd
      have hfr : i ≤ (g.out v).length ∧ RowDone g order v i ∧ Frames g order (some v) rest :=
        h.frames
      simp only [dfsRun]
      split
      · next ho =>
        -- the row is done: pop the frame, and its vertex finishes
        have hilen : (g.out v).length ≤ i := List.getElem?_eq_none_iff.1 ho
        have hvo : v ∉ order := fun hv => h.disjoint v hv (by simp)
        refine ih _ ⟨hnd.2, ?_, fun x => ?_, List.nodup_cons.2 ⟨hvo, h.order_nodup⟩,
          fun x hx => ?_, h.lt, fun u hu e he => ?_,
          hfr.2.2.pop List.mem_cons_self fun x hx => List.mem_cons_of_mem _ hx, h.roots⟩ ?_
        · have hc := h.chain
          simp only [List.map_cons, List.reverse_cons] at hc
          exact (List.isChain_append.1 hc).1
        · rw [h.entered x]
          simp only [List.map_cons, List.mem_cons]
          tauto
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hnd.1
          · have := h.disjoint x hx
            simp only [List.map_cons, List.mem_cons, not_or] at this
            exact this.2
        · rcases List.mem_cons.1 hu with rfl | hu
          · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he
            have hjlt : j < (g.out u).length := (List.getElem?_eq_some_iff.1 hj).1
            exact List.Sublist.cons_cons _
              (List.singleton_sublist.2 (hfr.2.1 j (by omega) e hj))
          · exact (h.finished u hu e he).trans (List.sublist_cons_self v order)
        · unfold potential at hp ⊢
          simp only [unentered, frameWork, List.map_cons, List.sum_cons] at hp ⊢
          omega
      · next w id ho =>
        have hwrow : (w, id) ∈ g.out v := List.mem_of_getElem? ho
        obtain ⟨hwn, harr⟩ := mem_out hwrow
        have hilt : i < (g.out v).length := (List.getElem?_eq_some_iff.1 ho).1
        split
        · next hent =>
          -- an arrow to a vertex not entered: push its frame
          have hent' : ent w = false := by simpa using hent
          have hwP : w ∉ v :: rest.map Prod.fst := fun hm => by
            have := (h.entered w).2 (Or.inr (by simpa using hm))
            simp [hent'] at this
          have hwo : w ∉ order := fun hm => by
            have := (h.entered w).2 (Or.inl hm)
            simp [hent'] at this
          refine ih _ ⟨?_, ?_, fun x => ?_, h.order_nodup, fun x hx => ?_, fun x hx => ?_,
            h.finished, ?_, fun r hr' => ?_⟩ ?_
          · simp only [List.map_cons]
            exact List.nodup_cons.2 ⟨hwP, List.nodup_cons.2 hnd⟩
          · have hc := h.chain
            simp only [List.map_cons] at hc ⊢
            rw [List.reverse_cons, List.isChain_append]
            refine ⟨hc, List.isChain_singleton w, fun x hx y hy => ?_⟩
            simp only [List.getLast?_reverse, List.head?_cons, Option.mem_def,
              Option.some.injEq] at hx hy
            exact hx ▸ hy ▸ harr
          · dsimp only
            by_cases hx : x = w
            · subst hx
              simp
            · rw [Function.update_of_ne hx, h.entered x]
              simp [hx]
          · have := h.disjoint x hx
            simp only [List.map_cons, List.mem_cons, not_or] at this ⊢
            exact ⟨fun hxw => hwo (hxw ▸ hx), this⟩
          · dsimp only at hx
            by_cases hxw : x = w
            · exact hxw ▸ hwn
            · rw [Function.update_of_ne hxw] at hx
              exact h.lt x hx
          · simp only [Frames]
            refine ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j), Nat.succ_pos i,
              hilt, by simp [ho], by simpa using hfr.2.1, hfr.2.2⟩
          · dsimp only
            by_cases hrw : r = w
            · subst hrw
              simp
            · rw [Function.update_of_ne hrw]
              exact h.roots r hr'
          · have hU := unentered_update (st := ⟨ent, (v, i) :: rest, order, root⟩) hwn hent'
            have hW := out_length_add_two_le hwn
            unfold potential at hp ⊢
            change (List.range g.n).countP (fun x => !Function.update ent w true x) + 1 =
              unentered g ⟨ent, (v, i) :: rest, order, root⟩ at hU
            unfold unentered
            rw [← hU, Nat.mul_succ] at hp
            simp only [frameWork, List.map_cons, List.sum_cons] at hp ⊢
            dsimp only at hp hW ⊢
            omega
        · next hent =>
          have hent' : ent w = true := by simpa using hent
          split
          · next hin =>
            -- a back arrow: name the cycle
            exact isCycle_cycleAt h rfl harr hin
          · next hin =>
            -- an arrow to a finished vertex: pass over it
            have hwo : w ∈ order := by
              rcases (h.entered w).1 hent' with h' | h'
              · exact h'
              · exact absurd h' hin
            refine ih _ ⟨h.nodup, h.chain, h.entered, h.order_nodup, h.disjoint, h.lt,
              h.finished, ⟨hilt, fun j hj e he => ?_, hfr.2.2⟩, h.roots⟩ ?_
            · by_cases hji : j < i
              · exact hfr.2.1 j hji e he
              · have : j = i := by omega
                subst this
                rw [ho] at he
                cases he
                exact hwo
            · unfold potential at hp ⊢
              simp only [unentered, frameWork, List.map_cons, List.sum_cons] at hp ⊢
              omega

/-- **The DFS order's promise**: on a graph whose arrows join its vertices, every vertex exactly
once with every arrow forward, or a named cycle. -/
theorem dfsOrder_spec {g : Digraph} (hg : g.WellFormed) : DfsPromise g (dfsOrder g) := by
  refine dfsRun_spec hg _ _ (dfsInv_start g) ?_
  have : unentered g dfsStart = g.n := by
    simp [unentered, dfsStart]
  unfold potential dfsFuel
  rw [this]
  simp [dfsStart, frameWork, Nat.succ_mul]

example : dfsOrder ⟨3, [(0, 1), (1, 2), (0, 2)]⟩ = .ok [0, 1, 2] := by decide
example : dfsOrder ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ = .error [0, 1, 2, 0] := by decide
example : dfsOrder ⟨2, [(1, 1)]⟩ = .error [1, 1] := by decide
example : dfsOrder ⟨4, [(0, 1), (2, 3)]⟩ = .ok [2, 3, 0, 1] := by decide
example : dfsOrder ⟨0, []⟩ = .ok [] := by decide

end AlgoDesign.Graphs.TopoOrder
