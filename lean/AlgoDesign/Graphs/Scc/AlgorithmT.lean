/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Basic

/-!
# Strong components: Algorithm T

Source: Tarjan and Zwick, *Finding strong components using depth-first search*, European Journal
of Combinatorics 119 (2024), arXiv 2201.07197v3: Algorithm T, Fig. 2 (p. 12), walked as
Implementation V (§6.1, Fig. 7(a), p. 20): a stack of frames (vertex, next row position) for the
current path, a separate stack `F` of followers with Fig. 2's guard at its bottom, low values with
"low = 0 means unvisited", and finished vertices marked done with a value above every entry number.

One step of the walk looks at one arrow, enters one vertex, or finishes one vertex, so the walk
is executed with fuel: `3 n + m` steps finish it. Where a move lowers the current vertex's low
value the walk checks p. 12's stop when done: once every vertex is entered and that low value has
dropped to the root's, everything not yet out comes out as one group and the walk ends.

Groups come out sinks first; the group emitted `e`-th of `k` gets id `k - 1 - e`, so the ids are
a topological order of the graph of groups. Each group's members come out in postorder: its
followers in the order they finished, then its leader.

The walk state also carries what the invariants read and the walk never does: each vertex's entry
number, the vertices in the order they finished, and the arrows the walk has come back over, in
order. `Valid` has one piece per box invariant, written from Tarjan–Zwick's Fig. 2 and Lemmas
3.8 and 3.9, each decidable; `traceValid` checks them at every step of a run, by `decide` on the
examples.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

namespace AlgorithmT

variable (g : Digraph)

/-- Nothing entered; `F` holds the guard. -/
def start : Walk :=
  ⟨g, 0, fun _ => 0, fun _ => false, [], [guard g], [], fun _ => 0, 0, fun _ => 0, [], []⟩

/-- Enter `v`: the next entry number becomes its low value, and it may lead. -/
def previsit (w : Walk) (v : ℕ) : Walk :=
  { w with time := w.time + 1, low := Function.update w.low v (w.time + 1),
           lead := Function.update w.lead v true, path := (v, 0) :: w.path,
           pre := Function.update w.pre v (w.time + 1) }

/-- Come back over the arrow from `v` to `x`: `v` takes `x`'s low value if smaller, and then no
longer leads. -/
def retreat (w : Walk) (v x : ℕ) : Walk :=
  let w := { w with retreats := w.retreats ++ [(v, x)] }
  if w.low x < w.low v then
    { w with low := Function.update w.low v (w.low x), lead := Function.update w.lead v false }
  else w

/-- Pop from `F` while the top's low value is at least `lv`; the popped vertices, top first, and
what is left. -/
def popFollowers (low : ℕ → ℕ) (lv : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | x :: f =>
    if lv ≤ low x then
      let r := popFollowers low lv f
      (x :: r.1, r.2)
    else ([], x :: f)

/-- Finish `v` (Fig. 2's postvisit): a leader takes the followers above it on `F` as its group,
which comes out with its members in postorder and every member marked done; a vertex that does
not lead goes on `F`. -/
def postvisit (w : Walk) (v : ℕ) : Walk :=
  let w := { w with finished := w.finished ++ [v] }
  if w.lead v then
    let r := popFollowers w.low (w.low v) w.followers
    let grp := r.1.reverse ++ [v]
    { w with low := fun u => if u ∈ grp then done g else w.low u,
             emitted := fun u => if u ∈ grp then w.groups.length else w.emitted u,
             followers := r.2, groups := w.groups ++ [grp] }
  else { w with followers := v :: w.followers }

/-- **One move**: with no current vertex, enter the next root if it is unvisited, else move the
outer loop on; otherwise look at the current vertex's next arrow, entering its head if unvisited
and coming back over it if not; at the end of the row, finish the vertex and come back over the
arrow that led to it. -/
def move (w : Walk) : Walk :=
  match w.path with
  | [] =>
    if w.next < g.n then
      if w.low w.next = 0 then previsit w w.next else { w with next := w.next + 1 }
    else w
  | (v, i) :: rest =>
    match (g.out v)[i]? with
    | some (x, _) =>
      let w := { w with path := (v, i + 1) :: rest }
      if w.low x = 0 then previsit w x else retreat w v x
    | none =>
      let w := postvisit g { w with path := rest } v
      match rest with
      | (u, _) :: _ => retreat w u v
      | [] => w

/-- Every vertex has been entered, and the current vertex's low value equals the root's, the root
being the vertex at the bottom of the path. -/
def doneAtRoot (w : Walk) : Bool :=
  match w.path with
  | [] => false
  | (v, i) :: rest => w.time == g.n && w.low v == w.low (rest.getLastD (v, i)).1

/-- **Stop when done** (Tarjan–Zwick p. 12): the move from `w` to `w'` has just lowered the current
vertex's low value, to the root's, with every vertex entered. -/
def stops (w w' : Walk) : Bool :=
  match w'.path with
  | [] => false
  | (v, _) :: _ => decide (w'.low v < w.low v) && doneAtRoot g w'

/-- **Everything not yet out comes out**: the open list from its bottom, then the path from the
top down, as one group, every member marked done; the walk ends. The path's vertices finish now, top
first, as they would one by one. -/
def stopAll (w : Walk) : Walk :=
  let grp := w.followers.dropLast.reverse ++ w.path.map Prod.fst
  { w with low := fun u => if u ∈ grp then done g else w.low u,
           emitted := fun u => if u ∈ grp then w.groups.length else w.emitted u,
           path := [], followers := [guard g], groups := w.groups ++ [grp], next := g.n,
           finished := w.finished ++ w.path.map Prod.fst }

/-- **One step**: one move, and the stop when done if that move calls for it. -/
def step (w : Walk) : Walk :=
  let w' := move g w
  if stops g w w' then stopAll g w' else w'

/-- `fuel` moves, never stopping early: the walk the proofs follow first. -/
def runMove : ℕ → Walk → Walk
  | 0, w => w
  | k + 1, w => runMove k (move g w)

/-- `fuel` steps. -/
def run : ℕ → Walk → Walk
  | 0, w => w
  | k + 1, w => run k (step g w)

/-- `run` is the step iterated. -/
theorem run_eq_iterate : ∀ (k : ℕ) (w : Walk), run g k w = (step g)^[k] w
  | 0, _ => rfl
  | k + 1, w => run_eq_iterate k (step g w)

/-! ### The walk keeps its graph -/

@[simp] theorem previsit_g (w : Walk) (v : ℕ) : (previsit w v).g = w.g := rfl

@[simp] theorem retreat_g (w : Walk) (v x : ℕ) : (retreat w v x).g = w.g := by
  unfold retreat
  dsimp only
  split <;> rfl

@[simp] theorem postvisit_g (w : Walk) (v : ℕ) : (postvisit g w v).g = w.g := by
  unfold postvisit
  dsimp only
  split <;> rfl

@[simp] theorem move_g (w : Walk) : (move g w).g = w.g := by
  unfold move
  dsimp only
  repeat' split
  all_goals simp

@[simp] theorem stopAll_g (w : Walk) : (stopAll g w).g = w.g := rfl

@[simp] theorem step_g (w : Walk) : (step g w).g = w.g := by
  unfold step
  dsimp only
  split <;> simp

@[simp] theorem runMove_g : ∀ (k : ℕ) (w : Walk), (runMove g k w).g = w.g
  | 0, _ => rfl
  | k + 1, w => (runMove_g k (move g w)).trans (move_g g w)

@[simp] theorem run_g : ∀ (k : ℕ) (w : Walk), (run g k w).g = w.g
  | 0, _ => rfl
  | k + 1, w => (run_g k (step g w)).trans (step_g g w)

/-- Enough steps for the whole walk: each vertex entered, finished and passed by the outer loop
once, and each arrow looked at once. -/
def steps : ℕ := 3 * g.n + g.arrows.length

/-- The walk run to its end. -/
def final : Walk := run g (steps g) (start g)

/-- The walk without the stop, moved to its end. -/
def finalMove : Walk := runMove g (steps g) (start g)

end AlgorithmT

open AlgorithmT in
/-- **Algorithm T**: the strong components, group ids `k - 1 - e` for the group emitted `e`-th of
`k`, members in postorder, groups listed in id order. -/
def algorithmT (g : Digraph) : Components := read g (final g)

/-! ## The invariants, from Tarjan–Zwick's lemmas -/

namespace AlgorithmT

variable (g)

/-- Nothing has finished at the start, so no leader has. -/
theorem not_leaderOut_start (v : ℕ) : ¬ LeaderOut (g := g) (start g) v := by
  rintro ⟨u, -, -, hu, -⟩
  simp [start] at hu

/-- **The start is legal**: `F` holds only the guard, no vertex is entered, no group is out. -/
theorem valid_start : Valid (start g) := by
  refine ⟨by simp [FollowersInFinishOrder, start], fun v _ hv => absurd rfl hv, ?_, ?_⟩
  · intro v _
    refine ⟨⟨fun h => ?_, fun h => absurd h (not_leaderOut_start g v)⟩,
      ⟨fun h => by simp [start] at h, fun h => absurd h (not_leaderOut_start g v)⟩⟩
    simp [start, done] at h
  · intro m hm
    simp [start] at hm

/-- `Valid` at each of the next `k + 1` states of a run. -/
def traceValid : ℕ → Walk → Bool
  | 0, w => decide (Valid w)
  | k + 1, w => decide (Valid w) && traceValid k (step g w)

theorem traceValid_spec : ∀ (k : ℕ) (w : Walk), traceValid g k w = true →
    ∀ j ≤ k, Valid (run g j w)
  | 0, w, h, j, hj => by
    obtain rfl : j = 0 := by omega
    simpa [traceValid, run] using h
  | k + 1, w, h, j, hj => by
    simp only [traceValid, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j => exact traceValid_spec k _ h.2 j (by omega)

end AlgorithmT

/-- **Algorithm T keeps its invariants** [proved] `validAlong` (`Scc/WalkStop.lean`): every state
of the walk on a well-formed graph is `Valid`. Tarjan–Zwick 2024, Lemma 3.8 (p. 8) for box
invariant 2, Lemma 3.9 (p. 9) for 3, and the proof of Lemma 3.9 with Fig. 2's postvisit for 1.
`Valid` alone is not kept step by step: those proofs also use the shape of the depth-first walk
(Lemmas 2.3–2.6, 3.2 and 3.4: entry order along the path, which vertices are descendants,
components as subtrees), kept as further invariants of the walk in `AlgorithmT.Inv`
(`Scc/WalkInv.lean`). At the stop when done (p. 12), everything not yet out is the root's whole
component (`mem_stopGroup_iff`). `traceValid` also checks every state of a run by `decide` on the
examples. -/
def ValidAlong : Prop :=
  ∀ g : Digraph, g.WellFormed → ∀ k,
    Valid (AlgorithmT.run g k (AlgorithmT.start g))

/-- **Algorithm T's promise** [proved] `algorithmTPromise` (`Scc/Correct.lean`): on a well-formed
graph, its groups are the strong components with ids in topological order, its member lists agree
with them, and each lists its members in postorder. Tarjan–Zwick 2024: Lemmas 3.6–3.9 and
Theorem 3.10 (pp. 7–10) for the groups, Theorem 3.5 (p. 7) for the order in which they come out,
and p. 10 for the members in postorder. -/
def AlgorithmTPromise : Prop :=
  ∀ g : Digraph, g.WellFormed →
    IsSccPartition g (algorithmT g).groupOf ∧ IdsTopological g (algorithmT g).groupOf ∧
      MembersAgree g (algorithmT g) ∧ MembersInPostorder g (algorithmT g)

example : algorithmT ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ = ⟨[0, 0, 1], [[1, 0], [2]]⟩ := by decide

set_option maxRecDepth 4000 in
example : algorithmT ⟨7, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 3), (4, 3), (1, 5), (5, 5),
    (5, 3), (5, 6), (6, 1)]⟩ = ⟨[0, 0, 0, 1, 1, 0, 0], [[2, 6, 5, 1, 0], [4, 3]]⟩ := by decide

/-- The stop when done fires here: every vertex is entered when `2` looks along `2 → 0`, the fourth
move, and its low value drops to `0`'s, so the three come out together. -/
example : AlgorithmT.stops ⟨3, [(0, 1), (1, 2), (2, 0)]⟩
    (AlgorithmT.runMove ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ 3
      (AlgorithmT.start ⟨3, [(0, 1), (1, 2), (2, 0)]⟩))
    (AlgorithmT.runMove ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ 4
      (AlgorithmT.start ⟨3, [(0, 1), (1, 2), (2, 0)]⟩)) = true := by decide

example : AlgorithmT.traceValid ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ 12
    (AlgorithmT.start ⟨3, [(0, 1), (1, 0), (1, 2)]⟩) = true := by decide

end AlgoDesign.Graphs.Scc
