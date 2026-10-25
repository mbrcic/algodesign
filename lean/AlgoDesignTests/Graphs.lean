import AlgoDesign
import Mathlib.Tactic

/-! Regression checks for the Graphs chapter's specifications: the union-find, the topological
order, the strong components with the condensation, the checker and 2-SAT, the bridges, cut vertices
and blocks, the union-find with undo, and the design project's contract, each in its own
namespace. Run with `lake env lean -DwarningAsError=true AlgoDesignTests/Graphs.lean`. -/

namespace AlgoDesignTests.GraphsUnionFind
open AlgoDesign.Graphs AlgoDesign.Graphs.UnionFind

-- every item alone: four roots, four groups
example : (init 4).Valid ∧ (init 4).count = 4 := by decide
-- a structure whose count is not its number of roots breaks `CountIsRoots`, and only it
example : ({ init 4 with count := 3 } : UnionFind).Valid ∧
    ¬ ({ init 4 with count := 3 } : UnionFind).WellFormed := by decide
-- a merge of two items already together merges nothing and answers no
example : (((init 2).unions [(0, 1)]).union 1 0).2 = false ∧
    (((init 2).unions [(0, 1)]).union 1 0).1.rank 0 = 1 ∧
    (((init 2).unions [(0, 1)]).union 1 0).1.count = 1 := by decide
-- on equal ranks the second root goes under the first, whose rank rises
example : ((init 2).union 0 1).1.parent 1 = 0 ∧ ((init 2).union 0 1).1.rank 0 = 1 := by decide

/-! ### The naive candidates are turned away

A lookup that compresses nothing, or halves the path (each item on it points at its grandparent),
answers the root, keeps every root and points every item higher, so it keeps the promise; what the
library's lookup owes beyond it, `FindSpec` (`find_spec`), turns both away: `FindSpec.compresses`,
on a path three links deep, the first depth at which halving leaves an item short of the root. A
lookup that flattens every tree, not only the walked path, does all that and compresses too;
`FindSpec.others_kept` turns it away. A question that answers right but hands back a fresh
structure, every item alone, changes who is together; the contract's `Ops.LookupTells` turns it
away. A start with one hidden extra item reports a group too many; `Ops.StartsAlone` turns it
away. -/

section Contracts

/-- One group of eight with root 3 and the path `0 → 1 → 2 → 3`: ranks 0, 1, 2, 3 up the path,
and items 4 to 7 hang straight off the root, so the root's rank 3 has its 2 ^ 3 items. -/
private def deep8 : UnionFind :=
  ⟨8, fun i => if i < 3 then i + 1 else 3, fun i => if i ≤ 3 then i else 0, 1⟩

example : deep8.Valid ∧ deep8.WellFormed := by decide
-- the library's lookup points the whole walk at the root and moves nothing else
example : (deep8.find 0).1.parent 0 = 3 ∧ (deep8.find 0).1.parent 1 = 3 ∧
    (deep8.find 0).1.parent 2 = 3 ∧ (deep8.find 0).1.parent 4 = 3 := by decide

/-- Answers the root and changes nothing. -/
private def noCompression (u : UnionFind) (x : ℕ) : UnionFind × ℕ := (u, u.root x)

example : ¬ FindSpec deep8 0 (noCompression deep8 0) := by
  intro h
  have := h.compresses 0 (by decide)
  revert this
  decide

/-- Path halving: each item on the walk points at its grandparent, and the walk goes on from it. -/
private def halveAux : ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) × ℕ
  | 0, p, x => (p, x)
  | f + 1, p, x => if p x = x then (p, x) else halveAux f (Function.update p x (p (p x))) (p (p x))

private def halving (u : UnionFind) (x : ℕ) : UnionFind × ℕ :=
  ({ u with parent := (halveAux u.n u.parent x).1 }, u.root x)

example : ¬ FindSpec deep8 0 (halving deep8 0) := by
  intro h
  have := h.compresses 0 (by decide)
  revert this
  decide

/-- Points every item of every tree straight at its root, not only the walked path. -/
private def flattenAll (u : UnionFind) (x : ℕ) : UnionFind × ℕ :=
  ({ u with parent := fun i => u.root i }, u.root x)

example : ¬ FindSpec deep8 2 (flattenAll deep8 2) := by
  intro h
  have := h.others_kept 0 (by decide)
  revert this
  decide

/-- Answers as the library's question does, then forgets every merge. -/
private def forgetful : Ops :=
  { ops with joined := fun u x y => (init u.n, (u.joined x y).2),
             keeps := fun u hu hw x hx y hy =>
               ⟨(ops.keeps u hu hw x hx y hy).1, (ops.keeps u hu hw x hx y hy).2.1,
                 valid_init u.n⟩,
             keepsWellFormed := fun u hu hw x hx y hy =>
               ⟨(ops.keepsWellFormed u hu hw x hx y hy).1,
                 (ops.keepsWellFormed u hu hw x hx y hy).2.1, wellFormed_init u.n⟩,
             keepsItems := fun u hu hw x hx y hy =>
               ⟨(ops.keepsItems u hu hw x hx y hy).1, (ops.keepsItems u hu hw x hx y hy).2.1,
                 rfl⟩ }

example : ¬ Contract forgetful := by
  intro h
  have hv : twoDeep.Valid := by decide
  have hw : twoDeep.WellFormed := by decide
  have := (h.promise.2.2.1 twoDeep hv hw 0 (by decide) 0 (by decide)).2.2.2 0 (by decide) 2
    (by decide)
  simp only [Same] at this
  revert this
  decide

/-- Starts with one item more than asked for. -/
private def oneExtra : Ops :=
  { ops with init := fun n => init (n + 1), emptyValid := fun n => valid_init (n + 1),
             emptyWellFormed := fun n => wellFormed_init (n + 1) }

example : ¬ Contract oneExtra := fun h => absurd (h.promise.1 1).1 (by decide)

end Contracts

end AlgoDesignTests.GraphsUnionFind

namespace AlgoDesignTests.GraphsTopo
open AlgoDesign.Graphs AlgoDesign.Graphs.TopoOrder

/-! ### Answers, checked by the kernel -/

-- what an answer means, on small graphs

example : IsTopoOrder ⟨3, [(0, 1), (1, 2), (0, 2)]⟩ [0, 1, 2] := by decide
example : ¬ IsTopoOrder ⟨3, [(0, 1), (1, 2), (0, 2)]⟩ [0, 2, 1] := by decide
example : ¬ IsTopoOrder ⟨1, [(0, 0)]⟩ [0] := by decide
example : IsCycle ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ [1, 2, 0, 1] := by decide
example : IsCycle ⟨1, [(0, 0)]⟩ [0, 0] := by decide
example : ¬ IsCycle ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ [1, 2, 0, 1, 2, 0, 1] := by decide
example : IsStuck ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ [0, 1, 2] := by decide
example : ¬ IsStuck ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ [0, 1] := by decide
example : ¬ IsStuck ⟨4, [(0, 1), (1, 0), (2, 3), (3, 2)]⟩ [0, 1] := by decide
example : IsStuck ⟨4, [(0, 1), (1, 0), (2, 3), (3, 2)]⟩ [0, 1, 2, 3] := by decide
example : IsStuck ⟨2, [(1, 1)]⟩ [1] := by decide
example : ¬ IsStuck ⟨2, [(0, 1)]⟩ [] := by decide

-- A ↔ B → C: all three are stuck, C too, since it waits on B
example : kahn ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ = .error [0, 1, 2] := by decide
example : IsStuck ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ [0, 1, 2] := by decide
-- a sub-cycle alone is not the stuck set: C waits on B and cannot be placed
example : ¬ IsStuck ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ [0, 1] := by decide
-- of two separate cycles, one alone is not the stuck set
example : ¬ IsStuck ⟨4, [(0, 1), (1, 0), (2, 3), (3, 2)]⟩ [0, 1] := by decide
-- a vertex that waits on nothing is not stuck, even beside a cycle
example : ¬ IsStuck ⟨3, [(0, 1), (1, 0)]⟩ [0, 1, 2] := by decide
example : kahn ⟨3, [(0, 1), (1, 0)]⟩ = .error [0, 1] := by decide
-- a loop: its vertex waits on itself and is stuck, and so is everything after it
example : kahn ⟨3, [(0, 1), (1, 1), (1, 2)]⟩ = .error [1, 2] := by decide
example : IsStuck ⟨3, [(0, 1), (1, 1), (1, 2)]⟩ [1, 2] := by decide
-- a doubled arrow counts twice and is walked twice
example : kahn ⟨2, [(0, 1), (0, 1)]⟩ = .ok [0, 1] := by decide
example : (start ⟨2, [(0, 1), (0, 1)]⟩).count 1 = 2 := by decide
-- the walk takes 3 vertices and walks 3 row entries: 6 looks, within n + m = 6
private def doubled : Digraph := ⟨3, [(0, 2), (0, 2), (1, 2)]⟩

example : ((runSteps step 3 (start doubled)).placed.map
    fun v => (doubled.out v).length + 1).sum = 6 := by decide
-- every state of the walk is legal, here after one and after two steps
example : Valid (step (start ⟨3, [(0, 2), (0, 2), (1, 2)]⟩)) := by decide
example : Valid (step (step (start ⟨3, [(0, 2), (0, 2), (1, 2)]⟩))) := by decide
-- the two methods give different orders on the same graph, both topological
example : kahn ⟨3, [(0, 2), (1, 2)]⟩ = .ok [0, 1, 2] := by decide
example : dfsOrder ⟨3, [(0, 2), (1, 2)]⟩ = .ok [1, 0, 2] := by decide
example : IsTopoOrder ⟨3, [(0, 2), (1, 2)]⟩ [1, 0, 2] := by decide
-- a 3-cycle is named w, …, v, w: from the vertex the back arrow reaches, up to the top
example : dfsOrder ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ = .error [0, 1, 2, 0] := by decide
example : IsCycle ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ [0, 1, 2, 0] := by decide
-- the back arrow closes the cycle above where it lands, not from the root
example : dfsOrder ⟨4, [(0, 1), (1, 2), (2, 3), (3, 1)]⟩ = .error [1, 2, 3, 1] := by decide
-- a loop's cycle is v, v
example : dfsOrder ⟨2, [(1, 1)]⟩ = .error [1, 1] := by decide
example : IsCycle ⟨2, [(1, 1)]⟩ [1, 1] := by decide
-- the empty graph has the empty order
example : kahn ⟨0, []⟩ = .ok [] ∧ dfsOrder ⟨0, []⟩ = .ok [] := by decide
-- the checkers agree with the properties
example : isStuck ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ [0, 1, 2] = true := by decide
example : isTopoOrder ⟨3, [(0, 2), (1, 2)]⟩ [0, 2, 1] = false := by decide
example : isCycle ⟨3, [(0, 1), (1, 2), (2, 0)]⟩ [0, 1, 2] = false := by decide

/-! ### The naive candidates are turned away

A Kahn whose counts ignore doubled arrows (one per waiting vertex, not per arrow) starts with a
count its walk then lowers too far; its start is not `Valid`, so `Ops.emptyValid` turns it away. A
Kahn whose walk lowers a count once per neighbour, not once per arrow, leaves a vertex stuck that
could be placed; `KahnPromise` turns it away. A Kahn that reports only the cycle, dropping the vertex that
waits on it, names a set that is not the whole of what is stuck; `KahnPromise` turns it away. A DFS
that marks a vertex when it is pushed on a stack of vertices to visit, not when it is entered, and
finishes it when it is popped, gives an order with an arrow pointing back; `DfsPromise`, what the
library's DFS order owes (`dfsOrder_spec`), turns it away. -/

section Contracts

/-- Counts the vertices each vertex waits on, not the arrows. -/
private def startDistinct (g : Digraph) : KahnState :=
  let c := fun v => ((List.range g.n).filter fun u => (u, v) ∈ g.arrows).length
  ⟨g, [], c, (List.range g.n).filter (fun v => c v = 0)⟩

example : ¬ Valid (startDistinct ⟨2, [(0, 1), (0, 1)]⟩) := by decide

/-- Walks each neighbour once, however many arrows lead to it. -/
private def stepOnce (st : KahnState) : KahnState :=
  match st.queue with
  | [] => st
  | v :: q =>
    let r := relax ((st.g.out v).filter fun e => (st.g.out v).find? (·.1 = e.1) = some e)
      st.count q
    ⟨st.g, st.placed ++ [v], r.1, r.2⟩

/-- Kahn's walk with that step. -/
private def onceWalk (g : Digraph) : Except (List ℕ) (List ℕ) :=
  answer g (runSteps stepOnce g.n (start g))

example : onceWalk ⟨2, [(0, 1), (0, 1)]⟩ = .error [1] := by decide

example : ¬ KahnPromise ⟨2, [(0, 1), (0, 1)]⟩ (onceWalk ⟨2, [(0, 1), (0, 1)]⟩) := by decide

/-- Reports the stuck set without its last vertex. -/
private def dropsOne (g : Digraph) : Except (List ℕ) (List ℕ) :=
  match kahn g with
  | .error s => .error s.dropLast
  | r => r

example : dropsOne ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ = .error [0, 1] := by decide

example : ¬ KahnPromise ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ (dropsOne ⟨3, [(0, 1), (1, 0), (1, 2)]⟩) := by
  decide

/-- A stack of vertices to visit, each marked when pushed and finished when popped. -/
private def markOnPushRun (g : Digraph) :
    ℕ → (ℕ → Bool) → List ℕ → List ℕ → ℕ → List ℕ
  | 0, _, _, done, _ => done
  | f + 1, m, [], done, r =>
    if r < g.n then
      if m r then markOnPushRun g f m [] done (r + 1)
      else markOnPushRun g f (Function.update m r true) [r] done r
    else done
  | f + 1, m, v :: s, done, r =>
    let p := (g.out v).foldl (fun (acc : (ℕ → Bool) × List ℕ) e =>
      if acc.1 e.1 then acc else (Function.update acc.1 e.1 true, e.1 :: acc.2)) (m, s)
    markOnPushRun g f p.1 p.2 (v :: done) r

private def markOnPush (g : Digraph) : Except (List ℕ) (List ℕ) :=
  .ok (markOnPushRun g (dfsFuel g) (fun _ => false) [] [] 0)

example : markOnPush ⟨3, [(0, 1), (0, 2), (1, 2)]⟩ = .ok [1, 2, 0] := by decide

example : ¬ DfsPromise ⟨3, [(0, 1), (0, 2), (1, 2)]⟩
    (markOnPush ⟨3, [(0, 1), (0, 2), (1, 2)]⟩) := by
  decide

end Contracts

end AlgoDesignTests.GraphsTopo

namespace AlgoDesignTests.GraphsScc
open AlgoDesign.Graphs AlgoDesign.Graphs.Scc AlgoDesign.Graphs.Scc.AlgorithmT

/-- A ↔ B → C. -/
def abc : Digraph := ⟨3, [(0, 1), (1, 0), (1, 2)]⟩

/-- Seven vertices: a knot {0, 1, 2, 5, 6} with a loop at 5, and a knot {3, 4} with a doubled arrow,
reached from the first by three arrows. -/
def seven : Digraph :=
  ⟨7, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 3), (4, 3), (1, 5), (5, 5), (5, 3), (5, 6),
    (6, 1)]⟩

/-- A loop at 0 and an arrow on to 1: two groups of one, the first cyclic. -/
def loopy : Digraph := ⟨2, [(0, 0), (0, 1)]⟩

/-- A ↔ B with three arrows to C, two of them doubled. -/
def doubled : Digraph := ⟨3, [(0, 1), (1, 0), (0, 2), (1, 2), (0, 2)]⟩

/-! ### Algorithm T: groups, ids topological, members in postorder -/

example : algorithmT abc = ⟨[0, 0, 1], [[1, 0], [2]]⟩ := by decide
example : IsSccPartition abc (algorithmT abc).groupOf := by decide
example : IdsTopological abc (algorithmT abc).groupOf := by decide
example : MembersAgree abc (algorithmT abc) ∧ MembersInPostorder abc (algorithmT abc) := by decide
example : finishOrder abc = [2, 1, 0] := by decide

set_option maxRecDepth 4000 in
example : algorithmT seven = ⟨[0, 0, 0, 1, 1, 0, 0], [[2, 6, 5, 1, 0], [4, 3]]⟩ := by decide
set_option maxRecDepth 4000 in
example : check seven (algorithmT seven).groupOf = none := by decide
set_option maxRecDepth 4000 in
example : IdsTopological seven (algorithmT seven).groupOf := by decide
set_option maxRecDepth 4000 in
example : MembersInPostorder seven (algorithmT seven) := by decide

-- a group of one with a loop: its own group, the loop dropped from the graph of groups
example : algorithmT loopy = ⟨[0, 1], [[0], [1]]⟩ := by decide
example : (condensation loopy (algorithmT loopy)).arrows = [(0, 1)] := by decide

/-- Every state of a run of `g` carries `g`. -/
theorem run_carries (g : Digraph) (k : ℕ) : (run g k (start g)).g = g := run_g _ _ _

/-- Decides `Valid` at every state of a run on a literal graph, its pieces read on that graph
(`run_carries`), so the states share their reachability questions. -/
macro "decide_run_valid" : tactic =>
  `(tactic| (intro k _
             unfold Valid FollowersInFinishOrder ClimbBackIsEarliest DoneIffGroupOut
             rw [run_carries]
             revert k
             decide))

set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000

-- every state of the walk on A ↔ B → C and on the loop keeps `Valid`
example : ∀ k ≤ steps abc, Valid (run abc k (start abc)) := by decide_run_valid
example : ∀ k ≤ steps loopy, Valid (run loopy k (start loopy)) := by decide_run_valid
set_option maxRecDepth 100000 in
example : ∀ k ≤ steps seven, Valid (run seven k (start seven)) := by decide_run_valid

/-! ### Kosaraju–Sharir -/

example : kosarajuSharir abc = ⟨[0, 0, 1], [[0, 1], [2]]⟩ := by decide
example : kosarajuSharir seven = ⟨[0, 0, 0, 1, 1, 0, 0], [[0, 2, 1, 6, 5], [3, 4]]⟩ := by decide

/-! ### The condensation: doubled arrows between groups give one arrow -/

set_option maxRecDepth 4000 in
example : (condensation seven (algorithmT seven)).arrows = [(0, 1)] := by decide
example : (condensation doubled (algorithmT doubled)).arrows = [(0, 1)] := by decide
example : (quotientArrows doubled (algorithmT doubled).groupOf) = [(0, 1), (0, 1), (0, 1)] := by
  decide

-- three groups in a chain with a skip arrow: arrows by group id, then member order, then row order
example : algorithmT ⟨4, [(0, 1), (1, 0), (1, 2), (0, 3), (2, 3), (1, 3)]⟩ =
    ⟨[0, 0, 1, 2], [[1, 0], [2], [3]]⟩ := by decide
example : (condensation ⟨4, [(0, 1), (1, 0), (1, 2), (0, 3), (2, 3), (1, 3)]⟩
    ⟨[0, 0, 1, 2], [[1, 0], [2], [3]]⟩).arrows = [(0, 1), (0, 2), (1, 2)] := by decide

/-! ### No vertices -/

example : algorithmT ⟨0, []⟩ = ⟨[], []⟩ ∧ kosarajuSharir ⟨0, []⟩ = ⟨[], []⟩ ∧
    check ⟨0, []⟩ [] = none ∧ TwoSat.twoSat 0 [] = .inr [] := by decide

/-! ### The weak checker's two planted wrong groupings

A → B → A as two groups of one passes a checker that trusts a supplied, empty graph of groups;
the graph of groups derived from the arrows has a cycle, and check 3 turns it away. A grouping
that joins two vertices that do not reach each other passes a checker that skips check 2; check 2
turns it away. -/

example : check ⟨2, [(0, 1), (1, 0)]⟩ [0, 1] = some .quotientCycle := by decide
example : check ⟨2, [(0, 1)]⟩ [0, 0] = some .notStronglyConnected := by decide
example : ¬ IsSccPartition ⟨2, [(0, 1)]⟩ [0, 0] := by decide
-- an unused id fails check 1
example : check abc [0, 0, 2] = some .partition := by decide

/-! ### The library meets its contract, with no hypothesis left -/

example : Contract ops := contract
example : ValidAlong := validAlong
example : AlgorithmTPromise := algorithmTPromise

/-! ### The naive candidates are turned away

A checker that skips check 2 passes a grouping joining vertices that do not reach each other; what
the library's checker owes (`check_eq_none_iff`) turns it away. Numbering groups in the order they
come out (sinks first) gives ids against the arrows; `Ops.condenses` turns it away. A
condensation without marks repeats an arrow for every original arrow between two groups;
`Ops.condenses` turns it away. -/

section Contracts

/-- Checks 1 and 3 only. -/
def skipsCheck2 (g : Digraph) (c : List ℕ) : Option Failure :=
  if !checkPartition g c then some .partition
  else if !checkAcyclic g c then some .quotientCycle else none

example : skipsCheck2 ⟨2, [(0, 1)]⟩ [0, 0] = none ∧ ¬ IsSccPartition ⟨2, [(0, 1)]⟩ [0, 0] := by
  decide

/-- Ids in emission order, sinks first. -/
def emissionOrder (g : Digraph) : Components :=
  ⟨(List.range g.n).map fun v => (final g).emitted v, (final g).groups⟩

example : ¬ IdsTopological abc (emissionOrder abc).groupOf := by decide

/-- Every arrow between two groups, repeats kept. -/
def noMarks (g : Digraph) (r : Components) : Digraph :=
  ⟨r.groups.length, quotientArrows g r.groupOf⟩

example : ¬ ∀ g : Digraph, g.WellFormed → (noMarks g (ops.components g)).arrows.Nodup := by
  intro h
  have := h doubled (by decide)
  revert this
  decide

end Contracts

/-! ### `Valid` has teeth: the classical climb-back rule breaks box invariant 2

The classical rule passes, over an arrow to a vertex still open, that vertex's entry number rather
than its low value. On 0 → 1, 1 → 2, 2 → 0, 1 → 3, 3 → 1, vertex 3 then gets 2 where a retreating
path 3 → 1 → 2 → 0 climbs back to 1. -/

section Classical

/-- 0 → 1, 1 → 2, 2 → 0, 1 → 3, 3 → 1. -/
def climb : Digraph := ⟨4, [(0, 1), (1, 2), (2, 0), (1, 3), (3, 1)]⟩

/-- Come back over an arrow to a vertex still open, passing its entry number. -/
def retreatPre (w : Walk) (v x : ℕ) : Walk :=
  let w := { w with retreats := w.retreats ++ [(v, x)] }
  if w.low x ≠ done climb ∧ w.pre x < w.low v then
    { w with low := Function.update w.low v (w.pre x), lead := Function.update w.lead v false }
  else w

/-- Algorithm T's step with the classical rule on arrows to vertices already entered. -/
def stepClassical (w : Walk) : Walk :=
  match w.path with
  | (v, i) :: rest =>
    match (climb.out v)[i]? with
    | some (x, _) =>
      let w := { w with path := (v, i + 1) :: rest }
      if w.low x = 0 then previsit w x else retreatPre w v x
    | none => step climb w
  | [] => step climb w

/-- `k` classical steps. -/
def runClassical : ℕ → Walk → Walk
  | 0, w => w
  | k + 1, w => runClassical k (stepClassical w)

-- Algorithm T keeps `Valid` throughout; the classical rule breaks it
set_option maxRecDepth 20000 in
example : ∀ k ≤ steps climb, Valid (run climb k (start climb)) := by decide_run_valid
set_option maxRecDepth 20000 in
example : ¬ ∀ k < steps climb, Valid (runClassical k (start climb)) := by decide
-- yet the classical rule still finds the same groups
set_option maxRecDepth 20000 in
example : ((runClassical (steps climb) (start climb)).groups) = (final climb).groups := by decide

end Classical

/-! ### 2-SAT -/

open AlgoDesign.Graphs.TwoSat in
example : twoSat 1 [(0, 0)] = .inr [true] ∧ twoSat 1 [(0, 0), (1, 1)] = .inl 0 ∧
    (twoSat 1 [(0, 1)]).isRight = true := by decide

-- (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁) ∧ (¬x₁ ∨ x₂): x₁ forced, then x₂
open AlgoDesign.Graphs.TwoSat in
example : ∃ a, twoSat 3 [(0, 2), (1, 2), (3, 4)] = .inr a ∧
    Satisfies a [(0, 2), (1, 2), (3, 4)] := ⟨_, rfl, by decide⟩

end AlgoDesignTests.GraphsScc

namespace AlgoDesignTests.GraphsBlocks
open AlgoDesign.Graphs AlgoDesign.Graphs.Blocks AlgoDesign.Graphs.Blocks.Walk

/-- The bowtie a–b, b–c, c–a, b–d, d–e, e–b: two triangles sharing the cut vertex b = 1. -/
def bowtie : Graph := ⟨5, [(0, 1), (1, 2), (2, 0), (1, 3), (3, 4), (4, 1)]⟩

/-- A doubled link 0–1, its copies given in opposite orders, a loop at 1, a bridge 1–2, and a
vertex 3 whose only link is a loop. -/
def twin : Graph := ⟨4, [(0, 1), (1, 0), (1, 1), (1, 2), (3, 3)]⟩

/-- A path of three vertices. -/
def path3 : Graph := ⟨3, [(0, 1), (1, 2)]⟩

/-- A cycle of three vertices. -/
def cycle3 : Graph := ⟨3, [(0, 1), (1, 2), (2, 0)]⟩

/-- Two pieces: a link and a triangle. -/
def apart : Graph := ⟨5, [(0, 1), (2, 3), (3, 4), (4, 2)]⟩

/-- A triple link. -/
def triple : Graph := ⟨2, [(0, 1), (1, 0), (0, 1)]⟩

/-- A doubled link inside a cycle, and a pendant link. -/
def cycleTwin : Graph := ⟨4, [(0, 1), (1, 2), (2, 0), (1, 0), (2, 3)]⟩

/-! ### The answers pinned with the Python's -/

example : blocks bowtie = ⟨[], [1], [some 1, some 1, some 1, some 0, some 0, some 0],
    [[5, 4, 3], [2, 1, 0]], [[1, 3, 4], [0, 1, 2]]⟩ := by decide
example : forest bowtie (blocks bowtie) = ⟨2, [1], [1, 2, 1, 0, 0], [2, 1, 1], [2, 0, 1]⟩ := by
  decide
example : (forest bowtie (blocks bowtie)).separators 0 4 = some [1] ∧
    (forest bowtie (blocks bowtie)).separators 1 4 = some [] := by decide

example : blocks twin = ⟨[3], [1], [some 1, some 1, none, some 0, none],
    [[3], [1, 0], []], [[1, 2], [0, 1], [3]]⟩ := by decide
example : forest twin (blocks twin) = ⟨3, [1], [1, 3, 0, 2], [3, 1, 2, 1], [2, 0, 0, 1]⟩ := by
  decide
example : (forest twin (blocks twin)).separators 0 2 = some [1] ∧
    (forest twin (blocks twin)).separators 0 3 = none ∧
    (forest twin (blocks twin)).separators 3 3 = some [] := by decide

example : blocks path3 = ⟨[0, 1], [1], [some 1, some 0], [[1], [0]], [[1, 2], [0, 1]]⟩ := by
  decide
example : blocks cycle3 = ⟨[], [], [some 0, some 0, some 0], [[2, 1, 0]], [[0, 1, 2]]⟩ := by
  decide
example : (blocks apart).bridges = [0] ∧ (blocks apart).cutVertices = [] ∧
    (blocks apart).blocks.length = 2 := by decide
example : (blocks triple).bridges = [] ∧ (blocks triple).blocks = [[2, 1, 0]] := by decide
example : (blocks cycleTwin).bridges = [4] ∧ (blocks cycleTwin).cutVertices = [2] ∧
    (blocks cycleTwin).blocks = [[4], [2, 1, 3, 0]] := by decide

/-! ### Every answer against the meaning by deletion

The bridges and cut vertices against `IsBridge` and `IsCutVertex`, the blocks against `SameBlock`,
and every separators query against `Separates`. -/

/-- The walk's report and the forest's separators agree with the specification on `g`. -/
def agrees (g : Graph) : Bool :=
  let r := blocks g
  let f := forest g r
  decide (∀ e < g.links.length, e ∈ r.bridges ↔ IsBridge g e) &&
  decide (∀ v < g.n, v ∈ r.cutVertices ↔ IsCutVertex g v) &&
  decide (BlocksAgree g r) && decide (VerticesAgree g r) &&
  (List.range g.n).all fun u => (List.range g.n).all fun v =>
    (f.separators u v).elim (decide (¬ g.Connected u v)) fun l =>
      decide (g.Connected u v ∧ ∀ w < g.n, (w ∈ l ↔ Separates g w u v)) && l.all (· < g.n)

example : agrees bowtie = true := by decide
example : agrees twin = true := by decide
example : agrees path3 = true := by decide
example : agrees cycle3 = true := by decide
example : agrees apart = true := by decide
example : agrees triple = true := by decide
example : agrees cycleTwin = true := by decide

-- a doubled link is never a bridge, in the walk's answer and by proof
example : (blocks triple).bridges = [] ∧ ¬ IsBridge triple 0 :=
  ⟨by decide, not_isBridge_of_twin (a := 0) (b := 1) (f := 2) rfl (Or.inl rfl) (by decide)⟩
-- a loop is in no block and never a bridge
example : (blocks twin).blockOfLink[2]? = some none ∧ ¬ IsBridge twin 2 :=
  ⟨by decide, not_isBridge_of_loop (a := 1) rfl⟩

/-! ### The contract and the invariants, proved for every well-formed graph -/

example : Contract ops := contract
example : Valid (run bowtie 7 (start bowtie)) := valid_along (by decide) 7

/-! ### `Valid` at every step -/

/-- Every state of a run of `g` carries `g`. -/
theorem run_carries (g : Graph) (k : ℕ) : (run g k (start g)).g = g := run_g _ _ _

/-- Decides `Valid` at every state of a run on a literal graph, its pieces read on that graph
(`run_carries`). -/
macro "decide_walk_valid" : tactic =>
  `(tactic| (intro k _
             unfold Valid ClimbBackIsEarliest StackHoldsOpenLinks
             rw [run_carries]
             revert k
             decide))

set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000

example : ∀ k ≤ steps bowtie, Valid (run bowtie k (start bowtie)) := by decide_walk_valid
example : ∀ k ≤ steps twin, Valid (run twin k (start twin)) := by decide_walk_valid
example : ∀ k ≤ steps cycleTwin, Valid (run cycleTwin k (start cycleTwin)) := by
  decide_walk_valid
example : ∀ k ≤ steps apart, Valid (run apart k (start apart)) := by decide_walk_valid

/-! ### Changing one rule

The walk with its row-entry rule and its finishing rule passed in, so the tests can change one
and watch `Valid` or the contract turn it away. -/

section Variants

/-- A rule for taking a row entry, as `look`. -/
abbrev Look := Walk → ℕ → Option ℕ → ℕ → ℕ → Bool → Walk

/-- A rule for a child finishing, as `finishUnder`. -/
abbrev Finish := Walk → ℕ → ℕ → ℕ → Bool → Walk

/-- `step` with the two rules passed in. -/
def stepWith (lk : Look) (fu : Finish) (g : Graph) (w : Walk) : Walk :=
  match w.path with
  | [] =>
    if w.next < g.n then
      if w.entry w.next = 0 then
        enter { w with next := w.next + 1, children := 0 } w.next none w.next
      else { w with next := w.next + 1 }
    else w
  | ⟨v, arr, i⟩ :: rest =>
    match (g.adj v)[i]? with
    | some (x, e) =>
      lk { w with path := ⟨v, arr, i + 1⟩ :: rest, taken := Function.update w.taken v (i + 1) }
        v arr x e rest.isEmpty
    | none =>
      let w' : Walk := { w with path := rest, finished := Function.update w.finished v true }
      match rest, arr with
      | ⟨u, _, _⟩ :: above, some e => fu w' u v e above.isEmpty
      | _, _ => finishRoot w' v

/-- `k` steps with the two rules. -/
def runWith (lk : Look) (fu : Finish) (g : Graph) : ℕ → Walk → Walk
  | 0, w => w
  | k + 1, w => runWith lk fu g k (stepWith lk fu g w)

/-- The answer with the two rules. -/
def blocksWith (lk : Look) (fu : Finish) (g : Graph) : Report :=
  report g (runWith lk fu g (steps g) (start g))

-- with the library's rules it is the library's walk
example : blocksWith look (finishUnder bowtie) bowtie = blocks bowtie := by decide
example : blocksWith look (finishUnder twin) twin = blocks twin := by decide

/-- Tarjan–Zwick's rule from strong components: a link back passes the neighbour's climb-back
number, not its entry number. -/
def lookT : Look := fun w v arr x e isRoot =>
  if x = v ∨ arr = some e then w
  else if w.entry x = 0 then
    enter { w with edges := e :: w.edges,
                   children := if isRoot then w.children + 1 else w.children } x (some e) v
  else if w.entry x < w.entry v then
    { w with edges := e :: w.edges, low := Function.update w.low v (min (w.low v) (w.low x)) }
  else w

-- on the bowtie, vertex 4's link back to b passes b's climb-back number 1, which b took from c:
-- the second triangle climbs above b, so b is not reported and the bowtie is one block
example : (blocksWith lookT (finishUnder bowtie) bowtie).cutVertices = [] ∧
    (blocksWith lookT (finishUnder bowtie) bowtie).blocks = [[5, 4, 3, 2, 1, 0]] := by decide
-- `Valid` turns it away: vertex 4's climb-back number is below the earliest it reaches
example : ¬ ∀ k ≤ steps bowtie, Valid (runWith lookT (finishUnder bowtie) bowtie k
    (start bowtie)) := by decide

/-- The primary sources' rule for simple graphs: skip the vertex the walk came from, not the link
it arrived by. -/
def lookParent : Look := fun w v _ x e isRoot =>
  if x = v ∨ x = w.up v then w
  else if w.entry x = 0 then
    enter { w with edges := e :: w.edges,
                   children := if isRoot then w.children + 1 else w.children } x (some e) v
  else if w.entry x < w.entry v then
    { w with edges := e :: w.edges, low := Function.update w.low v (min (w.low v) (w.entry x)) }
  else w

-- the second copy of the doubled link never climbs back: link 0 is reported as a bridge
example : (blocksWith lookParent (finishUnder twin) twin).bridges = [0, 3] := by decide
example : ¬ ∀ k ≤ steps twin, Valid (runWith lookParent (finishUnder twin) twin k
    (start twin)) := by decide

/-- The finishing rule with the cut test strict, as the bridge test is. -/
def finishStrict (g : Graph) : Finish := fun w u v e uIsRoot =>
  let w : Walk := { w with low := Function.update w.low u (min (w.low u) (w.low v)) }
  let w : Walk :=
    if w.entry u < w.low v then
      let r := popBlock e w.edges
      { w with edges := r.2, blocks := w.blocks ++ [r.1],
               vertices := w.vertices ++ [verticesOf g r.1],
               cut := if uIsRoot then w.cut else Function.update w.cut u true }
    else w
  if w.entry u < w.low v then { w with bridges := w.bridges ++ [e] } else w

/-- The finishing rule with the bridge test not strict, as the cut test is. -/
def finishLoose (g : Graph) : Finish := fun w u v e uIsRoot =>
  let w : Walk := { w with low := Function.update w.low u (min (w.low u) (w.low v)) }
  let w : Walk :=
    if w.entry u ≤ w.low v then
      let r := popBlock e w.edges
      { w with edges := r.2, blocks := w.blocks ++ [r.1],
               vertices := w.vertices ++ [verticesOf g r.1],
               cut := if uIsRoot then w.cut else Function.update w.cut u true }
    else w
  if w.entry u ≤ w.low v then { w with bridges := w.bridges ++ [e] } else w

example : (blocksWith look (finishStrict bowtie) bowtie).cutVertices = [] := by decide
example : (blocksWith look (finishLoose bowtie) bowtie).bridges = [0, 3] := by decide

/-! The promise's (a), `Ops.ReportsFailures`, turns each away. -/

/-- The walk that skips the vertex it came from. -/
def skipsParent (g : Graph) : Report := blocksWith lookParent (finishUnder g) g

/-- The walk with a strict cut test. -/
def strictCut (g : Graph) : Report := blocksWith look (finishStrict g) g

/-- The walk with a bridge test that is not strict. -/
def looseBridge (g : Graph) : Report := blocksWith look (finishLoose g) g

example : ¬ ∀ e, e ∈ (skipsParent twin).bridges ↔ IsBridge twin e := fun h =>
  not_isBridge_of_twin (a := 0) (b := 1) (f := 1) rfl (Or.inr rfl) (by decide)
    ((h 0).mp (by decide))

example : ¬ ∀ v, v ∈ (strictCut bowtie).cutVertices ↔ IsCutVertex bowtie v := fun h => by
  have := (h 1).mpr (by decide)
  revert this
  decide

example : ¬ ∀ e, e ∈ (looseBridge bowtie).bridges ↔ IsBridge bowtie e := fun h => by
  have := (h 3).mp (by decide)
  revert this
  decide

end Variants

end AlgoDesignTests.GraphsBlocks

namespace AlgoDesignTests.GraphsUndo
open AlgoDesign.Graphs AlgoDesign.Graphs.UndoUnionFind

/-! ### Answers, checked by the kernel -/

-- every item alone, the log empty: legal, and an undo changes nothing and answers no
example : (init 3).Valid ∧ (init 3).undo.2 = false ∧ (init 3).undo.1.log = [] ∧
    (init 3).undo.1.count = 3 := by
  decide
-- a merge of two items already together logs an empty entry; one undo takes back that call alone
example : let s := (init 3).unions [(0, 1), (1, 0)]
    s.log = [none, some (1, true)] ∧ s.count = 2 ∧ (s.undo.1.log = [some (1, true)]) ∧
      s.undo.2 = true ∧ s.undo.1.count = 2 ∧ (s.undo.1.joined 0 1) = true := by
  decide
-- a rollback restores the count: three merges, three undos, three groups again
example : let s := (init 3).unions [(0, 1), (1, 2), (0, 2)]
    s.count = 1 ∧ (s.rollback 1).count = 1 ∧ (s.rollback 2).count = 2 ∧
      (s.rollback 3).count = 3 ∧ (s.rollback 3).log = [] := by
  decide
-- on equal ranks the second root goes under the first, whose rank rises; undo lowers it again
example : let s := (init 2).unions [(0, 1)]
    s.uf.parent 1 = 0 ∧ s.uf.rank 0 = 1 ∧ s.log = [some (1, true)] ∧
      s.undo.1.uf.parent 1 = 1 ∧ s.undo.1.uf.rank 0 = 0 := by
  decide
-- lower rank under higher: no rank rises, and the entry says so
example : let s := (init 3).unions [(0, 1), (2, 0)]
    s.uf.parent 2 = 0 ∧ s.uf.rank 0 = 1 ∧ s.log.head? = some (some (2, false)) := by
  decide
-- every state on the way is legal, and rolling back walks through them, last first
example : let s := (init 4).unions [(0, 1), (2, 3), (1, 3), (0, 2)]
    s.Valid ∧ (s.rollback 1).Valid ∧ (s.rollback 2).Valid ∧
      (s.rollback 1).log = ((init 4).unions [(0, 1), (2, 3), (1, 3)]).log ∧
      (s.rollback 2).joined 0 3 = false ∧ (s.rollback 1).joined 0 3 = true := by
  decide
-- nothing compresses: 1 sits two links below the root of four items, and its lookup walks both,
-- as many as log₂ 4, every time
example : let s := (init 4).unions [(0, 1), (2, 3), (3, 1)]
    s.uf.parent 1 = 0 ∧ s.uf.parent 0 = 2 ∧ (findM s 1).time = 2 ∧ Nat.log2 s.uf.n = 2 ∧
      (findM (s.union 1 3).1 1).time = 2 := by
  decide

/-! ### Why the log is in `Valid`

The union-find's own `Valid` and `WellFormed` are not kept by `undo` alone: an entry no merge
wrote, taken back, gives one group too many. `RollbacksLegal` turns such a state away. -/

example : (UnionFind.init 2).Valid ∧ (UnionFind.init 2).WellFormed ∧
    ¬ (⟨UnionFind.init 2, [some (0, false)]⟩ : UndoUnionFind).Valid ∧
    ¬ ((undo ⟨UnionFind.init 2, [some (0, false)]⟩).1.uf.Valid ∧
      (undo ⟨UnionFind.init 2, [some (0, false)]⟩).1.uf.WellFormed) := by
  decide

/-! ### The theorems reject the naive candidates

An undo that skips an empty entry and takes back the merge below it leaves the run one merge
short; `undo_takes_back` turns it away by the count. An undo that puts the root back but forgets
to lower the other root's rank leaves a rank too high; `undo_takes_back` turns it away by the
rank. An undo that puts the link and rank back but not the count reports a group too few;
`undo_takes_back` turns it away by the count. -/

section Contracts

/-- After merging 0 and 1: legal, one group, root 0 of rank 1. -/
private def merged : UndoUnionFind := (init 2).unions [(0, 1)]

example : merged.Valid := by decide

/-- On an empty entry, skips it and takes back the merge below it. -/
private def skipsEmpty (s : UndoUnionFind) : UndoUnionFind × Bool :=
  match s.log with
  | none :: e :: log => (⟨unmerge s.uf e, log⟩, true)
  | _ => undo s

example : ¬ ∀ s : UndoUnionFind, s.Valid → ∀ x < s.uf.n, ∀ y < s.uf.n,
    skipsEmpty (s.union x y).1 = (s, true) := by
  intro h
  have hv : merged.Valid := by decide
  have := congrArg (fun r => r.1.uf.count) (h merged hv 0 (by decide) 0 (by decide))
  revert this
  decide

/-- Puts the root back and restores the count, but never lowers a rank. -/
private def keepsRank (s : UndoUnionFind) : UndoUnionFind × Bool :=
  match s.log with
  | some (c, _) :: log =>
    (⟨{ s.uf with parent := Function.update s.uf.parent c c, count := s.uf.count + 1 }, log⟩,
      true)
  | _ => undo s

example : ¬ ∀ s : UndoUnionFind, s.Valid → ∀ x < s.uf.n, ∀ y < s.uf.n,
    keepsRank (s.union x y).1 = (s, true) := by
  intro h
  have hv : (init 2).Valid := by decide
  have := congrArg (fun r => r.1.uf.rank 0) (h (init 2) hv 0 (by decide) 1 (by decide))
  revert this
  decide

/-- Puts the link and the rank back, but not the count. -/
private def keepsCount (s : UndoUnionFind) : UndoUnionFind × Bool :=
  match s.log with
  | e :: log => (⟨{ unmerge s.uf e with count := s.uf.count }, log⟩, true)
  | [] => (s, false)

example : ¬ ∀ s : UndoUnionFind, s.Valid → ∀ x < s.uf.n, ∀ y < s.uf.n,
    keepsCount (s.union x y).1 = (s, true) := by
  intro h
  have hv : (init 2).Valid := by decide
  have := congrArg (fun r => r.1.uf.count) (h (init 2) hv 0 (by decide) 1 (by decide))
  revert this
  decide

end Contracts

end AlgoDesignTests.GraphsUndo

namespace AlgoDesignTests.GraphsWorkbench
open AlgoDesign.Graphs AlgoDesign.Graphs.Workbench

/-! ### The design project's contract, piece by piece on small plans

Each piece the Python judge checks (`is_each_once` and the rest), decided on two small plans: it
holds of the right answer and fails on a broken one. -/

/-- Tasks 0 and 1 wait for each other, 2 waits for 1, and 3 waits on itself. -/
def plan : Digraph := ⟨4, [(0, 1), (1, 0), (1, 2), (3, 3)]⟩
/-- Task 0 waits on nothing, 1 and 2 wait for each other, 3 waits for 2, and 4 is alone. -/
def chainPlan : Digraph := ⟨5, [(0, 1), (1, 2), (2, 1), (2, 3)]⟩

-- nothing done: 0, 1 and 3 in knots (3 by its own loop), 2 blocked
example : EachOnceOn plan ∅ [] [] [0, 1, 3] [2] ∧ ReadyNowOn plan ∅ [] ∧ LaterOnesOn plan ∅ [] ∧
    KnottedOn plan ∅ [0, 1, 3] ∧ BlockedOnesOn plan ∅ [2] := by decide
-- a task that waits only on itself is in a knot
example : InKnot plan ∅ 3 ∧ ¬ KnottedOn plan ∅ [0, 1] := by decide
-- a task twice, a task missing, a done task listed
example : ¬ EachOnceOn plan ∅ [] [] [0, 1, 3] [2, 2] := by decide
example : ¬ EachOnceOn plan ∅ [] [] [0, 1] [2] := by decide
example : ¬ EachOnceOn plan {0} [0, 1] [2] [3] [] := by decide
-- a blocked task is not later, and the blocked list is not empty
example : ¬ LaterOnesOn plan ∅ [2] ∧ ¬ BlockedOnesOn plan ∅ [] := by decide
-- 0 done: the knot of two is gone, 1 is ready and 2 later
example : EachOnceOn plan {0} [1] [2] [3] [] ∧ ReadyNowOn plan {0} [1] ∧
    LaterOnesOn plan {0} [2] ∧ KnottedOn plan {0} [3] ∧ BlockedOnesOn plan {0} [] := by decide
example : ¬ ReadyNowOn plan {0} [1, 2] := by decide
-- the chain plan: 0 and 4 ready, 1 and 2 in a knot, 3 blocked behind it
example : EachOnceOn chainPlan ∅ [0, 4] [] [1, 2] [3] ∧ ReadyNowOn chainPlan ∅ [0, 4] ∧
    LaterOnesOn chainPlan ∅ [] ∧ KnottedOn chainPlan ∅ [1, 2] ∧
    BlockedOnesOn chainPlan ∅ [3] := by decide
-- chains of real waits, and broken ones: not from a knot, a wait that is not there, empty
example : WaitChain plan ∅ 2 [1, 2] ∧ WaitChain plan ∅ 2 [0, 1, 2] ∧ ¬ WaitChain plan ∅ 2 [2] ∧
    ¬ WaitChain plan ∅ 2 [3, 2] ∧ ¬ WaitChain plan ∅ 2 [] ∧ ¬ WaitChain plan ∅ 1 [0, 1, 2] := by
  decide
example : WaitChain chainPlan ∅ 3 [1, 2, 3] ∧ ¬ WaitChain chainPlan ∅ 3 [0, 1, 2, 3] := by decide
-- why: a chain for a blocked task, nothing for any other
example : ExplainsOn plan ∅ [(2, some [1, 2]), (0, none), (3, none)] := by decide
example : ¬ ExplainsOn plan ∅ [(2, none)] ∧ ¬ ExplainsOn plan ∅ [(0, some [0])] ∧
    ¬ ExplainsOn plan ∅ [(2, some [2])] := by decide
-- the reference's answers pass every piece on both plans
example : let s := reference.build plan ∅
    EachOnceOn plan ∅ (reference.ready s) (reference.later s) (reference.knot s)
      (reference.blocked s) ∧ ReadyNowOn plan ∅ (reference.ready s) ∧
    LaterOnesOn plan ∅ (reference.later s) ∧ KnottedOn plan ∅ (reference.knot s) ∧
    BlockedOnesOn plan ∅ (reference.blocked s) ∧
    ExplainsOn plan ∅ ((List.range 4).map fun v => (v, reference.why s v)) := by decide
set_option maxRecDepth 4000 in
example : let s := reference.build chainPlan ∅
    EachOnceOn chainPlan ∅ (reference.ready s) (reference.later s) (reference.knot s)
      (reference.blocked s) ∧ BlockedOnesOn chainPlan ∅ (reference.blocked s) ∧
    ExplainsOn chainPlan ∅ ((List.range 5).map fun v => (v, reference.why s v)) := by decide

end AlgoDesignTests.GraphsWorkbench
