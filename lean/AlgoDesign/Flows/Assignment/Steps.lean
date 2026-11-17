/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.Assignment.Spec

/-!
# Assignment: the steps

Sources: the Flow chapter, "Splitting the rent so nobody envies"; Ahuja, Magnanti and Orlin,
*Network Flows* (1993), §12.4 (one person at a time, p. 471); Kleinberg and Tardos, *Algorithm
Design*, §7.13, (7.65), p. 409.

The people are added one at a time, in row order; all labels start at 0. Person `k`'s step is a
best-first search over the objects on changed costs `cost − label of the person − label of the
object`, from the rows reached so far, starting at person `k`. The library runs it with the labels
fixed during the search (`search`): an array holds each object's distance from person `k` and the
person whose row gave it (`Search.best`, `Search.via`); each pick takes the object not yet visited
with the smallest distance, on a tie a free object first, then the lowest index (`pick`); a held
object is visited and its holder's row may bring other objects closer (`probeVisit`); at the free
object the labels move once (`settle`). The same search with the labels moved after every pick
(`pickSearch`: `update` by the pick's value `δ`, then `visit`) is the form the proofs follow;
`Probe.lean` proves the two agree. The step then walks back from the free object along the
recorded persons, each taking the object that led to it and leaving their old one to the next
(`walkBack`); person `k` takes the first object of the path.
-/

@[expose] public section

namespace AlgoDesign.Flows.Assignment

/-- **A list of `n` entries**, entry `i` being `f i`. -/
def build {α : Type} (n : ℕ) (f : ℕ → α) : List α := (List.range n).map f

/-- **The search of one person's step**, while it runs. -/
structure Search where
  /-- The label of every person. -/
  u : Labels
  /-- The label of every object. -/
  v : Labels
  /-- Each object's best changed cost from the rows reached so far. -/
  best : Labels
  /-- For each object, the person whose row gave its best changed cost. -/
  via : List ℕ
  /-- The objects visited, in order. -/
  visited : List ℕ
deriving DecidableEq, Repr

/-- The changed cost of person `i` and object `j`: the cost less the two labels. -/
def changed (P : Problem) (u v : Labels) (i j : ℕ) : ℤ := P.costAt i j - u.at i - v.at j

/-- **The persons reached**: the new person `cur`, and the holders of the visited objects. -/
def reached (obj : List ℕ) (cur : ℕ) (vis : List ℕ) (r : ℕ) : Bool :=
  decide (r = cur) || (decide (r < obj.length) && decide (obj.getD r 0 ∈ vis))

/-- Whether object `j` comes before object `b` in a pick: a smaller best changed cost, or the same
with `j` free and `b` held. -/
def before (obj : List ℕ) (s : Search) (j b : ℕ) : Bool :=
  decide (s.best.at j < s.best.at b) ||
    (decide (s.best.at j = s.best.at b) && decide (j ∉ obj) && decide (b ∈ obj))

/-- The scan of a pick over the candidates, in index order, `acc` the best so far. -/
def pickFrom (obj : List ℕ) (s : Search) : List ℕ → Option ℕ → Option ℕ
  | [], acc => acc
  | j :: js, none => pickFrom obj s js (some j)
  | j :: js, some b => pickFrom obj s js (if before obj s j b then some j else some b)

/-- **A pick**: the object not yet visited with the smallest best changed cost; on a tie a free
object first, then the lowest index. -/
def pick (P : Problem) (obj : List ℕ) (s : Search) : Option ℕ :=
  pickFrom obj s ((List.range P.n).filter fun j => j ∉ s.visited) none

/-- **The labels move by a pick's value `δ`**: `+ δ` on every person reached, `− δ` on every
object visited, and `− δ` on the best changed cost of every object not visited. -/
def update (P : Problem) (obj : List ℕ) (cur : ℕ) (s : Search) (δ : ℤ) : Search :=
  { s with
    u := build P.n fun r => s.u.at r + if reached obj cur s.visited r then δ else 0
    v := build P.n fun j => s.v.at j - if j ∈ s.visited then δ else 0
    best := build P.n fun j => s.best.at j - if j ∈ s.visited then 0 else δ }

/-- Whether the row of person `i` improves object `j`, not visited in `vis`. -/
def improves (P : Problem) (s : Search) (vis : List ℕ) (i j : ℕ) : Bool :=
  decide (j ∉ vis) && decide (changed P s.u s.v i j < s.best.at j)

/-- **A held object is visited**: its holder is reached, and the holder's row is scanned. -/
def visit (P : Problem) (obj : List ℕ) (s : Search) (j₁ : ℕ) : Search :=
  let i₁ := obj.idxOf j₁
  let vis := s.visited ++ [j₁]
  { s with
    visited := vis
    best := build P.n fun j =>
      if improves P s vis i₁ j then changed P s.u s.v i₁ j else s.best.at j
    via := build P.n fun j => if improves P s vis i₁ j then i₁ else s.via.getD j 0 }

/-- **The search's picks**, at most `fuel` of them: the search after the free object's pick, and
that object; none when the picks run out. -/
def searchLoop (P : Problem) (obj : List ℕ) (cur : ℕ) : ℕ → Search → Option (Search × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match pick P obj s with
    | none => none
    | some j =>
      let s' := update P obj cur s (s.best.at j)
      if j ∈ obj then searchLoop P obj cur fuel (visit P obj s' j) else some (s', j)

/-- **The search at the start of a step**: the labels of the state, and the new person's row as
every object's best changed cost. -/
def startSearch (st : State) : Search :=
  ⟨st.personLabel, st.objectLabel,
    build st.prob.n fun j => changed st.prob st.personLabel st.objectLabel st.obj.length j,
    build st.prob.n fun _ => st.obj.length, []⟩

/-- **The walk back**, at most `fuel` moves, from the free object `j`: the person recorded for `j`
takes it, and their old object is the next; it ends when the new person `cur` takes an object.
Returns the objects of every person and the objects of the path, the free one first. -/
def walkBack (cur : ℕ) (via : List ℕ) : ℕ → List ℕ → ℕ → List ℕ × List ℕ
  | 0, o, _ => (o, [])
  | fuel + 1, o, j =>
    let p := via.getD j 0
    if p = cur then (o.set p j, [j])
    else
      let r := walkBack cur via fuel (o.set p j) (o.getD p 0)
      (r.1, j :: r.2)

/-- **The search of a step, labels moved after every pick**, from the state `st`: the form the
proofs of `SearchKeeps.lean` follow. `search` is the form the library runs; `Probe.lean` proves the
two end with the same labels, path and objects visited. -/
def pickSearch (st : State) : Option (Search × ℕ) :=
  searchLoop st.prob st.obj st.obj.length (st.prob.n + 1) (startSearch st)

/-! ## The search as the library runs it: labels moved once, after the search

During the search the labels stay as they were at its start, and `best` holds each object's
distance from the new person: the cheapest changed cost of a path to it through the people reached.
When the search reaches a free object at distance `top`, the labels move once, as the cheapest
flow's heights: the new person by `top`, every visited object by `top` less its own distance, down,
and its holder by the same, up (`settle`). -/

/-- Whether object `j`, not visited in `vis`, comes closer through person `i₁`'s row, reached by
the visited object `j₁`. -/
def closer (P : Problem) (s : Search) (vis : List ℕ) (j₁ i₁ j : ℕ) : Bool :=
  decide (j ∉ vis) && decide (s.best.at j₁ + changed P s.u s.v i₁ j < s.best.at j)

/-- **A held object is visited, the labels unchanged**: its holder is reached, and each object not
visited may come closer through the holder's row, at the visited object's distance plus the changed
cost. -/
def probeVisit (P : Problem) (obj : List ℕ) (s : Search) (j₁ : ℕ) : Search :=
  let i₁ := obj.idxOf j₁
  let vis := s.visited ++ [j₁]
  { s with
    visited := vis
    best := build P.n fun j =>
      if closer P s vis j₁ i₁ j then s.best.at j₁ + changed P s.u s.v i₁ j else s.best.at j
    via := build P.n fun j => if closer P s vis j₁ i₁ j then i₁ else s.via.getD j 0 }

/-- **The labels move once**, when the search reached the free object `j` at distance `top`: the
new person `cur` gains `top`; every visited object loses `top` less its own distance, and its holder
gains it. -/
def settle (P : Problem) (obj : List ℕ) (cur : ℕ) (s : Search) (j : ℕ) : Search :=
  { s with
    u := build P.n fun r => s.u.at r +
      if r = cur then s.best.at j
      else if reached obj cur s.visited r then s.best.at j - s.best.at (obj.getD r 0) else 0
    v := build P.n fun k => s.v.at k - if k ∈ s.visited then s.best.at j - s.best.at k else 0 }

/-- **The search's picks, the labels fixed**, at most `fuel` of them: the search after the free
object's pick, its labels settled, and that object; none when the picks run out. -/
def probeLoop (P : Problem) (obj : List ℕ) (cur : ℕ) : ℕ → Search → Option (Search × ℕ)
  | 0, _ => none
  | fuel + 1, s =>
    match pick P obj s with
    | none => none
    | some j =>
      if j ∈ obj then probeLoop P obj cur fuel (probeVisit P obj s j)
      else some (settle P obj cur s j, j)

/-- **The search of a step** from the state `st`, as the library runs it. -/
def search (st : State) : Option (Search × ℕ) :=
  probeLoop st.prob st.obj st.obj.length (st.prob.n + 1) (startSearch st)

/-- **The walk back of a step**, after the search ended at the free object `j`: the new person's
place holds `n`, no object, until it takes one. -/
def walk (st : State) (s : Search) (j : ℕ) : List ℕ × List ℕ :=
  walkBack st.obj.length s.via (st.obj.length + 1) (st.obj ++ [st.prob.n]) j

/-- **One step**: the next person is added; the state stays when the search finds no free
object. -/
def step (st : State) : State :=
  match search st with
  | none => st
  | some (s, j) => ⟨st.prob, (walk st s j).1, s.u, s.v⟩

/-- **The state before the first person**: nobody placed, all labels 0. -/
def start (P : Problem) : State := ⟨P, [], build P.n fun _ => 0, build P.n fun _ => 0⟩

/-- **The state after the first `k` people.** -/
def after (P : Problem) : ℕ → State
  | 0 => start P
  | k + 1 => step (after P k)

/-- **The answer**: the state after the last person. -/
def assign (P : Problem) : Answer :=
  ⟨(after P P.n).obj, (after P P.n).personLabel, (after P P.n).objectLabel⟩

/-! ## The trace -/

/-- **One step's record**: the objects settled in order, the free one last; the path, from the
object the new person takes to the free one; and the labels after the step. -/
structure StepTrace where
  /-- The objects the search picked, in order, the free one last. -/
  settled : List ℕ
  /-- The objects of the path, from the new person's to the free one. -/
  path : List ℕ
  /-- The label of every person after the step. -/
  personLabel : Labels
  /-- The label of every object after the step. -/
  objectLabel : Labels
deriving DecidableEq, Repr

/-- The record of the step from the state `st`; none when the search finds no free object. -/
def stepTrace (st : State) : Option StepTrace :=
  match search st with
  | none => none
  | some (s, j) => some ⟨s.visited ++ [j], (walk st s j).2.reverse, s.u, s.v⟩

/-- **The trace of the run**: one record per person, in order. -/
def trace (P : Problem) : List StepTrace :=
  (List.range P.n).filterMap fun k => stepTrace (after P k)

end AlgoDesign.Flows.Assignment
