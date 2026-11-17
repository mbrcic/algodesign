/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Loop
public import AlgoDesign.Flows.Decide

/-!
# Push-relabel: max flow's promise, argued

Push-relabel (Goldberg and Tarjan, "A new approach to the maximum-flow problem", 1988; highest
vertex first, with the gap step and global relabels, as Cherkassky and Goldberg, "On implementing
the push-relabel method for the maximum flow problem", 1997) answers the same question as max flow,
with the same answer: a flow and the source's side of a cut. The library runs it in Rust and
Python; Lean has no procedure for it. So its promise, `PushRelabelPromise`, is stated here on an
abstract answer function, in the shape of max flow's three promise parts (`promise_iff`), and is
argued, not proved.

What is proved is the reason the argument is enough in practice: every answer push-relabel gives can
be checked, and an answer that passes max flow's decidable checks, a flow and a cut of the flow
amount with the source on its side and the sink not, is a largest flow
(`largest_of_passesChecks`); checks passed on every network give the whole promise
(`promise_of_passesChecks`). The library's tests run these checks on every answer.
-/

@[expose] public section

namespace AlgoDesign.Flows.PushRelabel

open AlgoDesign.Flows

/-- **Argued, not proved: push-relabel keeps max flow's promise.** Its answer is a flow, beside it
a cut whose capacity is the flow amount, and so the largest flow: max flow's `Ops.ReturnsAFlow`,
`Ops.CutMatchesFlow` and `Ops.Largest` for the answer function `maxFlow` (`promise_iff`). Argued
from Goldberg and Tarjan's proof, not proved here: the library has no Lean model of the procedure,
whose termination rests on counting pushes and relabels under heights below `2n`, and every answer
it gives is checked instead (`largest_of_passesChecks`). -/
def PushRelabelPromise (maxFlow : Network → Answer) : Prop :=
  (∀ N : Network, N.WellFormed → IsFlow N (maxFlow N).flow) ∧
  (∀ N : Network, N.WellFormed →
    N.source ∈ (maxFlow N).side ∧ N.sink ∉ (maxFlow N).side ∧
      (cutCapacity N (maxFlow N).side : ℤ) = value N (maxFlow N).flow) ∧
  (∀ N : Network, N.WellFormed → ∀ f, IsFlow N f → value N f ≤ value N (maxFlow N).flow)

/-- **The promise has max flow's shape**: for any procedures `o`, it is max flow's three promise
parts for `o`'s answer. -/
theorem promise_iff (o : Ops) :
    PushRelabelPromise o.maxFlow ↔ o.ReturnsAFlow ∧ o.CutMatchesFlow ∧ o.Largest :=
  Iff.rfl

/-- **Max flow's checks on one answer**: the answer's flow is a flow on `N`, the source is on the
cut's side and the sink is not, and the cut's capacity is the flow amount. -/
def PassesChecks (N : Network) (a : Answer) : Prop :=
  IsFlow N a.flow ∧ N.source ∈ a.side ∧ N.sink ∉ a.side ∧
    (cutCapacity N a.side : ℤ) = value N a.flow

instance (N : Network) (a : Answer) : Decidable (PassesChecks N a) := by
  unfold PassesChecks; infer_instance

/-- **An answer that passes the checks is a largest flow**: no flow exceeds its cut, and its cut
has its amount. -/
theorem largest_of_passesChecks {N : Network} (h : N.WellFormed) {a : Answer}
    (ha : PassesChecks N a) : ∀ f, IsFlow N f → value N f ≤ value N a.flow :=
  fun _ hf => (value_le_cutCapacity h hf ha.2.1 ha.2.2.1).trans ha.2.2.2.le

/-- **Checks passed on every network give the whole promise.** -/
theorem promise_of_passesChecks {maxFlow : Network → Answer}
    (hc : ∀ N : Network, N.WellFormed → PassesChecks N (maxFlow N)) :
    PushRelabelPromise maxFlow :=
  ⟨fun N h => (hc N h).1, fun N h => (hc N h).2,
    fun N h => largest_of_passesChecks h (hc N h)⟩

end AlgoDesign.Flows.PushRelabel
