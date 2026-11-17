/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.Spec
public import AlgoDesign.Flows.MaxFlow.Loop
public import AlgoDesign.Flows.MaxFlow.RulesBasic
public import AlgoDesign.Flows.MaxFlow.EdmondsKarp
public import AlgoDesign.Flows.MaxFlow.Dinic
public import AlgoDesign.Flows.MaxFlow.CapacityScaling

/-! Max flow: the loop around a path rule, and the three rules the library ships. The contract is
in `MaxFlow/Spec.lean`; the loop and its one proof in `MaxFlow/Loop.lean`; Edmonds–Karp's, Dinic's
and capacity scaling's rules in their own files. -/

@[expose] public section

namespace AlgoDesign.Flows.MaxFlow

/-! ## The library's max flow meets its contract

`Contract` in `MaxFlow/Spec.lean` is the part of the contract that Lean checks; the library's
procedures are the loop around Dinic's rule, its default. -/

/-- The library's procedures: the loop around Dinic's rule. -/
def ops : Ops := dinic.ops dinic_promise

/-- **The library's max flow meets the max-flow contract.** -/
theorem contract : Contract ops := PathRule.contract dinic_promise dinic_bound

/-- With Edmonds–Karp's rule the loop meets the contract too. -/
theorem contract_edmondsKarp : Contract (edmondsKarp.ops edmondsKarp_promise) :=
  PathRule.contract edmondsKarp_promise edmondsKarp_bound

end AlgoDesign.Flows.MaxFlow
