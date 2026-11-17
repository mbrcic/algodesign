# SPDX-License-Identifier: Apache-2.0
"""The Flow chapter: `network`, vertices with arrows of limited capacity, a source and a sink;
`residual`, the residual graph of a flow, each arrow paired with its reverse arrow; `max_flow`, the
loop around a path rule, answering with a largest flow and a cut of the same amount; and the three
path rules, `Dinic` (the default: a blocking flow through the layers of one search per round),
`EdmondsKarp` (one path of the fewest arrows per round) and `CapacityScaling` (one path whose every
arrow has residual capacity at least a threshold, halved when none is left); `DinicScaling`, Dinic's
rounds under capacity scaling's threshold, not taught; and `min_cost_flow`,
the cheapest flow of a given amount, the same loop with the path rule "cheapest"; and
`push_relabel`, max flow's answer by heights instead of paths, highest vertex first; and
`assignment`, the least-cost assignment of a square table, one person at a time, with labels that
prove it; and `max_matching`, a maximum matching of people with objects by max flow, with a cover as
large and, when someone stays unmatched, a blocked group. `naive` holds the slow references the
tests compare against; import it as `algodesign.flows.naive`. As in the paths package, `max_flow`,
`min_cost_flow`, `push_relabel` and `assignment` are the modules; their functions of the same name
are imported from them, as `from algodesign.flows.max_flow import max_flow`. `workbench` is the
chapter's design project's bench, not a structure; import it as `algodesign.flows.workbench`.
"""

from __future__ import annotations

from . import assignment, max_flow, min_cost_flow, push_relabel
from .assignment import Assignment, AssignmentStep, assignment_with_steps
from .capacity_scaling import CapacityScaling
from .dinic import Dinic
from .dinic_scaling import DinicScaling
from .edmonds_karp import EdmondsKarp
from .matching import BlockedGroup, Matching, max_matching, max_matching_with_rounds
from .max_flow import MaxFlow, PathRule, max_flow_with_rounds
from .min_cost_flow import MinCostFlow, MinCostRound, min_cost_flow_with_rounds
from .network import Network
from .residual import Augmentation, Residual

__all__ = [
    "Assignment", "AssignmentStep", "assignment", "assignment_with_steps",
    "Augmentation", "CapacityScaling", "Dinic", "DinicScaling", "EdmondsKarp", "MaxFlow",
    "MinCostFlow",
    "MinCostRound", "Network", "PathRule", "Residual", "max_flow", "max_flow_with_rounds",
    "min_cost_flow", "min_cost_flow_with_rounds", "push_relabel",
    "BlockedGroup", "Matching", "max_matching", "max_matching_with_rounds",
]
