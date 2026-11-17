# SPDX-License-Identifier: Apache-2.0
"""The design project's bench: the truth is the contract's four lists, the reads count what they
say, the plans come back the same from the same seed and hold the awkward cases, and each broken
promise is caught by its own check."""

from __future__ import annotations

import ctypes
import itertools
import sys
import types
from collections.abc import Iterator
from types import SimpleNamespace

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import Digraph, naive
from algodesign.graphs import workbench as wb

N = 2_000
SEED = 0x5EED_6A9B_17C3_0042  # a judge's seed: 64 bits, nowhere in the library


@st.composite
def plans(draw: st.DrawFn) -> wb.Tasks:
    n = draw(st.integers(1, 8))
    task = st.integers(0, n - 1)
    arrows = draw(st.lists(st.tuples(task, task), max_size=14))
    done = draw(st.frozensets(task, max_size=n))
    return wb.Tasks("drawn", n, arrows, done)


def _by_definition(tasks: wb.Tasks) -> tuple[set[int], set[int], set[int], set[int]]:
    """The Lean `Ready`, `Later`, `InKnot` and `Blocked`, read off their definitions with plain
    searches."""
    unfinished = {v for v in range(tasks.n) if v not in tasks.done}
    pending = Digraph(tasks.n, [(a, b) for a, b in tasks.arrows
                                if a in unfinished and b in unfinished])

    def reaches(v: int) -> set[int]:
        return naive.reachable(pending, [v]) | {v}

    ready = {v for v in unfinished if all(a in tasks.done for a, b in tasks.arrows if b == v)}
    knot = {v for v in unfinished if any(w in reaches(v) for w, _ in pending.into[v])}
    later = {v for v in unfinished - ready
             if not any(v in reaches(k) and k in knot for k in range(tasks.n))}
    blocked = {v for v in unfinished - knot if any(v in reaches(k) for k in knot)}
    return ready, later, knot, blocked


@given(plans())
def test_the_truth_is_the_contracts_four_lists(tasks: wb.Tasks) -> None:
    t = wb.truth(tasks)
    assert (t.ready, t.later, t.knot, t.blocked) == _by_definition(tasks)


@given(plans())
def test_the_chapter_candidate_keeps_the_contract(tasks: wb.Tasks) -> None:
    t = wb.truth(tasks)
    c = wb.chapter_candidate(wb.Plan(tasks, wb.Meter(10**9)))
    lists = (c.ready(), c.later(), c.knot(), c.blocked())
    assert wb.check_lists(lists, t) is None
    assert wb.is_explains({v: c.why(v) for v in range(tasks.n)}, t)


def test_the_chapter_candidate_passes_on_every_family() -> None:
    (v,) = wb.judge([wb.Entry("chapter", wb.chapter_candidate)], [SEED], n=N)
    assert v.passes(), wb.report(v)
    assert all(s.asked > 0 for s in v.seeds)
    assert v.worst_reads() < 2 and v.worst_why() == 0


def test_each_family_is_deterministic_and_holds_the_awkward_cases() -> None:
    for family in wb.FAMILIES:
        tasks = wb.generate(family, SEED, N)
        assert tasks == wb.generate(family, SEED, N)
        assert tasks != wb.generate(family, SEED + 1, N)
        t = wb.truth(tasks)
        assert all(len(x) > 0 for x in (t.ready, t.later, t.knot, t.blocked)), family
        assert len(set(tasks.arrows)) < len(tasks.arrows), family  # doubled arrows
        assert any(a == b and a in t.knot for a, b in tasks.arrows), family  # waits on itself
        on_a_cycle = Digraph(tasks.n, tasks.arrows)
        assert any(v in naive.reachable(on_a_cycle, [v]) and v not in t.knot
                   for v in tasks.done), family  # a done task on a cycle


def test_the_long_chains_are_long() -> None:
    tasks = wb.generate("chains", SEED, 100_000)
    c = wb.chapter_candidate(wb.Plan(tasks, wb.Meter(10**9)))
    longest = max(len(c.why(v) or []) for v in c.blocked()[::50])
    assert longest > 5_000


def test_every_read_is_counted() -> None:
    tasks = wb.Tasks("small", 3, [(0, 1), (0, 1), (1, 2)], frozenset({0}))
    meter = wb.Meter(10**9)
    plan = wb.Plan(tasks, meter)
    assert plan.waits_for(1) == [0, 0] and meter.reads == 2
    assert plan.waits_for(0) == [] and meter.reads == 3
    assert plan.waited_by(0) == [1, 1] and meter.reads == 5
    assert plan.is_done(0) and not plan.is_done(2) and meter.reads == 7
    for bad in (-1, 3):
        try:
            plan.waits_for(bad)
        except ValueError:
            continue
        raise AssertionError(bad)


class _Wrong:
    """The chapter candidate with one answer changed."""

    def __init__(self, plan: wb.Plan, change: str) -> None:
        self.c = wb.chapter_candidate(plan)
        self.lists = [self.c.ready(), self.c.later(), self.c.knot(), self.c.blocked()]
        self.change = change
        ready, later, knot, blocked = self.lists
        if change == "each once":
            later.append(later[0])
        elif change == "ready now":
            later.append(ready.pop())
        elif change == "later":
            blocked.append(later.pop())
        elif change == "in a knot":
            blocked.append(knot.pop())

    def ready(self) -> list[int]:
        return self.lists[0]

    def later(self) -> list[int]:
        return self.lists[1]

    def knot(self) -> list[int]:
        return self.lists[2]

    def blocked(self) -> list[int]:
        return self.lists[3]

    def why(self, v: int) -> list[int] | None:
        chain = self.c.why(v)
        return chain[1:] if self.change == "why" and chain else chain


def test_each_broken_promise_is_caught_by_its_own_check() -> None:
    for change in ("each once", "ready now", "later", "in a knot", "why"):
        def make(plan: wb.Plan, change: str = change) -> wb.Candidate:
            return _Wrong(plan, change)

        (v,) = wb.judge([wb.Entry(change, make)], [SEED], ("layered",), n=N)
        assert v.seeds[0].failure == f"broke the promise: {change}", (change, v.seeds[0])


def test_why_is_not_asked_unless_explained() -> None:
    class NoWhy:
        def __init__(self, plan: wb.Plan) -> None:
            self.c = wb.chapter_candidate(plan)
            self.ready, self.later = self.c.ready, self.c.later
            self.knot, self.blocked = self.c.knot, self.c.blocked

    (v,) = wb.judge([wb.Entry("no why", NoWhy)], [SEED], ("crates",), n=N,  # type: ignore[arg-type]
                    explain=False)
    assert v.passes() and "why not asked" in wb.report(v)


def test_a_candidate_that_rereads_the_plan_stops_at_the_budget() -> None:
    class Rereads:
        def __init__(self, plan: wb.Plan) -> None:
            for _ in range(plan.n):
                for v in range(plan.n):
                    plan.waits_for(v)

    (v,) = wb.judge([wb.Entry("rereads", Rereads)], [SEED], ("layered",), n=N)  # type: ignore[arg-type]
    assert v.seeds[0].failure is not None and "budget" in v.seeds[0].failure


def test_a_candidate_that_keeps_every_chain_is_over_memory() -> None:
    class KeepsChains:
        def __init__(self, plan: wb.Plan) -> None:
            self.c = wb.chapter_candidate(plan)
            self.chains = {v: self.c.why(v) for v in self.c.blocked()}
            self.ready, self.later = self.c.ready, self.c.later
            self.knot, self.blocked = self.c.knot, self.c.blocked

        def why(self, v: int) -> list[int] | None:
            return self.chains.get(v)

    (v,) = wb.judge([wb.Entry("keeps chains", KeepsChains)], [SEED], ("chains",),
                    n=20_000)
    s = v.seeds[0]
    assert s.failure is None and s.memory > wb.MEMORY * s.size()
    assert not v.passes() and "numbers per task and arrow" in wb.report(v)


def test_held_counts_what_the_candidate_keeps_and_not_the_plan() -> None:
    tasks = wb.Tasks("small", 3, [(0, 1)], frozenset())
    plan = wb.Plan(tasks, wb.Meter(10**9))

    class Holds:
        def __init__(self) -> None:
            self.plan = plan
            self.rows = [[1, 2], [3]]
            self.flags = bytearray(16)

    assert wb.held(Holds()) == 3 + 2


def test_no_hidden_seed_is_in_the_library() -> None:
    assert SEED not in wb.PRACTICE_SEEDS
    assert len(wb.PRACTICE_SEEDS) == 3


def test_the_truth_comes_after_every_candidates_lists(monkeypatch: pytest.MonkeyPatch) -> None:
    events: list[str] = []

    def make(name: str) -> wb.Make:
        def build(plan: wb.Plan) -> wb.Candidate:
            c = wb.chapter_candidate(plan)
            events.append(f"lists {name}")
            return c
        return build

    truth = wb.truth

    def recorded(tasks: wb.Tasks) -> wb.Truth:
        events.append("truth")
        return truth(tasks)

    monkeypatch.setattr(wb, "truth", recorded)
    wb.judge([wb.Entry("a", make("a")), wb.Entry("b", make("b"))], [SEED], ["layered"], n=N)
    assert events == ["lists a", "lists b", "truth"]


def test_the_order_of_the_why_questions_says_nothing() -> None:
    tasks = wb.generate("chains", SEED, N)
    t = wb.truth(tasks)
    asked = wb._asked(tasks, t, SEED)
    blocked = [v in t.blocked for v in asked]
    assert sum(blocked) == min(wb.ASKED, len(t.blocked))
    half = len(asked) // 2
    assert 0 < sum(blocked[:half]) < half  # blocked and not, mixed through the order


def test_a_task_waiting_only_on_itself_is_in_a_knot() -> None:
    # 0 waits on itself and on nothing else; 1 waits on 0; 2 waits on itself but is done, so its
    # loop holds no one up, and 3, waiting on 2, is ready.
    tasks = wb.Tasks("loops", 4, [(0, 0), (0, 1), (2, 2), (2, 3)], frozenset({2}))
    t = wb.truth(tasks)
    assert (t.knot, t.blocked, t.ready, t.later) == ({0}, {1}, {3}, set())
    assert (t.ready, t.later, t.knot, t.blocked) == _by_definition(tasks)


# What a candidate below keeps in its module's globals, where `held` must still see it.
_STASH: dict[str, list[int]] = {}


class _Lists:
    """The chapter's lists and answers, whatever else the candidate keeps."""

    def __init__(self, plan: wb.Plan) -> None:
        self.inner = wb.chapter_candidate(plan)

    def ready(self) -> list[int]:
        return self.inner.ready()

    def later(self) -> list[int]:
        return self.inner.later()

    def knot(self) -> list[int]:
        return self.inner.knot()

    def blocked(self) -> list[int]:
        return self.inner.blocked()

    def why(self, v: int) -> list[int] | None:
        return self.inner.why(v)


class _KeepsAGlobal(_Lists):
    def __init__(self, plan: wb.Plan) -> None:
        super().__init__(plan)
        _STASH["copy"] = list(range(30 * (plan.n + 5 * plan.n)))


class _KeepsAGenerator(_Lists):
    def __init__(self, plan: wb.Plan) -> None:
        super().__init__(plan)

        def paused() -> Iterator[int]:
            big = list(range(30 * (plan.n + 5 * plan.n)))
            yield len(big)
            yield big[0]

        self.gen = paused()
        next(self.gen)


def _over_memory(make: wb.Make) -> wb.SeedResult:
    (v,) = wb.judge([wb.Entry("hoarder", make)], [SEED], ("layered",), n=N, explain=False)
    return v.seeds[0]


def test_held_sees_a_module_global_and_a_paused_generator() -> None:
    for make in (_KeepsAGlobal, _KeepsAGenerator):
        s = _over_memory(make)
        assert s.failure is None and s.memory > wb.MEMORY * s.size(), make.__name__
    _STASH.clear()


# Candidates that keep a copy of the plan where ordinary code keeps data, each in a module of its
# own, so that what one keeps is not counted against another.
_ROUTES = {
    "a global list sized at import": """
SIZED = [0] * 2_000_000
class Candidate(_Lists):
    def __init__(self, plan):
        super().__init__(plan)
        for i in range(len(SIZED)):
            SIZED[i] = i
""",
    "a mutable default argument": """
def keep(x, store=[]):
    store.append(x)
class Candidate(_Lists):
    def __init__(self, plan):
        super().__init__(plan)
        for _ in range(plan.n):
            keep(list(range(200)))
""",
    "a class attribute of a helper class": """
class Store:
    data = []
class Candidate(_Lists):
    def __init__(self, plan):
        super().__init__(plan)
        Store.data = [list(range(200)) for _ in range(plan.n)]
""",
}


def _route(name: str, source: str) -> wb.Make:
    module = types.ModuleType(f"route_{len(sys.modules)}")
    module.__dict__["_Lists"] = _Lists
    sys.modules[module.__name__] = module
    exec(source, module.__dict__)  # noqa: S102 -- the candidates above, nothing else
    module.Candidate.__module__ = module.__name__
    return module.Candidate  # type: ignore[no-any-return]


@pytest.mark.parametrize("name", list(_ROUTES))
def test_held_counts_a_copy_kept_in_the_module(name: str) -> None:
    s = _over_memory(_route(name, _ROUTES[name]))
    assert s.failure is None and s.memory > wb.MEMORY * s.size(), name


def test_a_filled_function_cache_fails_the_verdict() -> None:
    make = _route("a cache", """
import functools
@functools.lru_cache(maxsize=None)
def rows(v):
    return list(range(200))
class Candidate(_Lists):
    def __init__(self, plan):
        super().__init__(plan)
        for v in range(plan.n):
            rows(v)
""")
    s = _over_memory(make)
    assert s.failure is not None and "cannot count" in s.failure


def test_the_plan_takes_no_attributes() -> None:
    class Candidate(_Lists):
        def __init__(self, plan: wb.Plan) -> None:
            super().__init__(plan)
            plan.extra = list(range(30 * plan.n))  # type: ignore[attr-defined]

    s = _over_memory(Candidate)
    assert s.failure is not None and "AttributeError" in s.failure


def test_held_counts_raw_numbers_in_a_buffer() -> None:
    raw = (ctypes.c_int64 * 1000)()
    assert wb.held(SimpleNamespace(raw=raw)) == 1000


def test_held_counts_a_numpy_array() -> None:
    np = pytest.importorskip("numpy")
    assert wb.held(SimpleNamespace(a=np.zeros(10**6))) == 10**6


def test_an_object_held_cannot_look_into_fails_the_verdict() -> None:
    class KeepsACounter(_Lists):
        def __init__(self, plan: wb.Plan) -> None:
            super().__init__(plan)
            self.ticket = itertools.count()

    s = _over_memory(KeepsACounter)
    assert s.failure == "holds what the bench cannot count: a count"


# --- The Lean's decided cases (`AlgoDesignTests/Graphs.lean`, `Workbench/Decide.lean`) ----------
# The same plans and answers, judged by the Python's pieces, which must say what `decide` says.

# Tasks 0 and 1 wait for each other, 2 waits for 1, and 3 waits on itself.
_PLAN = [(0, 1), (1, 0), (1, 2), (3, 3)]
# Task 0 waits on nothing, 1 and 2 wait for each other, 3 waits for 2, and 4 is alone.
_CHAIN_PLAN = [(0, 1), (1, 2), (2, 1), (2, 3)]


def _decided(n: int, arrows: list[tuple[int, int]], done: frozenset[int] = frozenset()) -> wb.Truth:
    return wb.truth(wb.Tasks("decided", n, arrows, done))


def test_the_lean_s_decided_lists_pass_every_piece() -> None:
    # Nothing done: 0, 1 and 3 in knots (3 by its own loop), 2 blocked.
    t = _decided(4, _PLAN)
    assert wb.check_lists(([], [], [0, 1, 3], [2]), t) is None
    # 0 done: the knot of two is gone, 1 is ready and 2 later.
    t0 = _decided(4, _PLAN, frozenset({0}))
    assert wb.check_lists(([1], [2], [3], []), t0) is None
    # The chain plan: 0 and 4 ready, 1 and 2 in a knot, 3 blocked behind it.
    assert wb.check_lists(([0, 4], [], [1, 2], [3]), _decided(5, _CHAIN_PLAN)) is None


def test_the_lean_s_decided_broken_lists_fail_their_piece() -> None:
    t = _decided(4, _PLAN)
    t0 = _decided(4, _PLAN, frozenset({0}))
    # A task waiting only on itself is in a knot: the knot list without 3 fails.
    assert 3 in t.knot and not wb.is_knotted([0, 1], t)
    # A task twice, a task missing, a done task listed.
    assert not wb.is_each_once(([], [], [0, 1, 3], [2, 2]), t)
    assert not wb.is_each_once(([], [], [0, 1], [2]), t)
    assert not wb.is_each_once(([0, 1], [2], [3], []), t0)
    # A blocked task is not later, and the blocked list is not empty.
    assert not wb.is_later_ones([2], t) and not wb.is_blocked_ones([], t)
    assert not wb.is_ready_now([1, 2], t0)


def test_the_lean_s_decided_wait_chains_and_why_answers() -> None:
    t = _decided(4, _PLAN)
    assert wb.is_wait_chain([1, 2], 2, t) and wb.is_wait_chain([0, 1, 2], 2, t)
    # Not from a knot, a wait that is not there, empty, and ending at another task.
    assert not any(wb.is_wait_chain(c, 2, t) for c in ([2], [3, 2], []))
    assert not wb.is_wait_chain([0, 1, 2], 1, t)
    c = _decided(5, _CHAIN_PLAN)
    assert wb.is_wait_chain([1, 2, 3], 3, c) and not wb.is_wait_chain([0, 1, 2, 3], 3, c)
    # Why: a chain for a blocked task, nothing for any other.
    assert wb.is_explains({2: [1, 2], 0: None, 3: None}, t)
    wrong: list[dict[int, object]] = [{2: None}, {0: [0]}, {2: [2]}]
    assert not any(wb.is_explains(a, t) for a in wrong)


@pytest.mark.parametrize("n,arrows", [(4, _PLAN), (5, _CHAIN_PLAN)])
def test_the_chapter_candidate_passes_the_lean_s_decided_plans(
    n: int, arrows: list[tuple[int, int]]
) -> None:
    tasks = wb.Tasks("decided", n, arrows, frozenset())
    t = wb.truth(tasks)
    cand = wb.chapter_candidate(wb.Plan(tasks, wb.Meter(10**9)))
    assert wb.check_lists((cand.ready(), cand.later(), cand.knot(), cand.blocked()), t) is None
    assert wb.is_explains({v: cand.why(v) for v in range(n)}, t)
