# SPDX-License-Identifier: Apache-2.0
"""The Graphs chapter's design project: a bench for a dependency analyzer.

A team keeps its tasks, what each waits for, and which tasks are already done. It wants four
lists: the tasks that can start now, those that will be able to start later, those caught in a
knot, and those blocked behind one; and, asked about a blocked task, a chain of real waits from a
task in a knot to it. The problem is fixed here, before any candidate exists. The reader
specifies, an AI implements, and this bench judges:

- `Plan`, the counted cost: a candidate sees the tasks only through it. `waits_for(v)` and
  `waited_by(v)` return one task for each arrow into or out of `v`, and count one read for each
  task returned (one at least, for an empty row); `is_done(v)` counts one. No clock is read.
- `generate`, the plans: three families drawn from a seed the judge keeps. `layered` is a project
  plan built stage by stage; `crates` grows the way a package registry does, so a few tasks are
  waited for by very many; `chains` hangs long chains of waits behind knots. Every family plants
  knots of every size, from a task that waits on itself up, doubled arrows, and done tasks on
  cycles and in the middle of chains. Task numbers are shuffled, so they say nothing about order.
  The library holds only `PRACTICE_SEEDS`, for a candidate to tune on.
- `judge`, the verdict: the truth is computed only after every candidate has built itself and
  given its four lists, and each answer is checked against the contract (`is_each_once`,
  `is_ready_now`, `is_later_ones`, `is_knotted`, `is_blocked_ones`, `is_explains`). The reads made
  while building and listing are held to `READS` per task and arrow, and what the candidate holds
  afterwards (`held`) to `MEMORY` numbers per task and arrow: about 100,000 tasks leave room for
  work and memory that grow with the tasks and arrows, and no more. `why` is asked, after the truth,
  of a sample of tasks, blocked and not, in a shuffled order, so the order says nothing about which
  are blocked; its reads per question are reported. `report` says it in plain words.
- `chapter_candidate`, the chapter's structures as a candidate, for calibration: the strong
  components of the arrows still waiting, and one search forward from the knots that keeps, for
  each task it reaches, the task it was reached from.

The truth is the chapter's too: a task is in a knot when its strong component of the arrows
between unfinished tasks has two members or more, or it waits on itself; blocked when a knot
reaches it and it is in none; ready when no arrow from an unfinished task enters it; later
otherwise.

The counts close the routes through `Plan`, and no more. A candidate that copies the rows reads
each once and then works on its copy uncounted, so the reads count the work only of a candidate
that reads as it goes; `held` counts the copy, not what is done with it, wherever the candidate
keeps it: in itself, in what its functions capture, in a paused generator, in an array of raw
numbers, or in its module's globals, its functions' defaults and caches and its classes' data,
where a container counts in full, filled at import or not.
An object `held` cannot look into fails the verdict rather than count nothing. A candidate that
edits the bench's private state, or reaches through the interpreter, is not caught. Reading the
candidate is the reader's part.

The promise comes first, in Lean: `lean/AlgoDesign/Graphs/Workbench/Spec.lean` states what every
candidate owes (`Contract`). Python only: a tool for the chapter's project, not a structure the
chapter teaches.

The Lean statements behind this module, in `lean/AlgoDesign/Graphs/Workbench/` (specification:
`Workbench/Spec.lean`): `reference_contract`, `valid_build`, `isSome_chain_iff`.
"""

from __future__ import annotations

import functools
import itertools
import math
import sys
import types
from array import array
from collections import deque
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import Protocol

from .._rng import SplitMix64
from .digraph import Digraph
from .naive import reachable
from .scc import strong_components

READS = 20
"""The most reads of the plan a candidate may make while building and listing, per task and per
arrow."""

MEMORY = 20
"""The most numbers a candidate may hold once built, per task and per arrow."""

BUDGET = 100
"""Reads per task and arrow, in one phase, at which the plan stops answering: a candidate past
it fails, and a run that would take hours ends."""

ASKED = 200
"""How many blocked tasks, and how many others, `why` is asked about on each plan."""

PRACTICE_SEEDS = (1, 2, 3)
"""Seeds a candidate may see and tune on. The judge's seeds are its own, and never in here."""

N = 100_000
"""The number of tasks in a judged plan."""


# --- The plans ------------------------------------------------------------------------------


@dataclass(frozen=True)
class Tasks:
    """A plan as the judge holds it: the tasks `0 .. n-1`, the arrows `(a, b)` (`b` waits for
    `a`), and the tasks already done. Never handed to a candidate, which sees `Plan` only."""

    family: str
    n: int
    arrows: list[tuple[int, int]]
    done: frozenset[int]


def _below(rng: SplitMix64, k: int) -> int:
    """A number in `0 .. k-1`."""
    return rng.next_u64() % k


def _distinct(rng: SplitMix64, among: Sequence[int], k: int) -> list[int]:
    """`k` different members of `among`, whose members differ, in the order drawn; all of them
    if it has fewer."""
    picked: list[int] = []
    seen: set[int] = set()
    while len(picked) < min(k, len(among)):
        x = among[_below(rng, len(among))]
        if x not in seen:
            seen.add(x)
            picked.append(x)
    return picked


def _cycle(members: list[int]) -> list[tuple[int, int]]:
    """Arrows around `members`, each waiting for the one before it: a knot. One member waits on
    itself."""
    return [(members[i - 1], members[i]) for i in range(len(members))]


def _knot_sizes(rng: SplitMix64, count: int, largest: int) -> list[int]:
    """Sizes for `count` knots: some of one task, some of two, the rest up to `largest`."""
    sizes = [1, 1, 1, 2, 2, 2]
    sizes += [3 + _below(rng, max(1, largest - 2)) for _ in range(max(0, count - len(sizes)))]
    return sizes[:count]


def _finish(family: str, rng: SplitMix64, n: int, arrows: list[tuple[int, int]],
            done: set[int]) -> Tasks:
    """Double one arrow in a hundred, then shuffle the task numbers and the arrows' order."""
    arrows = arrows + [arrows[_below(rng, len(arrows))] for _ in range(len(arrows) // 100)]
    names = list(range(n))
    for i in range(n - 1, 0, -1):
        j = _below(rng, i + 1)
        names[i], names[j] = names[j], names[i]
    renamed = [(names[a], names[b]) for a, b in arrows]
    for i in range(len(renamed) - 1, 0, -1):
        j = _below(rng, i + 1)
        renamed[i], renamed[j] = renamed[j], renamed[i]
    return Tasks(family, n, renamed, frozenset(names[v] for v in done))


def layered(seed: int, n: int) -> Tasks:
    """A project plan built stage by stage: each task waits for up to five tasks among the 500
    made just before it. Knots are planted among tasks made close together, and the first fifth
    to two fifths of the tasks made are done, with a few more done anywhere, one of them on a
    knot."""
    rng = SplitMix64(seed)
    arrows = []
    for t in range(1, n):
        window = range(max(0, t - 500), t)
        arrows += [(a, t) for a in _distinct(rng, window, _below(rng, 6))]
    knots = []
    for size in _knot_sizes(rng, 30, 50):
        start = _below(rng, n)
        knots.append(_distinct(rng, range(start, min(n, start + 3 * size)), size))
    for members in knots:
        arrows += _cycle(members)
    done = set(range(int(n * (0.2 + 0.2 * rng.next_f64()))))
    done |= {_below(rng, n) for _ in range(n // 200)}
    done.add(knots[-1][0])
    return _finish("layered", rng, n, arrows, done)


def crates(seed: int, n: int) -> Tasks:
    """Dependencies as a package registry grows them. Each new task waits for a few earlier
    ones, mostly picked in proportion to how many already wait for them, so a few are waited for
    by thousands. One knot joins two well-known unfinished tasks and twenty join random ones; about
    a sixth of the tasks, anywhere, are done."""
    rng = SplitMix64(seed)
    arrows = []
    urn: list[int] = []  # a task once when made, and once more each time it is waited for
    for t in range(n):
        wants = 0 if rng.next_f64() < 0.2 else min(40, 1 + int(-3 * math.log(1 - rng.next_f64())))
        for _ in range(wants if t else 0):
            a = urn[_below(rng, len(urn))] if rng.next_f64() < 0.8 else _below(rng, t)
            arrows.append((a, t))
            urn.append(a)
        urn.append(t)
    done = {_below(rng, n) for _ in range(n // 6)}
    waited: dict[int, int] = {}
    for a, _ in arrows:
        waited[a] = waited.get(a, 0) + 1
    popular = sorted((v for v in waited if v not in done), key=lambda v: (-waited[v], v))
    arrows += _cycle(_distinct(rng, popular[100:300], 2))
    for size in _knot_sizes(rng, 20, 10):
        arrows += _cycle(_distinct(rng, range(n), size))
    return _finish("crates", rng, n, arrows, done)


def chains(seed: int, n: int) -> Tasks:
    """Four long chains, an eighth of the tasks each, and the other half of the tasks waiting on
    one to three earlier ones. The first chain starts at a task that waits on itself, the second
    at a knot of two, the third at a knot of one in fifty of the other tasks, and the fourth has a
    knot of ten in its middle. A done task sits halfway down the second chain, a knot of five has
    one member done, and a few of the other tasks are done."""
    rng = SplitMix64(seed)
    length = max(2, n // 8)
    starts = [c * length for c in range(4)]
    arrows = [(t - 1, t) for s in starts for t in range(s + 1, s + length)]
    rest = range(4 * length, n)
    for t in rest:
        arrows += [(a, t) for a in _distinct(rng, range(t), 1 + _below(rng, 3))]
    arrows.append((starts[0], starts[0]))
    others = list(rest)
    two = [starts[1], others[0]]
    size = max(3, len(others) // 50)
    big = [starts[2]] + others[1:size]
    arrows += _cycle(two) + _cycle(big)
    middle = starts[3] + length // 2
    arrows.append((min(middle + 9, starts[3] + length - 1), middle))
    free = others[size:]  # in no knot planted so far
    broken = _distinct(rng, free, 5)
    arrows += _cycle(broken)
    done = {starts[1] + length // 2, broken[0]}
    done |= {free[_below(rng, len(free))] for _ in range(n // 1000)}
    return _finish("chains", rng, n, arrows, done)


FAMILIES: dict[str, Callable[[int, int], Tasks]] = {
    "layered": layered, "crates": crates, "chains": chains}
"""The plan families: each draws a plan from a seed and a number of tasks."""


def generate(family: str, seed: int, n: int = N) -> Tasks:
    """The plan `family` draws from `seed` with `n` tasks, the same every time."""
    return FAMILIES[family](seed, n)


# --- The counted cost ------------------------------------------------------------------------


class Meter:
    """What a candidate has read of the plan, and the read at which the plan stops answering."""

    def __init__(self, budget: int) -> None:
        self.reads = 0
        self.budget = budget
        self.over = False

    def charge(self, reads: int) -> None:
        self.reads += max(1, reads)
        if self.reads > self.budget:
            self.over = True
            raise OverBudget(f"more than {self.budget:,} reads")


class OverBudget(Exception):
    """The plan stopped answering: the candidate read more than `BUDGET` allows."""


class Plan:
    """The plan, as a candidate sees it: how many tasks, and three counted questions. Tasks are
    numbered `0 .. n-1`; an arrow from `a` to `b` means `b` waits for `a`. It takes no attributes
    of the candidate's."""

    __slots__ = ("__meter", "__done", "__into", "__out", "n")

    def __init__(self, tasks: Tasks, meter: Meter) -> None:
        self.__meter = meter
        self.__done = tasks.done
        self.__into: list[list[int]] = [[] for _ in range(tasks.n)]
        self.__out: list[list[int]] = [[] for _ in range(tasks.n)]
        for a, b in tasks.arrows:
            self.__into[b].append(a)
            self.__out[a].append(b)
        self.n = tasks.n

    def __task(self, v: int) -> int:
        if not 0 <= v < self.n:
            raise ValueError(f"no task {v}: tasks are 0..{self.n - 1}")
        return v

    def waits_for(self, v: int) -> list[int]:
        """The tasks `v` waits for, one per arrow into `v`: a task twice if it is waited for
        twice. Counts one read per task returned, and one for an empty row."""
        row = self.__into[self.__task(v)]
        self.__meter.charge(len(row))
        return list(row)

    def waited_by(self, v: int) -> list[int]:
        """The tasks that wait for `v`, one per arrow out of `v`. Counts as `waits_for` does."""
        row = self.__out[self.__task(v)]
        self.__meter.charge(len(row))
        return list(row)

    def is_done(self, v: int) -> bool:
        """Whether task `v` is already done. Counts one read."""
        self.__meter.charge(1)
        return self.__task(v) in self.__done


class Candidate(Protocol):
    """What a candidate offers once built: the four lists, and why a task is blocked."""

    def ready(self) -> list[int]:
        """The tasks that can start now."""
        ...

    def later(self) -> list[int]:
        """The tasks that will be able to start later."""
        ...

    def knot(self) -> list[int]:
        """The tasks caught in a knot."""
        ...

    def blocked(self) -> list[int]:
        """The tasks blocked behind a knot."""
        ...

    def why(self, v: int) -> list[int] | None:
        """For a blocked task, a chain of waits from a task in a knot to it; otherwise `None`."""
        ...


Make = Callable[[Plan], Candidate]
"""How a candidate is built: from the plan, seen through `Plan` only."""


# --- The protected truth ---------------------------------------------------------------------


@dataclass
class Truth:
    """The four lists as sets, and the arrows still holding anyone up. The Lean `Ready`,
    `Later`, `InKnot`, `Blocked` and `pending`."""

    unfinished: set[int]
    ready: set[int]
    later: set[int]
    knot: set[int]
    blocked: set[int]
    pending: set[tuple[int, int]]


def truth(tasks: Tasks) -> Truth:
    """The four lists, which no candidate reaches: the strong components of the arrows between
    unfinished tasks give the knots, and a search forward from the knots the blocked tasks."""
    unfinished = {v for v in range(tasks.n) if v not in tasks.done}
    pending = [(a, b) for a, b in tasks.arrows if a in unfinished and b in unfinished]
    g = Digraph(tasks.n, pending)
    comps = strong_components(g)
    knot = {v for v in unfinished
            if len(comps.groups[comps.group_of[v]]) > 1 or any(w == v for w, _ in g.out[v])}
    blocked = reachable(g, sorted(knot)) - knot
    ready = {v for v in unfinished if not g.into[v]}
    later = unfinished - ready - knot - blocked
    return Truth(unfinished, ready, later, knot, blocked, set(pending))


# --- The contract, piece by piece ------------------------------------------------------------

Lists = tuple[list[int], list[int], list[int], list[int]]
"""A candidate's four lists: ready, later, knot, blocked."""


def is_each_once(lists: Lists, t: Truth) -> bool:
    """Every unfinished task is in exactly one of the four lists, and no list holds anything
    else. The Lean `Ops.EachOnce`."""
    every = [v for one in lists for v in one]
    return (all(type(v) is int for v in every) and len(every) == len(t.unfinished)
            and set(every) == t.unfinished)


def is_ready_now(ready: list[int], t: Truth) -> bool:
    """The ready list holds exactly the unfinished tasks whose every wait is done. The Lean
    `Ops.ReadyNow`."""
    return set(ready) == t.ready


def is_later_ones(later: list[int], t: Truth) -> bool:
    """The later list holds exactly the tasks not ready now with nothing before them in a knot.
    The Lean `Ops.LaterOnes`."""
    return set(later) == t.later


def is_knotted(knot: list[int], t: Truth) -> bool:
    """The knot list holds exactly the tasks that wait on themselves, directly or through other
    unfinished tasks. The Lean `Ops.Knotted`."""
    return set(knot) == t.knot


def is_blocked_ones(blocked: list[int], t: Truth) -> bool:
    """The blocked list holds exactly the tasks in no knot that a knot reaches. The Lean
    `Ops.BlockedOnes`."""
    return set(blocked) == t.blocked


def is_wait_chain(chain: object, v: int, t: Truth) -> bool:
    """`chain` starts at a task in a knot, ends at `v`, and each step is an arrow between two
    unfinished tasks. The Lean `WaitChain`."""
    return (isinstance(chain, list) and len(chain) > 0 and all(type(x) is int for x in chain)
            and chain[0] in t.knot and chain[-1] == v
            and all((a, b) in t.pending for a, b in itertools.pairwise(chain)))


def is_explains(answers: dict[int, object], t: Truth) -> bool:
    """Each blocked task asked about got a chain of real waits from a knot, and every other task
    asked about got `None`. The Lean `Ops.Explains`, on the tasks asked."""
    return all(is_wait_chain(a, v, t) if v in t.blocked else a is None
               for v, a in answers.items())


def check_lists(lists: Lists, t: Truth) -> str | None:
    """The first piece of the contract the four lists break, by name, or `None`."""
    ready, later, knot, blocked = lists
    checks = [("each once", is_each_once(lists, t)), ("ready now", is_ready_now(ready, t)),
              ("later", is_later_ones(later, t)), ("in a knot", is_knotted(knot, t)),
              ("blocked", is_blocked_ones(blocked, t))]
    return next((name for name, ok in checks if not ok), None)


# --- Memory ----------------------------------------------------------------------------------

_SKIPPED = (type, types.ModuleType, types.BuiltinFunctionType, Plan, Meter)
_WORD = 1 << 63
_PLAIN = (int, float, complex, str, bytes, bytearray, type(None))
# Plain values no candidate can fill: a module's own count less these is what the candidate added.
_FIXED = (int, float, complex, str, bytes, type(None))
# Objects with nothing inside them to count beyond themselves.
_SMALL = (range, slice, object, type(Ellipsis), type(NotImplemented))


class Uncountable(Exception):
    """The candidate holds an object `held` cannot look into."""


def _class_data(cls: type) -> list[object]:
    """A class's own data: its values but `__`-names, methods and descriptors."""
    return [v for k, v in vars(cls).items() if not k.startswith("__") and not callable(v)
            and not isinstance(v, (property, staticmethod, classmethod,
                                   types.MemberDescriptorType, types.GetSetDescriptorType))]


def _globals(module: str) -> list[object]:
    """A module's global data: its global values but its own `__`-names and modules; for a
    function or class defined in it, what the function keeps (defaults, captured values, a cache)
    and the class's own data."""
    m = sys.modules.get(module)
    if m is None:
        return []
    data: list[object] = []
    for k, v in vars(m).items():
        if k.startswith("__") or isinstance(v, types.ModuleType):
            continue
        if not callable(v):
            data.append(v)
        elif getattr(v, "__module__", None) == module:
            data.extend(_class_data(v) if isinstance(v, type) else [v])
    return data


def _parts(obj: object) -> list[object] | None:
    """What `obj` holds: a container's items, a function's captured values and defaults, a
    paused generator's local values, an instance's attributes and its class's data; `None` for
    an object that shows none of these."""
    if isinstance(obj, dict):
        return [*obj.keys(), *obj.values()]
    if isinstance(obj, (list, tuple, set, frozenset, deque, array, memoryview)):
        return list(obj)
    if isinstance(obj, types.FunctionType):
        cells = []
        for cell in obj.__closure__ or ():
            try:
                cells.append(cell.cell_contents)
            except ValueError:  # a cell not filled yet
                pass
        return [*cells, *(obj.__defaults__ or ()), *(obj.__kwdefaults__ or {}).values()]
    if isinstance(obj, types.MethodType):
        return [obj.__self__, obj.__func__]
    if isinstance(obj, functools.partial):
        return [obj.func, *obj.args, *obj.keywords.values()]
    if isinstance(obj, (types.GeneratorType, types.CoroutineType, types.AsyncGeneratorType)):
        frame = getattr(obj, "gi_frame", None) or getattr(obj, "cr_frame", None) or getattr(
            obj, "ag_frame", None)
        return list(frame.f_locals.values()) if frame is not None else []
    slots = [name for cls in type(obj).__mro__ for name in getattr(cls, "__slots__", ())]
    if not hasattr(obj, "__dict__") and not slots:
        return None
    parts = list(vars(obj).values()) if hasattr(obj, "__dict__") else []
    parts += [getattr(obj, name) for name in slots if hasattr(obj, name)]
    for cls in type(obj).__mro__:
        if cls is not object:
            parts.extend(v for k, v in vars(cls).items()
                         if not k.startswith("__") and not callable(v)
                         and not isinstance(v, (property, staticmethod, classmethod,
                                                types.MemberDescriptorType,
                                                types.GetSetDescriptorType)))
    return parts


def _size(item: object) -> int:
    """How many numbers a plain value takes: one for a number or `None`, one per 64 bits of a
    larger integer, one per eight characters or bytes."""
    if isinstance(item, int) and not -_WORD <= item < _WORD:
        return -(-item.bit_length() // 64)
    if isinstance(item, (str, bytes, bytearray)):
        return max(1, -(-len(item) // 8))
    return 1


def _count(roots: list[object], seen: set[int], strict: bool = True) -> int:
    """How many numbers `roots` hold between them, each object not in `seen` counted once and
    added to it. An object it cannot look into raises `Uncountable` when `strict`, and otherwise
    counts its own size, one per 8 bytes."""
    todo = list(roots)
    count = 0
    while todo:
        obj = todo.pop()
        if isinstance(obj, _PLAIN):
            count += _size(obj)
            continue
        if id(obj) in seen or isinstance(obj, _SKIPPED):
            continue
        seen.add(id(obj))
        if isinstance(obj, functools._lru_cache_wrapper):
            if obj.cache_info().currsize > 0:
                raise Uncountable("a function's cache")
            todo.append(obj.__wrapped__)
            continue
        if not isinstance(obj, (array, memoryview)):
            try:  # raw numbers in a buffer, a numpy array's say: one per 8 bytes
                count += max(1, -(-memoryview(obj).nbytes // 8))  # type: ignore[arg-type]
                continue
            except TypeError:
                pass
        parts = _parts(obj)
        if parts is None:
            if type(obj) in _SMALL:
                count += 1
                continue
            if strict:
                raise Uncountable(f"a {type(obj).__name__}")
            count += max(1, sys.getsizeof(obj) // 8)
            continue
        todo.extend(parts)
    return count


def held(candidate: object, before: int = 0, modules: Sequence[str] = ()) -> int:
    """How many numbers the candidate holds. Every number, `None` and string it reaches counts
    once per place it is held, in containers, arrays, buffers, what its functions capture and its
    paused generators; the plan it was handed, functions, classes and modules count nothing. With
    `modules` (the module that builds the candidate, whose globals it may keep its data in),
    their global data counts too, with what their functions keep and their classes' data, less
    `before`, the plain numbers and strings among their globals before the candidate was built;
    a list, dict or other container counts in full, filled or not. Raises `Uncountable` on an
    object it cannot look into among what the candidate reaches, and on a filled function
    cache."""
    seen: set[int] = set()
    own = _count([candidate], seen)
    return own + _count([v for m in modules for v in _globals(m)], seen, strict=False) - before


# --- The verdict -----------------------------------------------------------------------------


@dataclass
class SeedResult:
    """One candidate on one plan."""

    family: str
    seed: int
    n: int
    arrows: int
    reads: int = 0
    memory: int = 0
    why_reads: float = 0.0
    asked: int = 0
    failure: str | None = None

    def size(self) -> int:
        """Tasks plus arrows: what reads and memory are counted against."""
        return self.n + self.arrows

    def passes(self) -> bool:
        return (self.failure is None and self.reads <= READS * self.size()
                and self.memory <= MEMORY * self.size())


@dataclass
class Verdict:
    """One candidate on every plan."""

    name: str
    seeds: list[SeedResult] = field(default_factory=list)

    def passes(self) -> bool:
        return bool(self.seeds) and all(s.passes() for s in self.seeds)

    def worst_reads(self) -> float:
        """The most reads per task and arrow on any plan."""
        return max((s.reads / s.size() for s in self.seeds), default=0.0)

    def worst_memory(self) -> float:
        """The most numbers held per task and arrow on any plan."""
        return max((s.memory / s.size() for s in self.seeds), default=0.0)

    def worst_why(self) -> float:
        """The most reads per `why` question on any plan."""
        return max((s.why_reads for s in self.seeds), default=0.0)


@dataclass
class Entry:
    """A candidate to judge: its name and how it is built."""

    name: str
    make: Make


def _asked(tasks: Tasks, t: Truth, seed: int) -> list[int]:
    """The tasks `why` is asked about: up to `ASKED` blocked ones and `ASKED` others, done tasks
    among them, drawn from the judge's seed, then shuffled together."""
    rng = SplitMix64(seed ^ 0x5A5A_A5A5)
    blocked = sorted(t.blocked)
    others = [v for v in range(tasks.n) if v not in t.blocked]
    asked = _distinct(rng, blocked, ASKED) + _distinct(rng, others, ASKED)
    return [asked[i] for i in _distinct(rng, range(len(asked)), len(asked))]


@dataclass
class _Run:
    """One candidate on one plan while it is judged: its meter, and once built, the candidate
    and its four lists."""

    result: SeedResult
    meter: Meter
    candidate: Candidate | None = None
    lists: Lists = ([], [], [], [])
    modules: tuple[str, ...] = ()
    before: int = 0


def _failed(run: _Run, e: Exception | None) -> None:
    """Set `failure` for a candidate that raised `e`, or read past its budget (even if it caught
    the plan's refusal)."""
    if e is not None:
        run.result.failure = f"raised {type(e).__name__}: {e}"
    if run.meter.over:
        run.result.failure = f"read the plan past its budget of {BUDGET} per task and arrow"


def _build(entry: Entry, tasks: Tasks, run: _Run) -> None:
    """Build the candidate and take its four lists, or set `failure`. The bench knows nothing
    true yet."""
    try:
        module = getattr(entry.make, "__module__", None)
        run.modules = (module,) if isinstance(module, str) else ()
        run.before = _count([v for m in run.modules for v in _globals(m) if isinstance(v, _FIXED)],
                            set(), strict=False)
        run.candidate = entry.make(Plan(tasks, run.meter))
        c = run.candidate
        run.lists = (list(c.ready()), list(c.later()), list(c.knot()), list(c.blocked()))
        run.result.reads = run.meter.reads
    except Exception as e:  # noqa: BLE001 -- a candidate that fails, fails its verdict
        _failed(run, e)
    _failed(run, None)


def _explain(run: _Run, asked: list[int], explain: bool) -> dict[int, object]:
    """Ask the built candidate why about `asked`, then count what it holds; its answers, or set
    `failure`."""
    answers: dict[int, object] = {}
    run.meter.reads = 0
    try:
        if explain:
            answers = {v: run.candidate.why(v) for v in asked} if run.candidate else {}
            run.result.why_reads = run.meter.reads / max(1, len(asked))
            run.result.asked = len(asked)
        run.result.memory = held(run.candidate, run.before, run.modules)
    except Uncountable as e:
        run.result.failure = f"holds what the bench cannot count: {e}"
    except Exception as e:  # noqa: BLE001 -- a candidate that fails, fails its verdict
        _failed(run, e)
    _failed(run, None)
    return answers


def judge(entries: Sequence[Entry], seeds: Sequence[int],
          families: Sequence[str] = tuple(FAMILIES), n: int = N,
          explain: bool = True) -> list[Verdict]:
    """Every candidate on the plan each family draws from each seed, each with a plan of its own.
    Every candidate builds itself and gives its four lists; only then is the truth computed and
    the tasks to ask about drawn, and `why` is asked of each candidate still standing, in a
    shuffled order. With `explain` false, `why` is not asked."""
    verdicts = [Verdict(e.name) for e in entries]
    for family in families:
        for seed in seeds:
            tasks = generate(family, seed, n)
            runs = []
            for entry, verdict in zip(entries, verdicts, strict=True):
                result = SeedResult(family, seed, tasks.n, len(tasks.arrows))
                verdict.seeds.append(result)
                run = _Run(result, Meter(BUDGET * result.size()))
                _build(entry, tasks, run)
                runs.append(run)
            t = truth(tasks)
            asked = _asked(tasks, t, seed)
            for run in runs:
                if run.result.failure is not None:
                    continue
                answers = _explain(run, asked, explain)
                if run.result.failure is not None:
                    continue
                wrong = check_lists(run.lists, t)
                if wrong is None and explain and not is_explains(answers, t):
                    wrong = "why"
                if wrong is not None:
                    run.result.failure = f"broke the promise: {wrong}"
    return verdicts


def report(verdict: Verdict) -> str:
    """The verdict in plain words: passes or not, and why, with the worst plan's numbers."""
    if not verdict.seeds:
        return f"{verdict.name}: not judged."
    failed = [s for s in verdict.seeds if s.failure is not None]
    if failed:
        s = failed[0]
        return f"{verdict.name}: fails on {s.family} seed {s.seed}: {s.failure}."
    reasons = []
    if any(s.reads > READS * s.size() for s in verdict.seeds):
        reasons.append(f"more than {READS} reads per task and arrow")
    if any(s.memory > MEMORY * s.size() for s in verdict.seeds):
        reasons.append(f"more than {MEMORY} numbers per task and arrow")
    head = "passes" if not reasons else "fails: " + ", ".join(reasons)
    asked = max(s.asked for s in verdict.seeds)
    why = (f"; why asked of {asked} tasks a plan, {verdict.worst_why():.1f} reads a question on "
           f"its worst plan" if asked else "; why not asked")
    return (f"{verdict.name}: {head}. {verdict.worst_reads():.2f} reads per task and arrow on its "
            f"worst plan (at most {READS}); {verdict.worst_memory():.2f} numbers held per task "
            f"and arrow (at most {MEMORY}){why}; every answer kept the contract.")


# --- The chapter's structures as a candidate -------------------------------------------------


class _Chapter:
    """The chapter's structures: the arrows between unfinished tasks, read once; their strong
    components (Algorithm T); one search forward from every knot at once, keeping for each task
    it reaches the task it came from."""

    def __init__(self, plan: Plan) -> None:
        unfinished = [not plan.is_done(v) for v in range(plan.n)]
        pending = [(v, w) for v in range(plan.n) if unfinished[v]
                   for w in plan.waited_by(v) if unfinished[w]]
        g = Digraph(plan.n, pending)
        comps = strong_components(g)
        knot = [unfinished[v] and (len(comps.groups[comps.group_of[v]]) > 1
                                   or any(w == v for w, _ in g.out[v])) for v in range(plan.n)]
        self.came_from = [-1] * plan.n  # for a blocked task, the task it was reached from
        todo = deque(v for v in range(plan.n) if knot[v])
        while todo:
            v = todo.popleft()
            for w, _ in g.out[v]:
                if not knot[w] and self.came_from[w] == -1:
                    self.came_from[w] = v
                    todo.append(w)
        self.lists: Lists = ([], [], [], [])
        for v in range(plan.n):
            if not unfinished[v]:
                continue
            which = (2 if knot[v] else 3 if self.came_from[v] != -1 else 0 if not g.into[v]
                     else 1)
            self.lists[which].append(v)

    def ready(self) -> list[int]:
        return self.lists[0]

    def later(self) -> list[int]:
        return self.lists[1]

    def knot(self) -> list[int]:
        return self.lists[2]

    def blocked(self) -> list[int]:
        return self.lists[3]

    def why(self, v: int) -> list[int] | None:
        if not 0 <= v < len(self.came_from) or self.came_from[v] == -1:
            return None
        chain = [v]
        while self.came_from[chain[-1]] != -1:
            chain.append(self.came_from[chain[-1]])
        return chain[::-1]


def chapter_candidate(plan: Plan) -> Candidate:
    """The chapter's structures as a candidate: it reads every task's row once, and answers why
    by walking back the tasks each was reached from."""
    return _Chapter(plan)
