# SPDX-License-Identifier: Apache-2.0
"""The Paths chapter's design project: a bench for a trip planner with a battery.

A delivery rider on a battery bike asks for the quickest trip from one place to another that never
runs the battery flat. The problem is fixed here, before any candidate exists. The reader
specifies, an AI implements, and this bench judges:

- `Town`, the counted cost: a candidate sees the town only through it. `streets_from(p)` and
  `streets_to(p)` return one row for each street out of or into `p`, and count one read for each
  row returned (one at least, for an empty row); `has_socket(p)` counts one. No clock is read.
  The reads made while the candidate builds itself are counted apart from the reads each trip
  makes, and a trip's reads are the bench's measure of the time to answer it.
- `generate`, the towns: two families drawn from a seed the judge keeps. `hills` is a grid of
  streets over smooth hills, most of them two-way; `sprawl` joins scattered places to their
  nearest neighbors. In both, a street's energy is a distance part plus the height it climbs, so
  it is negative downhill, and its minutes grow with its length and its climb. A few places
  have sockets. Every town plants a place no street leads to, and a hilltop whose every street in
  climbs more than a full battery holds, so some trips have no answer. Place numbers are shuffled.
  The bench holds only `PRACTICE_SEEDS`, for a candidate to tune on.
- `judge`, the verdict: the truth is computed only after every candidate has built itself and
  answered every trip, and each answer is checked against the contract (`is_real_trip`,
  `is_never_flat`, `is_none_quicker`, `is_says_none`). A trip's reads are held to `READS` per
  state and ride of the town (a state is a place at a battery level; a ride is a street from a
  state), and what the candidate holds after the last trip (`held`) to `MEMORY` numbers per state
  and ride. `report` says it in plain words.
- `chapter_candidate`, the chapter's method as a candidate, for calibration: Dijkstra's algorithm
  on the states, reading a place's streets each time it settles a state there.

The truth is the chapter's too: Dijkstra's algorithm on the states (`quickest`), with the battery's
level part of the state, checked in the tests on small towns against every trip that passes no
state twice.

The counts close the routes through `Town`, and no more. A candidate that copies the streets while
it builds reads each once and then works on its copy uncounted, so a trip's reads count its work
only for a candidate that reads as it goes; `held` counts the copy, not what is done with it,
wherever the candidate keeps it: in itself, in what its functions capture, in a paused generator,
in an array of raw numbers, or in its module's globals, its functions' defaults and caches and its
classes' data. An object `held` cannot look into fails the verdict rather than count nothing. A
candidate that edits the bench's private state, or reaches through the interpreter, is not caught.
Reading the candidate is the reader's part.

The promise comes first, in Lean: `lean/AlgoDesign/Paths/Workbench/Spec.lean` states what every
candidate owes (`Contract`), and `Workbench/Decide.lean` decides each piece on one trip. Each check
below names its Lean piece. Python only: a tool for the chapter's project, not a structure the
chapter teaches.

The Lean definitions behind this module, in `lean/AlgoDesign/Paths/Workbench/`: `Street`, `Town`,
`Town.WellFormed`, `Town.passes`, `Town.minutesFrom`, `Town.IsTrip`, `Town.NeverFlat`,
`Town.tripMinutes`, `RealTripOn`, `NoneQuickerOn`, `SaysNoneOn`, `Contract`. The Lean statements
behind this module, in `lean/AlgoDesign/Paths/Workbench/`: `exists_trip_iff`, `noneQuicker_iff`,
`Ops.realTrip_iff`, `Ops.noneQuicker_iff`, `Ops.saysNone_iff`.
"""

from __future__ import annotations

import functools
import heapq
import math
import sys
import types
from array import array
from collections import deque
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import Protocol

from .._rng import SplitMix64

READS = 20
"""The most reads of the town a trip may make, per state and per ride of the town."""

MEMORY = 20
"""The most numbers a candidate may hold after the last trip, per state and per ride."""

BUDGET = 40
"""Reads per state and ride, in one trip or in the build, at which the town stops answering: a
candidate past it fails, and a run that would take hours ends."""

ASKED = 8
"""How many trips each town is asked: six from a place drawn at random to a place drawn among those
its streets reach, one to the place no street leads to, and one to the hilltop."""

PRACTICE_SEEDS = (1, 2, 3)
"""Seeds a candidate may see and tune on. The judge's seeds are its own, and never in here."""

N = 10_000
"""The number of places in a judged town."""

FULL = 100
"""The battery's full level in a judged town; empty is 0."""

CHARGE = "charge"
"""The step that charges one level at the socket where the bike stands."""


def _below(rng: SplitMix64, k: int) -> int:
    """A draw from `0 .. k-1`."""
    return rng.next_u64() % k


# --- The towns ------------------------------------------------------------------------------


@dataclass(frozen=True)
class Street:
    """A one-way street, as the judge holds it. The Lean `Street`."""
    source: int
    target: int
    minutes: int
    energy: int


@dataclass(frozen=True)
class TownData:
    """A town as the judge holds it: places `0 .. n-1`, the streets, the places with a socket, the
    battery's full level, and the minutes a socket takes to add a level. The Lean `Town`. Never
    handed to a candidate, which sees `Town` only."""
    family: str
    seed: int
    n: int
    streets: tuple[Street, ...]
    sockets: frozenset[int]
    full: int
    charge_minutes: int
    trips: tuple[tuple[int, int], ...]  # the trips the judge asks, start and goal

    def well_formed(self) -> bool:
        """The Lean `Town.WellFormed`: every street joins two places, at most one street leads
        from one place to another, every socket is at a place."""
        pairs = [(s.source, s.target) for s in self.streets]
        return (all(0 <= a < self.n and 0 <= b < self.n for a, b in pairs)
                and len(set(pairs)) == len(pairs) and all(0 <= p < self.n for p in self.sockets)
                and all(s.minutes >= 0 for s in self.streets))


def _heights(rng: SplitMix64, width: float, bumps: int, amplitude: float) -> Callable[
        [float, float], int]:
    """Smooth hills: a sum of `bumps` round hills and hollows over a square of side `width`."""
    hills = [(rng.next_f64() * width, rng.next_f64() * width,
              (rng.next_f64() * 2 - 0.6) * amplitude, (0.08 + 0.15 * rng.next_f64()) * width)
             for _ in range(bumps)]

    def height(x: float, y: float) -> int:
        return round(sum(a * math.exp(-((x - cx) ** 2 + (y - cy) ** 2) / (2 * r * r))
                         for cx, cy, a, r in hills))
    return height


def _street(a: int, b: int, length: int, ha: int, hb: int) -> Street:
    """Minutes grow with the length and the climb; energy is the length plus the climb, so negative
    downhill."""
    climb = hb - ha
    return Street(a, b, 2 * length + max(0, climb), length + climb)


def _finish(family: str, seed: int, rng: SplitMix64, n: int, pairs: list[tuple[int, int, int]],
            height: list[int], socket_share: float, charge_minutes: int) -> TownData:
    """Streets from the pairs, the two planted places, sockets, trips, and shuffled numbers."""
    streets = {(a, b): _street(a, b, ln, height[a], height[b]) for a, b, ln in pairs if a != b}
    # the place no street leads to, and the hilltop no full battery climbs to
    lost, top = _below(rng, n), _below(rng, n)
    while top == lost:
        top = _below(rng, n)
    streets = {k: s for k, s in streets.items() if s.target != lost}
    for k, st in list(streets.items()):
        if st.target == top:
            streets[k] = Street(st.source, st.target, st.minutes, FULL + 1 + _below(rng, 5))
    sockets = {p for p in range(n) if rng.next_f64() < socket_share} - {lost, top}
    out: list[list[int]] = [[] for _ in range(n)]
    for a, b in streets:
        out[a].append(b)
    trips: list[tuple[int, int]] = []
    while len(trips) < ASKED - 2:
        # a goal some street route reaches; the battery may still forbid every route
        s = _below(rng, n)
        reached, todo = {s}, [s]
        while todo:
            for q in out[todo.pop()]:
                if q not in reached:
                    reached.add(q)
                    todo.append(q)
        goals = sorted(reached - {s, lost, top})
        if s in (lost, top) or not goals:
            continue
        trips.append((s, goals[_below(rng, len(goals))]))
    s0 = trips[0][0]
    trips += [(s0, lost), (s0, top)]
    order = list(range(n))
    for i in range(n - 1, 0, -1):
        j = _below(rng, i + 1)
        order[i], order[j] = order[j], order[i]
    keyed = sorted(streets.values(), key=lambda s: rng.next_u64())
    town = TownData(family, seed, n,
                    tuple(Street(order[s.source], order[s.target], s.minutes, s.energy)
                          for s in keyed),
                    frozenset(order[p] for p in sockets), FULL, charge_minutes,
                    tuple((order[a], order[b]) for a, b in trips))
    return town


def hills(seed: int, n: int = N) -> TownData:
    """A grid of streets over smooth hills: most neighbors joined both ways, some one way."""
    rng = SplitMix64(seed * 1_000_003 + 1)
    side = max(2, round(math.sqrt(n)))
    n = side * side
    h = _heights(rng, side, 8, 60)
    height = [h(i % side, i // side) for i in range(n)]
    pairs: list[tuple[int, int, int]] = []
    for i in range(n):
        x, y = i % side, i // side
        for j, ok in ((i + 1, x + 1 < side), (i + side, y + 1 < side)):
            if not ok or rng.next_f64() > 0.8:
                continue
            length = 1 + _below(rng, 3)
            r = rng.next_f64()
            if r < 0.85:
                pairs += [(i, j, length), (j, i, length)]
            elif r < 0.925:
                pairs.append((i, j, length))
            else:
                pairs.append((j, i, length))
    return _finish("hills", seed, rng, n, pairs, height, 0.015, 2)


def sprawl(seed: int, n: int = N) -> TownData:
    """Scattered places, each joined to its three nearest, most streets two-way, over hills."""
    rng = SplitMix64(seed * 1_000_003 + 2)
    width = 1000.0
    pts = [(rng.next_f64() * width, rng.next_f64() * width) for _ in range(n)]
    h = _heights(rng, width, 10, 80)
    height = [h(x, y) for x, y in pts]
    cell = width / max(1, round(math.sqrt(n / 4)))
    grid: dict[tuple[int, int], list[int]] = {}
    for i, (x, y) in enumerate(pts):
        grid.setdefault((int(x // cell), int(y // cell)), []).append(i)
    joined: dict[tuple[int, int], int] = {}
    for i, (x, y) in enumerate(pts):
        cx, cy = int(x // cell), int(y // cell)
        near = [j for dx in (-1, 0, 1) for dy in (-1, 0, 1)
                for j in grid.get((cx + dx, cy + dy), ()) if j != i]
        near.sort(key=lambda j: (pts[j][0] - x) ** 2 + (pts[j][1] - y) ** 2)
        for j in near[:3]:
            joined[(min(i, j), max(i, j))] = max(1, round(math.dist(pts[i], pts[j]) / 6))
    pairs: list[tuple[int, int, int]] = []
    for (i, j), length in sorted(joined.items()):
        r = rng.next_f64()
        if r < 0.7:
            pairs += [(i, j, length), (j, i, length)]
        elif r < 0.85:
            pairs.append((i, j, length))
        else:
            pairs.append((j, i, length))
    return _finish("sprawl", seed, rng, n, pairs, height, 0.02, 2)


FAMILIES: dict[str, Callable[[int, int], TownData]] = {"hills": hills, "sprawl": sprawl}


def generate(family: str, seed: int, n: int = N) -> TownData:
    """The town `family` draws from `seed`."""
    return FAMILIES[family](seed, n)


# --- The counted cost ------------------------------------------------------------------------


class OverBudget(Exception):
    """The town stopped answering: the candidate read more than `BUDGET` allows."""


class Meter:
    """What a candidate has read of the town in one phase, and the read at which the town stops
    answering."""

    def __init__(self, budget: int) -> None:
        self.reads = 0
        self.budget = budget
        self.over = False

    def start(self) -> None:
        self.reads = 0

    def charge(self, reads: int) -> None:
        self.reads += max(1, reads)
        if self.reads > self.budget:
            self.over = True
            raise OverBudget(f"more than {self.budget:,} reads")


class Town:
    """The town, as a candidate sees it: how many places, the battery's full level, the minutes a
    socket takes to add a level, and three counted questions. Places are numbered `0 .. n-1`. It
    takes no attributes of the candidate's."""

    __slots__ = ("__meter", "__out", "__into", "__sockets", "n", "full", "charge_minutes")

    def __init__(self, data: TownData, meter: Meter) -> None:
        self.__meter = meter
        self.__out: list[list[tuple[int, int, int]]] = [[] for _ in range(data.n)]
        self.__into: list[list[tuple[int, int, int]]] = [[] for _ in range(data.n)]
        for s in data.streets:
            self.__out[s.source].append((s.target, s.minutes, s.energy))
            self.__into[s.target].append((s.source, s.minutes, s.energy))
        self.__sockets = data.sockets
        self.n = data.n
        self.full = data.full
        self.charge_minutes = data.charge_minutes

    def __place(self, p: int) -> int:
        if type(p) is not int or not 0 <= p < self.n:
            raise ValueError(f"no place {p!r}: places are 0..{self.n - 1}")
        return p

    def streets_from(self, p: int) -> list[tuple[int, int, int]]:
        """The streets out of `p`, one row `(place it leads to, minutes, energy)` each. Counts one
        read per row, and one for an empty row."""
        row = self.__out[self.__place(p)]
        self.__meter.charge(len(row))
        return list(row)

    def streets_to(self, p: int) -> list[tuple[int, int, int]]:
        """The streets into `p`, one row `(place it leaves, minutes, energy)` each. Counts as
        `streets_from` does."""
        row = self.__into[self.__place(p)]
        self.__meter.charge(len(row))
        return list(row)

    def has_socket(self, p: int) -> bool:
        """Whether `p` has a socket. Counts one read."""
        self.__meter.charge(1)
        return self.__place(p) in self.__sockets


class Candidate(Protocol):
    """What a candidate offers once built."""

    def plan(self, start: int, goal: int) -> list[int | str] | None:
        """The quickest trip from `start` to `goal` that never runs the battery flat, as its
        steps: a place for a ride along the street to it, `"charge"` for a charging stop; or
        `None` when there is no such trip."""
        ...


Make = Callable[[Town], Candidate]
"""How a candidate is built: from the town, seen through `Town` only."""


# --- The protected truth ---------------------------------------------------------------------


def _rows(data: TownData) -> list[list[tuple[int, int, int]]]:
    out: list[list[tuple[int, int, int]]] = [[] for _ in range(data.n)]
    for s in data.streets:
        out[s.source].append((s.target, s.minutes, s.energy))
    return out


def quickest(data: TownData, start: int, goal: int,
             out: list[list[tuple[int, int, int]]] | None = None) -> int | None:
    """The minutes of the quickest trip from `start` to `goal` that never runs flat, or `None`:
    Dijkstra's algorithm on the states (place, level), the battery starting full. A ride from
    level `l` along a street of energy `e` needs `l - e >= 0` and ends at `min(full, l - e)`; a
    charging stop at a socket below full ends one level up."""
    out = out if out is not None else _rows(data)
    full, cm = data.full, data.charge_minutes
    best = {(start, full): 0}
    heap = [(0, start, full)]
    while heap:
        d, p, lv = heapq.heappop(heap)
        if best.get((p, lv)) != d:
            continue
        if p == goal:
            return d
        nexts = [(q, m, min(full, lv - e)) for q, m, e in out[p] if lv - e >= 0]
        if lv < full and p in data.sockets:
            nexts.append((p, cm, lv + 1))
        for q, m, l2 in nexts:
            nd = d + m
            if nd < best.get((q, l2), math.inf):
                best[(q, l2)] = nd
                heapq.heappush(heap, (nd, q, l2))
    return None


# --- The contract, piece by piece ------------------------------------------------------------


def _walk(data: TownData, start: int, answer: object) -> list[tuple[int, int, int]] | None:
    """The states the answer passes, `(place, level, minutes so far)`, the start first, or `None`
    when a step is not a step of the town: a ride needs a street from where the bike stands to
    the place named, a charging stop a socket there. Levels are not capped below: a trip that
    runs flat shows a level below 0. The Lean `Town.passes` and `Town.minutesFrom`."""
    if not isinstance(answer, list):
        return None
    street = {(s.source, s.target): s for s in data.streets}
    p, lv, mins = start, data.full, 0
    states = [(p, lv, mins)]
    for step in answer:
        if step == CHARGE and type(step) is str:
            if p not in data.sockets:
                return None
            lv, mins = min(data.full, lv + 1), mins + data.charge_minutes
        elif type(step) is int and (p, step) in street:
            s = street[(p, step)]
            p, lv, mins = step, min(data.full, lv - s.energy), mins + s.minutes
        else:
            return None
        states.append((p, lv, mins))
    return states


def is_real_trip(data: TownData, start: int, goal: int, answer: object) -> bool:
    """Every ride is along a street of the town, every charging stop at a socket, and the trip
    ends at the goal. The Lean `Town.IsTrip`, the first half of `RealTripOn`."""
    states = _walk(data, start, answer)
    return states is not None and states[-1][0] == goal


def is_never_flat(data: TownData, start: int, answer: object) -> bool:
    """After every step the level is not below empty. The Lean `Town.NeverFlat`, the second half
    of `RealTripOn`."""
    states = _walk(data, start, answer)
    return states is not None and all(lv >= 0 for _, lv, _ in states)


def minutes_of(data: TownData, start: int, answer: object) -> int:
    """The minutes a real trip takes. The Lean `Town.tripMinutes`."""
    states = _walk(data, start, answer)
    assert states is not None
    return states[-1][2]


def is_none_quicker(data: TownData, start: int, answer: object, best: int | None) -> bool:
    """No trip that never runs flat is quicker than the one given: its minutes are at most the
    quickest's. The Lean `NoneQuickerOn`, for an answer that is a real trip."""
    return answer is None or (best is not None and minutes_of(data, start, answer) <= best)


def is_says_none(answer: object, best: int | None) -> bool:
    """`None` exactly when no trip from the start to the goal never runs flat. The Lean
    `SaysNoneOn`."""
    return (answer is None) == (best is None)


def check_answer(data: TownData, start: int, goal: int, answer: object,
                 best: int | None) -> str | None:
    """The first piece of the contract the answer breaks, by name, or `None`."""
    if not is_says_none(answer, best):
        return "says none" if answer is None else "gave a trip where there is none"
    if answer is None:
        return None
    if not is_real_trip(data, start, goal, answer):
        return "a real trip"
    if not is_never_flat(data, start, answer):
        return "never flat"
    if not is_none_quicker(data, start, answer, best):
        return "none quicker"
    return None


# --- Memory, counted as `algodesign.graphs.workbench` counts it ---------------------------

_SKIPPED = (type, types.ModuleType, types.BuiltinFunctionType, Town, Meter)
_WORD = 1 << 63
_PLAIN = (int, float, complex, str, bytes, bytearray, type(None))
_FIXED = (int, float, complex, str, bytes, type(None))
_SMALL = (range, slice, object, type(Ellipsis), type(NotImplemented))


class Uncountable(Exception):
    """The candidate holds an object `held` cannot look into."""


def _class_data(cls: type) -> list[object]:
    return [v for k, v in vars(cls).items() if not k.startswith("__") and not callable(v)
            and not isinstance(v, (property, staticmethod, classmethod,
                                   types.MemberDescriptorType, types.GetSetDescriptorType))]


def _globals(module: str) -> list[object]:
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
    if isinstance(obj, dict):
        return [*obj.keys(), *obj.values()]
    if isinstance(obj, (list, tuple, set, frozenset, deque, array, memoryview)):
        return list(obj)
    if isinstance(obj, types.FunctionType):
        cells = []
        for cell in obj.__closure__ or ():
            try:
                cells.append(cell.cell_contents)
            except ValueError:
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
            parts.extend(_class_data(cls))
    return parts


def _size(item: object) -> int:
    if isinstance(item, int) and not -_WORD <= item < _WORD:
        return -(-item.bit_length() // 64)
    if isinstance(item, (str, bytes, bytearray)):
        return max(1, -(-len(item) // 8))
    return 1


def _count(roots: list[object], seen: set[int], strict: bool = True) -> int:
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
            try:
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
    """How many numbers the candidate holds: every number, `None` and string it reaches, once per
    place it is held, and its module's global data less `before`; the town it was handed counts
    nothing. Raises `Uncountable` on an object it cannot look into."""
    seen: set[int] = set()
    own = _count([candidate], seen)
    return own + _count([v for m in modules for v in _globals(m)], seen, strict=False) - before


# --- The verdict -----------------------------------------------------------------------------


@dataclass
class TownResult:
    """One candidate on one town."""
    family: str
    seed: int
    n: int
    streets: int
    full: int
    build_reads: int = 0
    trip_reads: list[int] = field(default_factory=list)
    memory: int = 0
    nones: int = 0
    charged: int = 0
    failure: str | None = None

    def size(self) -> int:
        """States and rides: every place and every street, once per battery level."""
        return (self.n + self.streets) * (self.full + 1)

    def worst_trip(self) -> int:
        return max(self.trip_reads, default=0)


@dataclass
class Verdict:
    """One candidate on every town."""
    name: str
    towns: list[TownResult] = field(default_factory=list)


@dataclass
class Entry:
    """A candidate to judge: its name and how it is built."""
    name: str
    make: Make


def judge(entries: Sequence[Entry], seeds: Sequence[int],
          families: Sequence[str] = tuple(FAMILIES), n: int = N) -> list[Verdict]:
    """Every candidate on the town each family draws from each seed, each with a town of its own.
    Every candidate builds itself and answers every trip; only then is the truth computed."""
    verdicts = [Verdict(e.name) for e in entries]
    for family in families:
        for seed in seeds:
            data = generate(family, seed, n)
            runs: list[tuple[TownResult, list[object]]] = []
            for entry, verdict in zip(entries, verdicts, strict=True):
                result = TownResult(family, seed, data.n, len(data.streets), data.full)
                verdict.towns.append(result)
                meter = Meter(BUDGET * result.size())
                answers: list[object] = []
                try:
                    module = getattr(entry.make, "__module__", None)
                    modules = (module,) if isinstance(module, str) else ()
                    before = _count([v for m in modules for v in _globals(m)
                                     if isinstance(v, _FIXED)], set(), strict=False)
                    candidate = entry.make(Town(data, meter))
                    result.build_reads = meter.reads
                    for s, g in data.trips:
                        meter.start()
                        answers.append(candidate.plan(s, g))
                        result.trip_reads.append(meter.reads)
                    result.memory = held(candidate, before, modules)
                except Uncountable as e:
                    result.failure = f"holds what the bench cannot count: {e}"
                except Exception as e:  # noqa: BLE001 -- a candidate that fails, fails its verdict
                    result.failure = f"raised {type(e).__name__}: {e}"
                if meter.over:
                    result.failure = f"read the town past its budget of {BUDGET} per state and ride"
                runs.append((result, answers))
            out = _rows(data)
            best = [quickest(data, s, g, out) for s, g in data.trips]
            for result, answers in runs:
                if result.failure is not None:
                    continue
                result.nones = sum(b is None for b in best)
                for (s, g), answer, b in zip(data.trips, answers, best, strict=True):
                    wrong = check_answer(data, s, g, answer, b)
                    if wrong is not None:
                        result.failure = f"broke the promise on the trip {s} to {g}: {wrong}"
                        break
                    if isinstance(answer, list) and CHARGE in answer:
                        result.charged += 1
    return verdicts


def report(verdict: Verdict) -> str:
    """The verdict in plain words: passes or not, and why, with the worst town's numbers."""
    if not verdict.towns:
        return f"{verdict.name}: not judged."
    failed = [t for t in verdict.towns if t.failure is not None]
    if failed:
        t = failed[0]
        return f"{verdict.name}: fails on {t.family} seed {t.seed}: {t.failure}."
    reasons = []
    if any(t.worst_trip() > READS * t.size() for t in verdict.towns):
        reasons.append(f"a trip read more than {READS} per state and ride")
    if any(t.memory > MEMORY * t.size() for t in verdict.towns):
        reasons.append(f"more than {MEMORY} numbers per state and ride")
    head = "passes" if not reasons else "fails: " + ", ".join(reasons)
    worst = max(verdict.towns, key=lambda t: t.worst_trip() / t.size())
    mem = max(verdict.towns, key=lambda t: t.memory / t.size())
    build = max(verdict.towns, key=lambda t: t.build_reads)
    asked = sum(len(t.trip_reads) for t in verdict.towns)
    nones = sum(t.nones for t in verdict.towns)
    charged = sum(t.charged for t in verdict.towns)
    return (f"{verdict.name}: {head}. {worst.worst_trip():,} reads on its costliest trip "
            f"({worst.worst_trip() / worst.size():.3f} per state and ride, at most {READS}); "
            f"{build.build_reads:,} reads to build on its costliest town; "
            f"{mem.memory:,} numbers held on its largest "
            f"({mem.memory / mem.size():.3f} per state and ride, at most {MEMORY}); "
            f"{asked} trips asked, {nones} with no trip, {charged} answers with a charging stop; "
            f"every answer kept the contract.")


# --- The chapter's method as a candidate -----------------------------------------------------


class _Chapter:
    """Dijkstra's algorithm on the states, as the chapter runs it: a state is a place and a level,
    a ride lowers the level by the street's energy and ends at most at full, and a socket adds a
    level. It reads a place's streets and its socket each time it settles a state there, and keeps
    nothing between trips."""

    def __init__(self, town: Town) -> None:
        self.town = town

    def plan(self, start: int, goal: int) -> list[int | str] | None:
        t = self.town
        full = t.full
        best = {(start, full): 0}
        came: dict[tuple[int, int], tuple[int, int] | None] = {(start, full): None}
        heap = [(0, start, full)]
        while heap:
            d, p, lv = heapq.heappop(heap)
            if best[(p, lv)] != d:
                continue
            if p == goal:
                steps: list[int | str] = []
                at: tuple[int, int] | None = (p, lv)
                while at is not None and came[at] is not None:
                    prev = came[at]
                    assert prev is not None
                    steps.append(CHARGE if prev[0] == at[0] else at[0])
                    at = prev
                return steps[::-1]
            nexts = [(q, m, min(full, lv - e)) for q, m, e in t.streets_from(p) if lv - e >= 0]
            if lv < full and t.has_socket(p):
                nexts.append((p, t.charge_minutes, lv + 1))
            for q, m, l2 in nexts:
                nd = d + m
                if nd < best.get((q, l2), math.inf):
                    best[(q, l2)] = nd
                    came[(q, l2)] = (p, lv)
                    heapq.heappush(heap, (nd, q, l2))
        return None


def chapter_candidate(town: Town) -> Candidate:
    """The chapter's method as a candidate: Dijkstra's algorithm on the states."""
    return _Chapter(town)
