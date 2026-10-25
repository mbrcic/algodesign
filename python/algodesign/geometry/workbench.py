# SPDX-License-Identifier: Apache-2.0
"""The Geometry chapter's design project: a bench for an index of "places like this one".

The problem is fixed here, before any candidate exists: answer the ten nearest stored points to a
query, beat the scan's count of distance computations, find at least nine in ten of the true ten
nearest (recall@10 of 0.9), and hold no more than a memory cap. The reader specifies, an AI
implements, and this bench judges:

- `Points` and `Query`, the counted cost: a candidate sees the stored points and each query only
  through them. Every squared distance (`dist`) and every inner product with a vector of its own
  (`dot`) counts one; nothing else reads a coordinate, and no clock is read.
- `generate`, the hidden corpora: clustered points of low intrinsic dimension in 100 dimensions,
  and a skewed family meant to be hard, both drawn from a seed the judge keeps. The library holds
  only `PRACTICE_SEEDS`, for a candidate to tune on.
- `judge`, the verdict: the scan computes the true ten nearest only after every candidate has
  answered, and each answer is checked against the contract (`is_up_to_k`, `is_stored`,
  `is_each_once`, `is_nearest_first`, `is_exact_distance`), its recall measured, and the
  candidate's memory counted (`held`) against `CAP` numbers per stored coordinate. `report` says
  it in plain words.
- `scan_candidate`, `kdtree_candidate`, `lsh_candidate`, `hnsw_candidate`, the chapter's own
  structures as candidates, for calibration.

The checks close the routes through the objects a candidate is handed, and no more. Coordinates
are stored scaled, axis by axis, by secret powers of two, so a candidate that reads the storage
gets wrong distances and fails `is_exact_distance`; `held` refuses one that keeps copies of the
coordinates.
A candidate that edits the bench's private state, or reaches through the interpreter (frames,
`gc`, other modules), is not caught: reading the candidate is the reader's part.

The promise comes first, in Lean: `lean/AlgoDesign/Geometry/Workbench/Spec.lean` states what every
answer owes (`Contract`) and how recall is measured (`recallAt`). Python only: a tool for the
chapter's project, not a structure the chapter teaches.

The Lean statements behind this module, in `lean/AlgoDesign/Geometry/Workbench/` (specification:
`Workbench/Spec.lean`): `reference_contract`, `recall_eq_one_of_scan`, `reference_recall`,
`time_referenceM`.
"""

from __future__ import annotations

import functools
import math
import random
import types
from array import array
from collections import deque
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import Protocol

from ._rng import SplitMix64
from .hnsw import HNSW, finish
from .kdtree import KDTree, Leaf, Node
from .lsh import LSHIndex, PStable
from .point import sq_dist

K = 10
"""How many nearest points a query asks for."""

RECALL = 0.9
"""The least recall@10 a candidate may have, on every hidden seed."""

SHARE = 0.5
"""The most distances and inner products per query a candidate may compute, as a share of the
scan's `n`, on every hidden seed."""

CAP = 1.0
"""The memory cap, in numbers held per stored coordinate: `CAP * n * d` numbers in all. The bench
holds the points, so this is the index alone, and a full copy of the points would fill it."""

COPIES = 0.1
"""The share of the stored coordinates a candidate may hold copies of before `held` refuses it.
A k-d tree's cuts are coordinates, one per node, about `n` of `n * d`."""

PRACTICE_SEEDS = (1, 2, 3)
"""Seeds a candidate may see and tune on. The judge's seeds are its own, and never in here."""

DIM = 100
"""The ambient dimension of every corpus."""

Answer = list[tuple[float, int]]
"""Squared distances with point ids, nearest first."""


# --- The counted cost ------------------------------------------------------------------------


class Meter:
    """What a candidate has computed: squared distances and inner products, one count each."""

    def __init__(self) -> None:
        self.distances = 0
        self.dots = 0

    def ticks(self) -> int:
        """Distances and inner products together: the cost a query is scored on."""
        return self.distances + self.dots


class _Store:
    """The coordinates, each axis scaled by a secret power of two. Scaling by a power of two is
    exact in floating point, so undoing it gives back the coordinates bit for bit, and a distance
    computed through `Points` is bit for bit `point.sq_dist`'s."""

    def __init__(self, rows: list[list[float]]) -> None:
        dim = len(rows[0]) if rows else 0
        secret = random.SystemRandom()
        exponents = [secret.choice([e for e in range(-6, 7) if e != 0]) for _ in range(dim)]
        self.scale = [2.0 ** -e for e in exponents]
        self.rows = [[x * 2.0 ** e for x, e in zip(row, exponents, strict=True)] for row in rows]
        self.opened = False

    def point(self, i: int) -> list[float]:
        return [x * s for x, s in zip(self.rows[i], self.scale, strict=True)]

    def dist(self, a: list[float], b: list[float]) -> float:
        total = 0.0
        for x, y, s in zip(a, b, self.scale, strict=True):
            t = (x - y) * s
            total += t * t
        return total

    def dot(self, a: list[float], v: Sequence[float]) -> float:
        total = 0.0
        for x, y, s in zip(a, v, self.scale, strict=True):
            total += (x * s) * y
        return total

    def scaled(self, q: list[float]) -> list[float]:
        """A query stored as the points are."""
        return [x / s for x, s in zip(q, self.scale, strict=True)]


def _vector(v: Sequence[float], dim: int) -> list[float]:
    """A plain copy of `v`, read once: a candidate's own number type never meets a coordinate."""
    values = [float(x) for x in list(v)]
    if len(values) != dim or not all(math.isfinite(x) for x in values):
        raise ValueError(f"a vector of {dim} finite numbers, not {len(values)} of them")
    return values


class Points:
    """The stored points, as a candidate sees them: how many, their dimension, and two counted
    operations. Indices run from 0 to `n - 1`."""

    def __init__(self, store: _Store, meter: Meter) -> None:
        self.__store = store
        self.__meter = meter
        self.n = len(store.rows)
        self.dim = DIM if not store.rows else len(store.rows[0])

    def dist(self, i: int, j: int) -> float:
        """The squared distance between points `i` and `j`. Counts one distance."""
        self.__meter.distances += 1
        return self.__store.dist(self.__store.rows[i], self.__store.rows[j])

    def dot(self, i: int, v: Sequence[float]) -> float:
        """The inner product of point `i` with the candidate's own vector `v`. Counts one."""
        self.__meter.dots += 1
        return self.__store.dot(self.__store.rows[i], _vector(v, self.dim))


class Query:
    """One query, as a candidate sees it: two counted operations, and nothing else."""

    def __init__(self, store: _Store, row: list[float], meter: Meter) -> None:
        self.__store = store
        self.__row = row
        self.__meter = meter

    def dist(self, i: int) -> float:
        """The squared distance from the query to stored point `i`. Counts one distance."""
        self.__meter.distances += 1
        return self.__store.dist(self.__row, self.__store.rows[i])

    def dot(self, v: Sequence[float]) -> float:
        """The inner product of the query with the candidate's own vector `v`. Counts one."""
        self.__meter.dots += 1
        return self.__store.dot(self.__row, _vector(v, len(self.__row)))


class Candidate(Protocol):
    """What a candidate offers once built: the `k` nearest stored points it finds for a query."""

    def query(self, q: Query, k: int) -> Answer:
        """Up to `k` stored points as `(squared distance, id)`, nearest first."""
        ...


Make = Callable[[Points], Candidate]
"""How a candidate is built: from the stored points, seen through `Points` only."""


def raw_points(points: Points) -> list[list[float]]:
    """The coordinates themselves, for the library's own structures as candidates, which are
    built from coordinates and judged with `trusted=True`. A candidate judged untrusted that
    calls this fails."""
    store: _Store = points._Points__store  # type: ignore[attr-defined]
    store.opened = True
    return [store.point(i) for i in range(len(store.rows))]


def charge(q: Query, distances: int) -> None:
    """Count `distances` more for query `q`: for the library's k-d tree, which measures its
    points from coordinates. It can only add."""
    q._Query__meter.distances += max(distances, 0)  # type: ignore[attr-defined]


# --- The hidden corpora ----------------------------------------------------------------------


@dataclass
class Corpus:
    """A corpus as the judge holds it: a name, the points, and the queries. Never handed to a
    candidate, which sees `Points` and `Query` only."""

    family: str
    points: list[list[float]]
    queries: list[list[float]]


def _gaussian(rng: SplitMix64, size: int, sigma: float = 1.0) -> list[float]:
    return [sigma * rng.standard_normal() for _ in range(size)]


def _embed(rng: SplitMix64, latent: int) -> Callable[[list[float]], list[float]]:
    """A random linear map from `latent` dimensions into `DIM`: columns of length about 1."""
    matrix = [_gaussian(rng, latent, 1.0 / math.sqrt(latent)) for _ in range(DIM)]

    def embed(z: list[float]) -> list[float]:
        return [sum(a * b for a, b in zip(row, z, strict=True)) for row in matrix]

    return embed


def clusters(seed: int, n: int, queries: int, latent: int = 24, centers: int = 40,
             spread: float = 2.0, noise: float = 0.5) -> Corpus:
    """Points of low intrinsic dimension in `DIM` dimensions: a Gaussian mixture of `centers`
    clusters in `latent` dimensions, embedded linearly, plus a little noise on every axis. The
    queries are drawn from the same mixture."""
    rng = SplitMix64(seed)
    embed = _embed(rng, latent)
    middles = [_gaussian(rng, latent, spread) for _ in range(centers)]

    def draw() -> list[float]:
        middle = middles[int(rng.next_f64() * centers)]
        z = [m + rng.standard_normal() for m in middle]
        return [x + noise * rng.standard_normal() for x in embed(z)]

    return Corpus("clusters", [draw() for _ in range(n)], [draw() for _ in range(queries)])


def skewed(seed: int, n: int, queries: int, latent: int = 24, centers: int = 40,
           spread: float = 2.0, noise: float = 0.5) -> Corpus:
    """A family meant to be hard. Cluster sizes fall off as 1/rank, so one cluster holds a fifth
    of the points and many hold a handful; spreads range over twenty times; one point in ten is a
    near-copy of another, so distances nearly tie; and one query in five lies between two
    clusters, where nothing is near."""
    rng = SplitMix64(seed)
    embed = _embed(rng, latent)
    middles = [_gaussian(rng, latent, spread) for _ in range(centers)]
    widths = [0.15 * 20 ** rng.next_f64() for _ in range(centers)]
    weights = [1.0 / (r + 1) for r in range(centers)]
    total = sum(weights)

    def pick() -> int:
        u, c = rng.next_f64() * total, 0
        while c < centers - 1 and u >= weights[c]:
            u -= weights[c]
            c += 1
        return c

    def draw(c: int) -> list[float]:
        z = [m + widths[c] * rng.standard_normal() for m in middles[c]]
        return [x + noise * rng.standard_normal() for x in embed(z)]

    points: list[list[float]] = []
    for _ in range(n):
        if points and rng.next_f64() < 0.1:
            original = points[int(rng.next_f64() * len(points))]
            points.append([x + 1e-6 * rng.standard_normal() for x in original])
        else:
            points.append(draw(pick()))
    asked: list[list[float]] = []
    for _ in range(queries):
        if rng.next_f64() < 0.2:
            a, b = middles[int(rng.next_f64() * centers)], middles[int(rng.next_f64() * centers)]
            z = [(x + y) / 2 + rng.standard_normal() for x, y in zip(a, b, strict=True)]
            asked.append([x + noise * rng.standard_normal() for x in embed(z)])
        else:
            asked.append(draw(pick()))
    return Corpus("skewed", points, asked)


FAMILIES: dict[str, Callable[[int, int, int], Corpus]] = {"clusters": clusters, "skewed": skewed}
"""The seed families: each draws a corpus from a seed, a size and a number of queries."""


def generate(family: str, seed: int, n: int = 10_000, queries: int = 100) -> Corpus:
    """The corpus `family` draws from `seed`: `n` points and `queries` queries, the same every
    time."""
    return FAMILIES[family](seed, n, queries)


# --- The protected reference ----------------------------------------------------------------


def reference(points: list[list[float]], q: list[float], k: int) -> Answer:
    """The scan, which no candidate reaches: every point measured, the `k` nearest kept, the
    one stored first on a tie. The Lean `reference`."""
    return sorted((sq_dist(p, q), i) for i, p in enumerate(points))[:k]


# --- The contract, piece by piece ------------------------------------------------------------


def is_up_to_k(answer: Answer, k: int) -> bool:
    """At most `k` points answered. The Lean `UpToK`."""
    return len(answer) <= k


def is_stored(answer: Answer, n: int) -> bool:
    """Every point answered is a stored one: its id is below `n`. The Lean `Stored`."""
    return all(isinstance(i, int) and 0 <= i < n for _, i in answer)


def is_each_once(answer: Answer) -> bool:
    """No point is answered twice. The Lean `EachOnce`."""
    return len({i for _, i in answer}) == len(answer)


def is_nearest_first(answer: Answer) -> bool:
    """Nearest first: the distances never decrease. The Lean `NearestFirst`."""
    return all(a[0] <= b[0] for a, b in zip(answer, answer[1:]))


def is_exact_distance(answer: Answer, distance: Callable[[int], float]) -> bool:
    """Each distance answered is the point's exact squared distance from the query, as
    `distance` computes it. The Lean `ExactDistance`."""
    return all(d == distance(i) for d, i in answer)


def check_answer(answer: Answer, k: int, n: int, distance: Callable[[int], float]) -> str | None:
    """The first piece of the Lean `Contract` an answer breaks, or `None`. `is_exact_distance` is
    asked only of an answer whose points are stored."""
    if type(answer) is not list or not all(
        type(a) is tuple and len(a) == 2 and type(a[0]) is float and type(a[1]) is int
        for a in answer
    ):
        return "contract (an answer is a list of (float, int) pairs, plain Python types)"
    if not is_up_to_k(answer, k):
        return "contract (up_to_k)"
    if not is_stored(answer, n):
        return "contract (stored)"
    if not is_each_once(answer):
        return "contract (each_once)"
    if not is_nearest_first(answer):
        return "contract (nearest_first)"
    if not is_exact_distance(answer, distance):
        return "contract (exact_distance)"
    return None


def recall(answer: Answer, truth: list[float], k: int, distance: Callable[[int], float]) -> float:
    """The share of the true `k` nearest the answer found. `truth` is every stored point's
    squared distance from the query, least first; a point answered counts if it is no farther
    than the `min(k, n)`-th of them, so a tie at that distance counts whichever point is
    answered. Out of `min(k, n)`, and 1 when that is 0. The Lean `recallAt`."""
    m = min(k, len(truth))
    if m == 0:
        return 1.0
    kth = truth[m - 1]
    return sum(1 for _, i in answer if distance(i) <= kth) / m


# --- Memory -----------------------------------------------------------------------------------

_SKIPPED = (type, types.ModuleType, types.BuiltinFunctionType, Points, Query, Meter)
_WORD = 1 << 63


def _parts(obj: object) -> list[object]:
    """What `obj` holds: a container's items, a function's captured values and defaults, an
    instance's attributes and its class's data."""
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
    parts = list(vars(obj).values()) if hasattr(obj, "__dict__") else []
    for cls in type(obj).__mro__:
        for name in getattr(cls, "__slots__", ()):
            if hasattr(obj, name):
                parts.append(getattr(obj, name))
        if cls is not object:
            parts.extend(v for k, v in vars(cls).items()
                         if not k.startswith("__") and not callable(v)
                         and not isinstance(v, (property, staticmethod, classmethod)))
    return parts


def _size(item: object) -> int:
    """How many numbers a plain value takes: one for a number or `None`, one per 64 bits of a
    larger integer, one per eight characters of a string."""
    if isinstance(item, int) and not -_WORD <= item < _WORD:
        return -(-item.bit_length() // 64)
    if isinstance(item, (str, bytes, bytearray)):
        return max(1, -(-len(item) // 8))
    return 1


def held(candidate: object, coordinates: frozenset[float] = frozenset()) -> tuple[int, int]:
    """How many numbers the candidate holds, and how many of them are in `coordinates`. Every
    number, `None` and attribute it reaches counts once per place it is held, in containers,
    arrays and what its functions capture; the points and queries it was handed, and classes and
    modules, count nothing."""
    seen = {id(candidate)}
    todo = _parts(candidate)
    count = copies = 0
    while todo:
        obj = todo.pop()
        if isinstance(obj, (int, float, complex, str, bytes, bytearray, type(None))):
            count += _size(obj)
            copies += isinstance(obj, float) and obj in coordinates
            continue
        if id(obj) in seen or isinstance(obj, _SKIPPED):
            continue
        seen.add(id(obj))
        todo.extend(_parts(obj))
    return count, copies


# --- The verdict -----------------------------------------------------------------------------


@dataclass
class SeedResult:
    """One candidate on one hidden corpus."""

    family: str
    seed: int
    n: int
    queries: int
    recall: float = 0.0
    distances: float = 0.0
    dots: float = 0.0
    build_ticks: int = 0
    memory: int = 0
    cap: int = 0
    failure: str | None = None

    def ticks(self) -> float:
        """Distances and inner products per query: the score."""
        return self.distances + self.dots

    def passes(self) -> bool:
        return (self.failure is None and self.recall >= RECALL and self.ticks() <= SHARE * self.n
                and self.memory <= self.cap)


@dataclass
class Verdict:
    """One candidate on every hidden corpus."""

    name: str
    seeds: list[SeedResult] = field(default_factory=list)

    def passes(self) -> bool:
        return bool(self.seeds) and all(s.passes() for s in self.seeds)

    def worst_recall(self) -> float:
        return min((s.recall for s in self.seeds), default=0.0)

    def worst_ticks(self) -> float:
        """The most distances and inner products per query on any seed."""
        return max((s.ticks() for s in self.seeds), default=0.0)

    def worst_memory(self) -> tuple[int, int]:
        """The most numbers held on any seed, and that seed's cap."""
        s = max(self.seeds, key=lambda s: s.memory / max(s.cap, 1))
        return s.memory, s.cap


@dataclass
class Entry:
    """A candidate to judge: its name, how it is built, and whether it is the library's own,
    built from coordinates and reporting its own memory (`trusted`)."""

    name: str
    make: Make
    trusted: bool = False


def _sample(store: _Store) -> frozenset[float]:
    """The coordinates of every tenth point, as stored and as they are: what `held` looks for."""
    picked = range(0, len(store.rows), 10)
    return frozenset([x for i in picked for x in store.rows[i]]
                     + [x for i in picked for x in store.point(i)])




def _answer(entry: Entry, store: _Store, rows: list[list[float]], k: int,
            result: SeedResult) -> list[Answer] | None:
    """Build the candidate and ask it every query, stored in `rows`; its answers, or `None` with
    `result.failure` set. The bench knows nothing true yet."""
    meter = Meter()
    try:
        candidate = entry.make(Points(store, meter))
        result.build_ticks = meter.ticks()
        meter.distances = meter.dots = 0
        answers = [candidate.query(Query(store, row, meter), k) for row in rows]
    except Exception as e:  # noqa: BLE001 -- a candidate that fails, fails its verdict
        result.failure = f"raised {type(e).__name__}: {e}"
        return None
    result.distances = meter.distances / max(len(rows), 1)
    result.dots = meter.dots / max(len(rows), 1)
    if entry.trusted:
        result.memory = candidate.held()  # type: ignore[attr-defined]
        return answers
    result.memory, copies = held(candidate, _sample(store))
    if store.opened:
        result.failure = "read the coordinates through raw_points"
    elif 10 * copies > COPIES * result.n * DIM:
        result.failure = "holds copies of the coordinates"
    return answers


def judge(entries: Sequence[Entry], seeds: Sequence[int],
          families: Sequence[str] = tuple(FAMILIES), n: int = 10_000, queries: int = 100,
          k: int = K) -> list[Verdict]:
    """Every candidate on the corpus each family draws from each seed. Every candidate answers
    a corpus before the scan computes its true nearest points, and each candidate gets a store
    of its own, so none sees what another did."""
    verdicts = [Verdict(e.name) for e in entries]
    for family in families:
        for seed in seeds:
            corpus = generate(family, seed, n, queries)
            runs = []
            for entry, verdict in zip(entries, verdicts, strict=True):
                store = _Store(corpus.points)
                rows = [store.scaled(q) for q in corpus.queries]
                result = SeedResult(family, seed, n, queries, cap=int(CAP * n * DIM))
                runs.append((result, _answer(entry, store, rows, k, result)))
                verdict.seeds.append(result)
            for qi, q in enumerate(corpus.queries):
                truth = [d for d, _ in reference(corpus.points, q, n)]

                def distance(i: int, q: list[float] = q) -> float:
                    return sq_dist(corpus.points[i], q)

                for result, answers in runs:
                    if answers is None or result.failure is not None:
                        continue
                    wrong = check_answer(answers[qi], k, n, distance)
                    if wrong is not None:
                        result.failure = f"query {qi}: {wrong}"
                        continue
                    result.recall += recall(answers[qi], truth, k, distance) / queries
    return verdicts


def report(verdict: Verdict) -> str:
    """The verdict in plain words: passes or not, and why, with the worst seed's numbers."""
    if not verdict.seeds:
        return f"{verdict.name}: not judged."
    failed = [s for s in verdict.seeds if s.failure is not None]
    if failed:
        s = failed[0]
        return f"{verdict.name}: fails on {s.family} seed {s.seed}: {s.failure}."
    n = max(s.n for s in verdict.seeds)
    memory, cap = verdict.worst_memory()
    ticks = verdict.worst_ticks()
    reasons = []
    if verdict.worst_recall() < RECALL:
        reasons.append(f"recall@{K} below {RECALL}")
    if any(s.ticks() > SHARE * s.n for s in verdict.seeds):
        reasons.append("more than half the scan's distances")
    if memory > cap:
        reasons.append("more memory than the cap")
    head = "passes" if not reasons else "fails: " + ", ".join(reasons)
    return (f"{verdict.name}: {head}. Recall@{K} {verdict.worst_recall():.3f} on its worst seed "
            f"(at least {RECALL}); {ticks:.0f} distances and inner products per query on its "
            f"worst seed, against the scan's {n} ({100 * ticks / n:.1f}%); memory {memory:,} "
            f"numbers, against a cap of {cap:,}; every answer kept the contract.")


# --- The chapter's structures as candidates --------------------------------------------------


class _Scan:
    """The scan: every stored point measured, the `k` nearest kept. It holds nothing."""

    def __init__(self, points: Points) -> None:
        self.n = points.n

    def query(self, q: Query, k: int) -> Answer:
        return sorted((q.dist(i), i) for i in range(self.n))[:k]

    def held(self) -> int:
        """Nothing."""
        return 0


def scan_candidate(points: Points) -> Candidate:
    """The scan as a candidate: recall 1 at `n` distances a query. It holds nothing, so it is
    judged the same with `trusted=True` or without."""
    return _Scan(points)


class _KDTree:
    """The chapter's k-d tree. A query reads the query's coordinates once, an inner product per
    axis, and is charged one distance per point its best-first search measures."""

    def __init__(self, points: Points, bucket: int) -> None:
        self.tree = KDTree(raw_points(points), bucket)
        self.axes = [[float(a == b) for a in range(points.dim)] for b in range(points.dim)]

    def query(self, q: Query, k: int) -> Answer:
        coordinates = [q.dot(axis) for axis in self.axes]
        found, stats = self.tree.k_nearest_with_stats(coordinates, k)
        charge(q, stats.points_measured)
        return found

    def held(self) -> int:
        """The ordering, four numbers a node, two a leaf, and the axes."""
        def size(v: Node | Leaf) -> int:
            return 2 if isinstance(v, Leaf) else 4 + size(v.left) + size(v.right)

        nodes = 0 if self.tree.root is None else size(self.tree.root)
        return len(self.tree.order) + nodes + len(self.axes) ** 2


def kdtree_candidate(bucket: int = 8) -> Make:
    """The k-d tree as a candidate, with `bucket` points a leaf. Judge it with `trusted=True`."""
    return lambda points: _KDTree(points, bucket)


class _LSH:
    """The chapter's p-stable LSH. A query computes its key in every table through inner
    products with the table's directions, then measures each candidate once."""

    def __init__(self, points: Points, hashes: int, tables: int, width: float, seed: int) -> None:
        self.family = PStable(points.dim, hashes, tables, width, seed)
        self.index = LSHIndex(raw_points(points), self.family)

    def query(self, q: Query, k: int) -> Answer:
        found: set[int] = set()
        f = self.family
        for t, table in enumerate(self.index.buckets):
            key = tuple(math.floor((q.dot(a) + b) / f.w)
                        for a, b in zip(f.directions[t], f.offsets[t], strict=True))
            found.update(table.get(key, []))
        return sorted((q.dist(i), i) for i in found)[:k]

    def held(self) -> int:
        """One entry a point a table, a key's numbers per bucket, and the directions and
        offsets."""
        entries = sum(len(ids) + (len(key) if isinstance(key, tuple) else 1)
                      for table in self.index.buckets for key, ids in table.items())
        directions = sum(len(a) + 1 for table in self.family.directions for a in table)
        return entries + directions


def lsh_candidate(hashes: int, tables: int, width: float, seed: int = 0) -> Make:
    """p-stable LSH as a candidate: `tables` tables, keys of `hashes` cells of `width`. Judge it
    with `trusted=True`."""
    return lambda points: _LSH(points, hashes, tables, width, seed)


class _HNSW:
    """The chapter's graph index. A query walks it with the query's counted distances."""

    def __init__(self, points: Points, m: int, ef_construction: int, ef: int, flat: bool,
                 seed: int) -> None:
        self.graph = HNSW(raw_points(points), m, ef_construction, seed, flat)
        self.ef = ef

    def query(self, q: Query, k: int) -> Answer:
        if k == 0:
            return []
        return finish(self.graph.search_by(q.dist, max(self.ef, k)), k)

    def held(self) -> int:
        """Every link, a level for every node, and the entry point."""
        return sum(len(ns) + 1 for node in self.graph.links for ns in node) + 1


def hnsw_candidate(m: int, ef: int, ef_construction: int = 200, seed: int = 0,
                   flat: bool = False) -> Make:
    """The graph index as a candidate, layered or `flat`, searched with beam width `ef`. Judge
    it with `trusted=True`."""
    return lambda points: _HNSW(points, m, ef_construction, ef, flat, seed)
