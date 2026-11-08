# SPDX-License-Identifier: Apache-2.0
"""The design project's bench: the truth is the quickest trip over every trip that passes no state
twice, the towns come back the same from the same seed and hold a goal no street reaches and a
hilltop no battery climbs to, the reads count what they say, and each broken promise is caught by
its own check."""

from __future__ import annotations

import heapq

import pytest
from hypothesis import given
from hypothesis import strategies as st

from algodesign.paths import workbench as wb

N = 400  # a small judged town: the bench's own size takes minutes per trip in the tests


@st.composite
def towns(draw: st.DrawFn) -> wb.TownData:
    """Up to five places and eight streets, a battery of up to three levels, streets of zero
    minutes and negative energy among them."""
    n = draw(st.integers(1, 5))
    place = st.integers(0, n - 1)
    pairs = draw(st.sets(st.tuples(place, place), max_size=8))
    streets = tuple(wb.Street(a, b, draw(st.integers(0, 4)), draw(st.integers(-2, 3)))
                    for a, b in sorted(pairs) if a != b)
    sockets = draw(st.frozensets(place, max_size=n))
    return wb.TownData("drawn", 0, n, streets, sockets, draw(st.integers(0, 3)),
                       draw(st.integers(0, 3)), ())


def _brute(data: wb.TownData, start: int, goal: int) -> int | None:
    """The quickest over every trip from `start` that passes no state twice and never runs flat;
    the Lean `Town.noneQuicker_iff` says these are enough."""
    out = [[s for s in data.streets if s.source == p] for p in range(data.n)]
    best: list[int | None] = [None]

    def go(p: int, lv: int, mins: int, seen: set[tuple[int, int]]) -> None:
        if p == goal and (best[0] is None or mins < best[0]):
            best[0] = mins
        moves = [(s.target, s.minutes, min(data.full, lv - s.energy)) for s in out[p]
                 if lv - s.energy >= 0]
        if p in data.sockets:
            moves.append((p, data.charge_minutes, min(data.full, lv + 1)))
        for q, m, l2 in moves:
            if (q, l2) not in seen:
                seen.add((q, l2))
                go(q, l2, mins + m, seen)
                seen.remove((q, l2))

    go(start, data.full, 0, {(start, data.full)})
    return best[0]


@given(towns())
def test_the_truth_is_the_quickest_over_every_trip(data: wb.TownData) -> None:
    assert data.well_formed()
    for s in range(data.n):
        for g in range(data.n):
            assert wb.quickest(data, s, g) == _brute(data, s, g)


@given(towns())
def test_the_chapter_candidate_keeps_the_contract(data: wb.TownData) -> None:
    chapter = wb.chapter_candidate(wb.Town(data, wb.Meter(10**9)))
    for s in range(data.n):
        for g in range(data.n):
            best = wb.quickest(data, s, g)
            answer = chapter.plan(s, g)
            assert wb.check_answer(data, s, g, answer, best) is None
            if answer is not None:
                assert wb.check_answer(data, s, g, None, best) == "says none"


def test_the_chapter_candidate_passes_on_every_family() -> None:
    verdict = wb.judge([wb.Entry("chapter", wb.chapter_candidate)], [1], n=N)[0]
    assert all(t.failure is None for t in verdict.towns), [t.failure for t in verdict.towns]
    assert wb.report(verdict).startswith("chapter: passes.")


def test_each_family_is_deterministic_and_holds_the_trips_with_no_answer() -> None:
    for family in wb.FAMILIES:
        a, b = wb.generate(family, 5, N), wb.generate(family, 5, N)
        assert a == b and a.well_formed()
        assert len(a.trips) == wb.ASKED
        lost, top = a.trips[-2][1], a.trips[-1][1]
        assert not any(s.target == lost for s in a.streets)
        assert all(s.energy > a.full for s in a.streets if s.target == top)
        assert wb.quickest(a, *a.trips[-2]) is None and wb.quickest(a, *a.trips[-1]) is None
        assert any(s.energy < 0 for s in a.streets)


# --- The Lean's three-place town (`AlgoDesignTests.PathsWorkbench`) ---------------------------

TOWN = wb.TownData("lean", 0, 3, (wb.Street(0, 1, 2, 1), wb.Street(1, 2, 3, 1),
                                  wb.Street(2, 0, 1, -1)), frozenset({1}), 1, 5, ())
DARK = wb.TownData("lean", 0, 3, TOWN.streets, frozenset(), 1, 5, ())
C = wb.CHARGE


def test_the_lean_s_decided_trips_pass_every_piece() -> None:
    assert TOWN.well_formed() and DARK.well_formed()
    trip: list[int | str] = [1, C, 2]
    best = wb.quickest(TOWN, 0, 2)
    assert best == 10 and wb.minutes_of(TOWN, 0, trip) == 10
    assert wb.is_real_trip(TOWN, 0, 2, trip) and wb.is_never_flat(TOWN, 0, trip)
    assert wb.is_none_quicker(TOWN, 0, trip, best) and wb.is_says_none(trip, best)
    # downhill at full stays full: back from 2 to 0 and on to 1 at level 0, never flat
    down: list[int | str] = [0, 1]
    assert wb.check_answer(TOWN, 2, 1, down, wb.quickest(TOWN, 2, 1)) is None
    assert wb.check_answer(DARK, 0, 2, None, wb.quickest(DARK, 0, 2)) is None


def test_the_lean_s_decided_broken_trips_fail_their_piece() -> None:
    best = wb.quickest(TOWN, 0, 2)
    # without the charge the battery runs flat: a real trip, but flat
    assert wb.is_real_trip(TOWN, 0, 2, [1, 2]) and not wb.is_never_flat(TOWN, 0, [1, 2])
    assert wb.check_answer(TOWN, 0, 2, [1, 2], best) == "never flat"
    # a charge where there is no socket is no trip
    assert wb.check_answer(TOWN, 0, 2, [C, 1, 2], best) == "a real trip"
    assert wb.check_answer(TOWN, 0, 2, None, best) == "says none"
    # a slower trip is real and not the quickest
    slow: list[int | str] = [1, C, 2, 0, 1, C, 2]
    assert wb.is_real_trip(TOWN, 0, 2, slow) and wb.is_never_flat(TOWN, 0, slow)
    assert wb.check_answer(TOWN, 0, 2, slow, best) == "none quicker"
    # no socket: no trip from 0 to 2 never runs flat
    none = wb.quickest(DARK, 0, 2)
    assert none is None
    assert wb.check_answer(DARK, 0, 2, [1, 2], none) == "gave a trip where there is none"
    assert not wb.is_real_trip(DARK, 0, 2, [1, C, 2])


def test_a_trip_may_arrive_at_empty() -> None:
    data = wb.TownData("t", 0, 2, (wb.Street(0, 1, 1, 2),), frozenset(), 2, 1, ())
    assert wb.quickest(data, 0, 1) == 1
    assert wb.check_answer(data, 0, 1, [1], 1) is None


@pytest.mark.parametrize("answer", ["1", [1.0], [True], ["charge "], 7])
def test_an_answer_of_the_wrong_kind_is_no_trip(answer: object) -> None:
    assert not wb.is_real_trip(TOWN, 0, 1, answer)


# --- The counted cost ----------------------------------------------------------------------


def test_every_read_is_counted() -> None:
    meter = wb.Meter(10**9)
    town = wb.Town(TOWN, meter)
    assert town.streets_from(0) == [(1, 2, 1)] and meter.reads == 1
    assert town.streets_to(0) == [(2, 1, -1)] and meter.reads == 2
    assert town.has_socket(1) and meter.reads == 3
    empty = wb.TownData("t", 0, 1, (), frozenset(), 1, 1, ())
    m2 = wb.Meter(10**9)
    assert wb.Town(empty, m2).streets_from(0) == [] and m2.reads == 1
    with pytest.raises(ValueError):
        town.streets_from(3)
    with pytest.raises(ValueError):
        town.has_socket(True)


def test_the_town_takes_no_attributes() -> None:
    town = wb.Town(TOWN, wb.Meter(10))
    with pytest.raises(AttributeError):
        town.cache = {}  # type: ignore[attr-defined]


def test_a_candidate_that_rereads_the_town_stops_at_the_budget() -> None:
    class Rereads:
        def __init__(self, town: wb.Town) -> None:
            self.town = town

        def plan(self, start: int, goal: int) -> list[int | str] | None:
            while True:
                self.town.streets_from(start)

    verdict = wb.judge([wb.Entry("rereads", Rereads)], [1], ["hills"], n=N)[0]
    assert "past its budget" in (verdict.towns[0].failure or "")
    assert wb.report(verdict).startswith("rereads: fails on hills seed 1")


def test_a_candidate_that_keeps_a_copy_is_counted() -> None:
    class Copies:
        def __init__(self, town: wb.Town) -> None:
            self.rows = [town.streets_from(p) for p in range(town.n)]
            self.inner = wb.chapter_candidate(town)

        def plan(self, start: int, goal: int) -> list[int | str] | None:
            return self.inner.plan(start, goal)

    copies, chapter = wb.judge([wb.Entry("copies", Copies),
                                wb.Entry("chapter", wb.chapter_candidate)], [1], ["hills"], n=N)
    data = wb.generate("hills", 1, N)
    rows = [sum(s.source == p for s in data.streets) for p in range(data.n)]
    assert copies.towns[0].build_reads == sum(max(1, r) for r in rows)
    assert chapter.towns[0].build_reads == 0
    assert copies.towns[0].memory >= 3 * len(data.streets)
    assert chapter.towns[0].memory < copies.towns[0].memory


def test_an_object_held_cannot_look_into_fails_the_verdict() -> None:
    class Hides:
        def __init__(self, town: wb.Town) -> None:
            self.inner = wb.chapter_candidate(town)
            self.box = iter([1, 2, 3])

        def plan(self, start: int, goal: int) -> list[int | str] | None:
            return self.inner.plan(start, goal)

    verdict = wb.judge([wb.Entry("hides", Hides)], [1], ["hills"], n=N)[0]
    assert "cannot count" in (verdict.towns[0].failure or "")


def test_the_truth_comes_after_every_candidates_answers(monkeypatch: pytest.MonkeyPatch) -> None:
    order: list[str] = []
    truth = wb.quickest

    def logged(*args: object, **kw: object) -> int | None:
        order.append("truth")
        return truth(*args, **kw)  # type: ignore[arg-type]

    class Logs:
        def __init__(self, town: wb.Town) -> None:
            self.inner = wb.chapter_candidate(town)

        def plan(self, start: int, goal: int) -> list[int | str] | None:
            order.append("plan")
            return self.inner.plan(start, goal)

    monkeypatch.setattr(wb, "quickest", logged)
    wb.judge([wb.Entry("a", Logs), wb.Entry("b", Logs)], [1], ["hills"], n=N)
    assert order.index("truth") == 2 * wb.ASKED


def test_the_chapter_candidate_reads_a_place_s_streets_each_time_it_settles_a_state() -> None:
    data = wb.generate("sprawl", 2, N)
    meter = wb.Meter(10**12)
    s, g = data.trips[0]
    wb.chapter_candidate(wb.Town(data, meter)).plan(s, g)
    rows = [[t for t in data.streets if t.source == p] for p in range(data.n)]
    # the same walk, counting a read per row and per socket question below full
    best, heap, reads = {(s, data.full): 0}, [(0, s, data.full)], 0
    while heap:
        d, p, lv = heapq.heappop(heap)
        if best[(p, lv)] != d:
            continue
        if p == g:
            break
        reads += max(1, len(rows[p])) + (lv < data.full)
        nexts = [(t.target, t.minutes, min(data.full, lv - t.energy)) for t in rows[p]
                 if lv - t.energy >= 0]
        if lv < data.full and p in data.sockets:
            nexts.append((p, data.charge_minutes, lv + 1))
        for q, m, l2 in nexts:
            if d + m < best.get((q, l2), 10**18):
                best[(q, l2)] = d + m
                heapq.heappush(heap, (d + m, q, l2))
    assert meter.reads == reads


def test_no_hidden_seed_is_in_the_library() -> None:
    assert set(wb.PRACTICE_SEEDS) == {1, 2, 3}
