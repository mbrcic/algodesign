# SPDX-License-Identifier: Apache-2.0
"""Topological order: Kahn's order or the stuck vertices, the depth-first order or a cycle, pinned
exactly on small graphs (the Rust walks the same rows in the same order, so the arrays must match)
and judged by the plain oracles on random small graphs.
"""

from __future__ import annotations

from hypothesis import given
from hypothesis import strategies as st

from algodesign.graphs import Cycle, Digraph, Stuck, dfs_order, naive, topological_order
from algodesign.graphs.topo import KahnState


@st.composite
def digraphs(draw: st.DrawFn) -> Digraph:
    n = draw(st.integers(0, 6))
    if n == 0:
        return Digraph(0, [])
    vertex = st.integers(0, n - 1)
    return Digraph(n, draw(st.lists(st.tuples(vertex, vertex), max_size=12)))


def test_both_orders_on_a_small_dag() -> None:
    g = Digraph(5, [(3, 1), (0, 1), (1, 2), (0, 3), (4, 2)])
    assert topological_order(g) == [0, 4, 3, 1, 2]
    assert dfs_order(g) == [4, 0, 3, 1, 2]


def test_kahn_and_the_depth_first_walk_give_different_orders() -> None:
    # Kahn vertices 0 and 1 as they come; the walk finishes 2 under 0, then 0, then 1.
    g = Digraph(3, [(0, 2), (1, 2)])
    assert topological_order(g) == [0, 1, 2]
    assert dfs_order(g) == [1, 0, 2]


def test_a_vertex_is_marked_when_entered() -> None:
    # The walk goes 0, 1, 2 down one path; the arrow 0 -> 2 then meets a finished vertex.
    g = Digraph(3, [(0, 1), (0, 2), (1, 2)])
    assert dfs_order(g) == [0, 1, 2]
    assert topological_order(g) == [0, 1, 2]


def test_doubled_arrows_count_twice_and_vertex_once() -> None:
    g = Digraph(3, [(0, 1), (0, 1), (2, 1)])
    assert topological_order(g) == [0, 2, 1]
    assert dfs_order(g) == [2, 0, 1]


def test_no_vertices() -> None:
    assert topological_order(Digraph(0, [])) == []
    assert dfs_order(Digraph(0, [])) == []


def test_two_vertices_waiting_on_each_other_hold_up_what_follows() -> None:
    # A <-> B -> C: all three are stuck, C only because it waits on B.
    g = Digraph(3, [(0, 1), (1, 0), (1, 2)])
    assert topological_order(g) == Stuck([0, 1, 2])
    assert dfs_order(g) == Cycle([0, 1, 0])


def test_a_loop_makes_its_vertex_stuck() -> None:
    g = Digraph(2, [(0, 1), (1, 1)])
    assert topological_order(g) == Stuck([1])
    assert dfs_order(g) == Cycle([1, 1])
    h = Digraph(2, [(0, 0), (0, 1)])
    assert topological_order(h) == Stuck([0, 1])
    assert dfs_order(h) == Cycle([0, 0])


def test_the_cycle_runs_from_the_arrows_target_back_to_it() -> None:
    g = Digraph(4, [(0, 1), (1, 2), (2, 3), (3, 1)])
    assert dfs_order(g) == Cycle([1, 2, 3, 1])
    assert topological_order(g) == Stuck([1, 2, 3])
    three = Digraph(3, [(0, 1), (1, 2), (2, 0)])
    assert dfs_order(three) == Cycle([0, 1, 2, 0])
    assert topological_order(three) == Stuck([0, 1, 2])


def test_a_cycle_met_from_a_later_root() -> None:
    g = Digraph(4, [(0, 1), (2, 3), (3, 2)])
    assert dfs_order(g) == Cycle([2, 3, 2])
    assert topological_order(g) == Stuck([2, 3])


def test_the_oracles_refuse_wrong_answers() -> None:
    g = Digraph(3, [(0, 1), (1, 0), (1, 2)])
    assert not naive.is_order(g, [0, 1, 2])
    assert not naive.is_stuck_set(g, [])
    assert not naive.is_stuck_set(g, [2])  # 2's only arrow in comes from outside the set
    assert not naive.is_stuck_set(g, [1, 0])
    assert naive.is_stuck_set(g, [0, 1])  # 2 alone outside is ordered
    assert not naive.is_cycle(g, [0, 1])
    assert not naive.is_cycle(g, [1, 2, 1])
    assert not naive.is_cycle(Digraph(2, [(0, 1), (1, 0)]), [0, 1, 0, 1, 0])
    assert naive.is_cycle(g, [1, 0, 1])
    assert naive.stuck_vertices(g) == [0, 1, 2]
    assert not naive.has_cycle(Digraph(3, [(0, 1), (0, 1), (1, 2)]))


@given(digraphs())
def test_answers_agree_with_the_oracles(g: Digraph) -> None:
    cyclic = naive.has_cycle(g)
    kahn = topological_order(g)
    if isinstance(kahn, Stuck):
        assert cyclic
        assert naive.is_stuck_set(g, kahn.vertices)
        assert kahn.vertices == naive.stuck_vertices(g)
    else:
        assert not cyclic
        assert naive.is_order(g, kahn)
    walk = dfs_order(g)
    if isinstance(walk, Cycle):
        assert cyclic
        assert naive.is_cycle(g, walk.vertices)
    else:
        assert not cyclic
        assert naive.is_order(g, walk)


def kahn_states(g: Digraph) -> list[KahnState]:
    """Every state of Kahn's walk, step by step, as the Lean's `kahnStart` and `kahnStep`."""
    count = [len(g.into[v]) for v in range(g.n)]
    st = KahnState([], count, [v for v in range(g.n) if count[v] == 0])
    states = [st]
    while st.queue:
        v, count = st.queue[0], list(st.count)
        queue = st.queue[1:]
        for w, _ in g.out[v]:
            count[w] -= 1
            if count[w] == 0:
                queue.append(w)
        st = KahnState(st.placed + [v], count, queue)
        states.append(st)
    return states


@given(digraphs())
def test_every_state_of_kahns_walk_is_valid(g: Digraph) -> None:
    states = kahn_states(g)
    assert all(st.is_valid(g) for st in states)
    answer = topological_order(g)
    if isinstance(answer, list):
        assert states[-1].placed == answer


def test_each_broken_kahn_state_names_its_piece() -> None:
    # 0 -> 1 -> 2 and 0 -> 2, after placing 0: 1 is ready, 2 still waits on 1.
    g = Digraph(3, [(0, 1), (1, 2), (0, 2)])
    assert KahnState([0], [0, 0, 1], [1]).check_valid(g) is None
    assert KahnState([1, 0], [0, 0, 1], []).check_valid(g) == "invariant 1 (placed_after_waits)"
    assert KahnState([0], [0, 0, 2], [1]).check_valid(g) == "invariant 2 (counts_unplaced_waits)"
    assert KahnState([0], [0, 0, 1], []).check_valid(g) == "invariant 3 (ready_is_zero)"
    assert KahnState([0], [0, 0, 1], [1, 1]).check_valid(g) == "invariant 3 (ready_is_zero)"


def test_a_negative_placed_vertex_is_named() -> None:
    assert KahnState([-1], [], []).check_valid(Digraph(0, [])) == "invariant 1 (placed_after_waits)"


def test_the_depth_first_walk_goes_down_a_path_deeper_than_recursion_could() -> None:
    # The walk keeps its path in frames, not on Python's call stack (its limit is about 1,000).
    n = 100_000
    assert dfs_order(Digraph(n, [(v, v + 1) for v in range(n - 1)])) == list(range(n))
    cycle = dfs_order(Digraph(n, [(v, (v + 1) % n) for v in range(n)]))
    assert isinstance(cycle, Cycle) and len(cycle.vertices) == n + 1
