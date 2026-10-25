# SPDX-License-Identifier: Apache-2.0
"""Strong components: Algorithm T and Kosaraju-Sharir pinned exactly on small graphs (the Rust walks
the same rows in the same order, so the arrays must match), compared as partitions with mutual
reachability on random small graphs; the graph of groups; the checker against true and planted
wrong groupings.
"""

from __future__ import annotations

from hypothesis import assume, given
from hypothesis import strategies as st

from algodesign.graphs import (
    Components,
    Digraph,
    check_components,
    condensation,
    kosaraju_sharir,
    naive,
    strong_components,
)
from algodesign.graphs.scc import Walk


@st.composite
def digraphs(draw: st.DrawFn) -> Digraph:
    n = draw(st.integers(0, 7))
    if n == 0:
        return Digraph(0, [])
    vertex = st.integers(0, n - 1)
    return Digraph(n, draw(st.lists(st.tuples(vertex, vertex), max_size=14)))


# 0 -> 1 -> 2 -> 0 and 1 -> 5 -> 6 -> 1 make one group; 3 <-> 4 (4 -> 3 doubled) is a sink group
# that 2 and 5 both reach; 5 has a loop. The walk enters every vertex before 6 climbs back to 1, so
# it stops when done with 2 on the open list and 0, 1, 5, 6 on the path.
PINNED = Digraph(
    7, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 3), (4, 3), (1, 5), (5, 5), (5, 3), (5, 6), (6, 1)]
)


def test_algorithm_t_on_the_pinned_graph() -> None:
    comps = strong_components(PINNED)
    assert comps.group_of == [0, 0, 0, 1, 1, 0, 0]
    assert comps.groups == [[2, 6, 5, 1, 0], [4, 3]]


def test_kosaraju_sharir_on_the_pinned_graph() -> None:
    comps = kosaraju_sharir(PINNED)
    assert comps.group_of == [0, 0, 0, 1, 1, 0, 0]
    assert comps.groups == [[0, 2, 1, 6, 5], [3, 4]]


def test_the_pinned_graph_of_groups_has_one_arrow() -> None:
    q = condensation(PINNED, strong_components(PINNED))
    assert q.n == 2
    assert q.arrows == [(0, 1)]


def test_two_that_reach_each_other_and_one_they_lead_to() -> None:
    # A <-> B -> C.
    g = Digraph(3, [(0, 1), (1, 0), (1, 2)])
    assert strong_components(g) == Components([0, 0, 1], [[1, 0], [2]])
    assert kosaraju_sharir(g) == Components([0, 0, 1], [[0, 1], [2]])
    assert condensation(g, strong_components(g)).arrows == [(0, 1)]


def test_a_vertex_with_a_loop_is_a_cyclic_group_of_one() -> None:
    g = Digraph(2, [(0, 0), (0, 1)])
    assert strong_components(g) == Components([0, 1], [[0], [1]])
    assert kosaraju_sharir(g) == Components([0, 1], [[0], [1]])
    assert condensation(g, strong_components(g)).arrows == [(0, 1)]


def test_doubled_arrows() -> None:
    both_ways = Digraph(2, [(0, 1), (1, 0), (0, 1), (1, 0)])
    assert strong_components(both_ways) == Components([0, 0], [[1, 0]])
    assert condensation(both_ways, strong_components(both_ways)).arrows == []
    one_way = Digraph(2, [(1, 0), (1, 0)])
    assert strong_components(one_way) == Components([1, 0], [[1], [0]])
    assert kosaraju_sharir(one_way) == Components([1, 0], [[1], [0]])


def test_the_graph_of_groups_keeps_one_copy_and_no_loops() -> None:
    # Groups {0, 1} and {2, 3}, joined by four arrows (two doubled), each group with loops.
    g = Digraph(
        4, [(0, 1), (1, 0), (2, 3), (3, 2), (0, 2), (0, 2), (1, 3), (1, 2), (0, 0), (3, 3)]
    )
    comps = strong_components(g)
    q = condensation(g, comps)
    assert q.arrows == [(comps.group_of[0], comps.group_of[2])]


def test_no_vertices() -> None:
    assert strong_components(Digraph(0, [])) == Components([], [])
    assert kosaraju_sharir(Digraph(0, [])) == Components([], [])
    assert condensation(Digraph(0, []), Components([], [])).n == 0
    assert check_components(Digraph(0, []), []) is None


def test_the_checker_names_the_failed_check() -> None:
    a_b_a = Digraph(2, [(0, 1), (1, 0)])
    # Two singletons are each strongly connected; the graph of groups derived from the arrows has
    # the cycle 0 -> 1 -> 0.
    assert check_components(a_b_a, [0, 1]) == "acyclic"
    assert check_components(a_b_a, [0, 0]) is None
    one_way = Digraph(2, [(0, 1)])
    # 1 does not reach 0, so one group cannot hold both.
    assert check_components(one_way, [0, 0]) == "strongly connected"
    assert check_components(one_way, [0, 1]) is None
    assert check_components(one_way, [1, 0]) is None  # any numbering of the right groups
    assert check_components(one_way, [0]) == "partition"
    assert check_components(one_way, [0, 2]) == "partition"
    assert check_components(one_way, [-1, 0]) == "partition"
    assert check_components(one_way, [0, 10**9]) == "partition"


@given(digraphs())
def test_both_methods_find_the_mutual_reachability_groups(g: Digraph) -> None:
    truth = naive.mutual_groups(g)
    for comps in (strong_components(g), kosaraju_sharir(g)):
        assert naive.same_partition(comps.group_of, truth)
        assert sorted(v for members in comps.groups for v in members) == list(range(g.n))
        assert all(comps.group_of[v] == c for c, members in enumerate(comps.groups) for v in members)


@given(digraphs())
def test_group_numbers_are_a_topological_order(g: Digraph) -> None:
    for comps in (strong_components(g), kosaraju_sharir(g)):
        assert all(comps.group_of[v] <= comps.group_of[w] for v, w in g.arrows)


@given(digraphs())
def test_members_come_in_the_order_the_walk_finishes_them(g: Digraph) -> None:
    finish = {v: k for k, v in enumerate(naive.postorder(g))}
    for members in strong_components(g).groups:
        assert members == sorted(members, key=finish.__getitem__)


@given(digraphs())
def test_a_group_of_one_is_cyclic_exactly_when_it_has_a_loop(g: Digraph) -> None:
    for members in strong_components(g).groups:
        if len(members) == 1:
            v = members[0]
            assert (v in naive.reachable(g, [v])) == ((v, v) in g.arrows)


@given(digraphs())
def test_the_graph_of_groups_is_the_arrows_between_groups_once_each(g: Digraph) -> None:
    comps = strong_components(g)
    q = condensation(g, comps)
    between = {(comps.group_of[v], comps.group_of[w]) for v, w in g.arrows}
    assert sorted(q.arrows) == sorted((c, d) for c, d in between if c != d)
    assert len(set(q.arrows)) == len(q.arrows)


@given(digraphs())
def test_the_checker_accepts_both_methods(g: Digraph) -> None:
    assert check_components(g, strong_components(g).group_of) is None
    assert check_components(g, kosaraju_sharir(g).group_of) is None


@given(digraphs(), st.data())
def test_the_checker_rejects_every_wrong_grouping(g: Digraph, data: st.DataObject) -> None:
    truth = strong_components(g).group_of
    assume(g.n > 0)
    wrong = list(truth)
    v = data.draw(st.integers(0, g.n - 1))
    wrong[v] = data.draw(st.integers(-1, g.n))
    assume(not naive.same_partition(wrong, truth))
    assert check_components(g, wrong) is not None


@given(digraphs(), st.data())
def test_the_checker_rejects_random_groupings(g: Digraph, data: st.DataObject) -> None:
    labels = data.draw(st.lists(st.integers(0, g.n), min_size=g.n, max_size=g.n))
    verdict = check_components(g, labels)
    right = naive.same_partition(labels, naive.mutual_groups(g))
    used = set(labels) == set(range(len(set(labels))))
    assert (verdict is None) == (right and used)


def test_walk_states_name_their_broken_piece() -> None:
    # 0 <-> 1 -> 2 after 2 came out, 1 finished onto F, and the walk came back to 0.
    g = Digraph(3, [(0, 1), (1, 0), (1, 2)])
    good = Walk(low=[1, 1, 4], followers=[1, 3], groups=[[2]], pre=[1, 2, 3], finished=[2, 1],
                retreats=[(1, 0), (1, 2), (0, 1)])
    assert good.check_valid(g) is None
    off_f = Walk(**{**good.__dict__, "followers": [3]})
    assert off_f.check_valid(g) == "invariant 1 (followers_in_finish_order)"
    high = Walk(**{**good.__dict__, "low": [1, 2, 4]})
    assert high.check_valid(g) == "invariant 2 (climb_back_is_earliest)"
    forgot = Walk(**{**good.__dict__, "retreats": [(1, 2), (0, 1)]})
    assert forgot.check_valid(g) == "invariant 2 (climb_back_is_earliest)"
    not_done = Walk(**{**good.__dict__, "low": [1, 1, 3]})
    assert not_done.check_valid(g) == "invariant 3 (done_iff_group_out)"


# The chapter's chat: Omar, Amara, Priya, Mateo, Kenji, Sofia = 0 .. 5.
CHAT = Digraph(6, [(4, 5), (3, 1), (1, 3), (1, 0), (1, 2), (2, 3)])


@given(digraphs())
def test_every_state_of_the_walk_is_valid(g: Digraph) -> None:
    states = Walk.trace(g)
    for state in states:
        assert state.check_valid(g) is None
    if g.n:  # the last state has every vertex out, in the groups the walk returns
        assert sorted(states[-1].groups) == sorted(strong_components(g).groups)
        assert states[-1].low == [g.n + 1] * g.n and states[-1].followers == [g.n]


def test_every_state_on_the_pinned_graph_and_the_chat_is_valid() -> None:
    for g in (PINNED, CHAT):
        assert all(state.check_valid(g) is None for state in Walk.trace(g))


def test_the_walk_stops_when_done_at_its_step() -> None:
    # PINNED: everyone is entered when 6 looks along 6 -> 1 and its number drops to 1, 0's own,
    # so that climb back stops the walk, with 2 on the open list and 0, 1, 5, 6 on the path.
    # Without the stop the walk would go on looking and finishing one vertex at a time.
    states = Walk.trace(PINNED)
    assert len(states) == 16
    before, stop = states[-2], states[-1]
    assert before.groups == [[4, 3]] and before.followers == [2, 7]
    assert before.low[6] == 7
    assert stop.groups == [[4, 3], [2, 6, 5, 1, 0]]
    assert stop.retreats[-1] == (6, 1)
    assert stop.finished[-4:] == [6, 5, 1, 0] and stop.followers == [7]
    # The chat: Kenji, the last root, walks down to Sofia, the last vertex entered; her group
    # comes out and the walk comes back over Kenji -> Sofia, which lowers nothing, so it does not
    # stop: Kenji finishes and comes out alone, as at the end of any walk.
    states = Walk.trace(CHAT)
    assert len(states) == 15
    assert states[-2].groups == [[0], [3, 2, 1], [5]]
    assert states[-1].groups == [[0], [3, 2, 1], [5], [4]]
    assert states[-1].retreats == states[-2].retreats


@given(digraphs())
def test_the_groups_agree_with_the_group_ids(g: Digraph) -> None:
    for comps in (strong_components(g), kosaraju_sharir(g)):
        assert sorted(v for members in comps.groups for v in members) == list(range(g.n))
        assert all(comps.group_of[v] == c
                   for c, members in enumerate(comps.groups) for v in members)


def test_both_methods_go_down_a_path_deeper_than_recursion_could() -> None:
    # Both walks keep their path in frames, not on Python's call stack (its limit is about 1,000).
    n = 100_000
    path = Digraph(n, [(v, v + 1) for v in range(n - 1)])
    cycle = Digraph(n, [(v, (v + 1) % n) for v in range(n)])
    for find in (strong_components, kosaraju_sharir):
        assert len(find(path).groups) == n
        assert len(find(cycle).groups) == 1
