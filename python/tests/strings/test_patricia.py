# SPDX-License-Identifier: Apache-2.0
"""The Patricia tree, checked the way `rust/crates/algodesign/src/strings/patricia.rs` checks it.

The property test mirrors that module's single proptest, statement for statement: the same
alphabet and sizes, `is_valid()` after *every* insert, and every query compared against two
independent oracles at once -- a `Trie`, which is the same key set in the uncompressed
representation, and a `dict`, which knows nothing about tries. The fixed cases mirror its
`#[test]`s, including the two trees built node by node to show box lines 3 and 4 each failing on
its own.

**Why `is_valid()` is asserted after every insert and not once at the end.** Lean's
`branchesUnlessWordEnds_ofTrie` and `noEmptyBranches_ofTrie` prove box lines 3 and 4 of `ofTrie`,
the one-pass collapse of a finished trie. This module inserts incrementally and splits edges,
which is a different algorithm carrying the same obligation. The Lean proves it for that algorithm
too (`valid_insert`), but of the Lean `insert`, not of this module; asserting after every insert is
what checks this code, and a shape a later insert happens to repair was still broken by the one
before it.
"""

import sys
from collections.abc import Iterator

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings.patricia import Patricia, _Node
from algodesign.strings.trie import Trie

SYMBOLS = st.integers(min_value=0, max_value=2)
keys = st.lists(st.lists(SYMBOLS, max_size=6).map(bytes), max_size=30)
probes = st.lists(st.lists(SYMBOLS, max_size=7).map(bytes), min_size=1, max_size=10)

WORDS = [b"she", b"shells", b"sea", b"shore", b"seashore"]
"""The chapter's worked example. The values below are always `WORDS.index(w)`, never the position
in whatever order a test inserts them, so that the shape a test pins is comparable across
insertion orders."""


def every_prefix(key: bytes) -> Iterator[bytes]:
    """Every prefix of `key`, the empty one included."""
    for cut in range(len(key) + 1):
        yield key[:cut]


def shape(node: _Node[int]) -> dict[bytes, tuple[int | None, object]]:
    """The tree below `node` as nested dicts: `{edge label: (value there, children)}`.

    Reaches into `_Node` on purpose. `node_count` alone cannot pin a shape -- two different trees
    can hold the same number of nodes -- and shape is how the algorithm's variant is observed. So
    the worked example is pinned as a picture, not only as a count.
    """
    return {
        child.label: (child.value if child.has_value else None, shape(child))
        for _, child in sorted(node.children.items())
    }


def build(words: list[bytes]) -> Patricia[int]:
    """`words` inserted in the order given, each holding its index in `WORDS`."""
    pat: Patricia[int] = Patricia()
    for w in words:
        pat.insert(w, WORDS.index(w))
    return pat


@given(keys, probes)
@settings(max_examples=50, deadline=None)
def test_matches_a_trie_and_a_dict_while_staying_valid(
    ks: list[bytes], qs: list[bytes]
) -> None:
    """Mirrors `matches_a_trie_and_a_btreemap_while_staying_valid`.

    Two oracles, because they fail differently: the `Trie` catches a compression that moved a
    key, and the `dict` catches a bug the two structures could share. Duplicate keys stay in the
    generator so overwrite is exercised.

    Lean: the sorted `keys_with_prefix` comparison against the trie is `words_perm_ofTrie`, the
    permutation form -- `words_ofTrie` is stronger, an equality in Lean's own child order, and is
    about `ofTrie`'s output rather than about these two independently built structures.
    """
    pat: Patricia[int] = Patricia()
    trie: Trie[int] = Trie()
    oracle: dict[bytes, int] = {}
    for i, k in enumerate(ks):
        old = oracle.get(k)
        assert pat.insert(k, i) == old
        assert trie.insert(k, i) == old
        oracle[k] = i
        assert pat.is_valid()  # the obligation the Lean discharges for its own insert only
        assert len(pat) == len(oracle)
        assert len(pat) == len(trie)

    for q in list(qs) + list(ks):
        assert pat.get(q) == oracle.get(q)
        assert pat.get(q) == trie.get(q)
        assert pat.contains(q) == (q in oracle)

        longest = max((k for k in oracle if q.startswith(k)), key=len, default=None)
        assert pat.longest_prefix(q) == longest
        assert pat.longest_prefix(q) == trie.longest_prefix(q)

        for p in every_prefix(q):
            mine = pat.keys_with_prefix(p)
            assert mine == sorted(k for k in oracle if k.startswith(p))
            assert mine == trie.keys_with_prefix(p)


def test_the_worked_example_is_eight_nodes_and_this_shape() -> None:
    """The chapter's worked example, the Patricia half.

    `she/shells/sea/shore/seashore` is 17 nodes as a trie (pinned in `test_trie.py`) and 8 here,
    both counts root-inclusive: `root -> "s" -> { "ea" -> "shore"; "h" -> { "e" -> "lls";
    "ore" } }`. The count and the picture are both pinned, because a count alone does not say
    which tree was built.

    Nine bytes of the five words went into edge labels rather than into nodes of their own --
    that is all that happened. Every byte of every key is still present, in order, spread across
    the labels on the path to it: `keys()` reads them back.
    """
    pat = build(WORDS)
    assert pat.node_count() == 8
    assert len(pat) == 5
    assert pat.is_valid()
    assert pat.keys() == sorted(WORDS)
    assert shape(pat.root) == {
        b"s": (
            None,
            {
                b"ea": (2, {b"shore": (4, {})}),
                b"h": (
                    None,
                    {
                        b"e": (0, {b"lls": (1, {})}),
                        b"ore": (3, {}),
                    },
                ),
            },
        )
    }


def test_the_worked_examples_shape_does_not_depend_on_insertion_order() -> None:
    """The same five words, inserted back to front, build the same tree.

    Worth pinning because the shape pinned above is reached by a particular sequence of edge
    splits, and it would be easy to read the picture as an artefact of that sequence. It is not:
    a Patricia tree's shape is a function of its key set (and `remove` keeps it so, which
    `test_insert_and_remove_keep_the_shape` checks). That is also what
    makes the 8 in the chapter a property of the example rather than of the order it is printed
    in.
    """
    forwards = build(WORDS)
    backwards = build(list(reversed(WORDS)))
    assert shape(backwards.root) == shape(forwards.root)
    assert backwards.node_count() == forwards.node_count() == 8


def test_same_keys_fewer_nodes_than_the_trie() -> None:
    """Mirrors `same_keys_fewer_nodes_than_the_trie`: both node counts, trie and Patricia.

    Lean: `words_perm_ofTrie` for the key lists (compared here as sorted lists), and nothing at
    all for the node counts -- the counts are a measurement, which is why they are taken rather
    than asserted.
    """
    pat = build(WORDS)
    trie: Trie[int] = Trie()
    for w in WORDS:
        trie.insert(w, WORDS.index(w))

    assert pat.keys() == trie.keys()
    assert pat.node_count() == 8
    assert trie.node_count() == 17
    assert pat.node_count() < trie.node_count()


def test_no_valueless_single_child_chain_survives() -> None:
    """Mirrors `no_valueless_single_child_chain_survives`. `roman`/`rom` are chains in the trie
    and single edges here."""
    pat: Patricia[int] = Patricia()
    for w in [b"romane", b"romanus", b"romulus"]:
        pat.insert(w, 0)
    assert pat.is_branches_unless_word_ends()
    assert pat.node_count() == 6  # root, "rom", "an", "e", "us", "ulus"


def test_root_with_one_child_is_valid() -> None:
    """Mirrors `root_with_one_child_is_valid`: the shape the root exemption exists for.

    A single key compresses to a valueless root with exactly one child. So does any key set whose
    keys share a first byte -- which is most of them. That shape is compression's own output
    (`branchesUnlessWordEnds_ofTrie`), and a box line rejecting it would be rejecting the
    theorem. The rule is waived at the root because it cannot be enforced there, not because a
    root could never meet it: a valueless root with one child has no incoming edge for that child
    to be merged into, so no compression step can remove it.
    """
    pat: Patricia[int] = Patricia()
    pat.insert(b"abc", 0)
    assert pat.node_count() == 2  # root plus one leaf, no chain
    assert pat.is_valid()

    shared: Patricia[int] = Patricia()
    for w in [b"abc", b"abd", b"axy"]:
        shared.insert(w, 0)
    assert len(shared.root.children) == 1  # the exempt shape, from three keys
    assert not shared.root.has_value
    assert shared.is_valid()


def test_below_root_valueless_single_child_chain_breaks_branches_unless_word_ends() -> None:
    """Mirrors `below_root_valueless_single_child_chain_breaks_branches_unless_word_ends`.

    Built node by node rather than through `insert`, because `insert` never produces this shape
    -- it is exactly what box line 3 exists to reject, one level below the root where the
    exemption does not reach. A gate that cannot fail establishes nothing, so this is the failure.
    """
    leaf: _Node[int] = _Node(b"b")
    leaf.value = 1
    leaf.has_value = True
    chain: _Node[int] = _Node(b"a")
    chain.children[ord("b")] = leaf

    pat: Patricia[int] = Patricia()
    pat.root.children[ord("a")] = chain
    pat._len = 1
    assert not pat.is_branches_unless_word_ends()


def test_an_empty_edge_label_below_the_root_breaks_no_empty_branches() -> None:
    """Mirrors `an_empty_edge_label_below_the_root_breaks_no_empty_branches`.

    Box line 4 on its own: this node has two children, so box line 3 would not reject it. `insert` never produces an empty label below the root
    either.

    The child is filed under `b"a"` although its label is empty -- deliberately breaking the
    "a child's dict key is its label's first byte" correspondence `insert` always maintains,
    because an empty label has no first byte. Do not "fix" it: there is no byte to use, and
    filing it under a real one would stop this fixture testing the check it exists for.
    """
    x: _Node[int] = _Node(b"x")
    x.value = 1
    x.has_value = True
    y: _Node[int] = _Node(b"y")
    y.value = 2
    y.has_value = True
    bad: _Node[int] = _Node(b"")  # empty: the invariant this test violates
    bad.children[ord("x")] = x
    bad.children[ord("y")] = y

    pat: Patricia[int] = Patricia()
    pat.root.children[ord("a")] = bad
    pat._len = 2
    assert not pat.is_no_empty_branches()


def test_stores_and_retrieves() -> None:
    """Mirrors `stores_and_retrieves`. `shell` ends strictly inside an edge label, so there is no
    node to ask and it is not a key."""
    pat: Patricia[int] = Patricia()
    pat.insert(b"she", 0)
    pat.insert(b"shells", 1)
    pat.insert(b"sea", 2)
    assert pat.get(b"shells") == 1
    assert pat.get(b"shell") is None
    assert not pat.contains(b"shell")
    assert pat.keys_with_prefix(b"sh") == [b"she", b"shells"]
    assert pat.longest_prefix(b"shellsort") == b"shells"


def test_keys_with_prefix_of_a_prefix_ending_inside_a_label() -> None:
    """The case `Trie.keys_with_prefix` does not have: the query stops mid-edge.

    `shel` ends four bytes into the `lls` edge's path. Every key below that edge still begins
    with `shel`, so the whole label finishes the path and the subtree is the answer.
    """
    pat = build(WORDS)
    assert pat.keys_with_prefix(b"shel") == [b"shells"]
    assert pat.keys_with_prefix(b"shex") == []
    assert pat.keys_with_prefix(b"seas") == [b"seashore"]


def test_inserting_a_proper_prefix_of_an_existing_key_splits_at_the_label_end() -> None:
    """Mirrors `inserting_a_proper_prefix_of_an_existing_key_splits_exactly_at_the_label_end`.

    `insert`'s "the key ends exactly where it diverges" arm, which no other test here reaches:
    every other split has the new key outlast the divergence. By the time `shell` arrives,
    `shells` has been folded into an `lls` leaf edge under an `e` node, and `shell` ends exactly
    at the `ll`/`s` boundary inside that edge -- so the split makes a valued `ll` node with an
    `s` leaf child. One leaf becomes a node plus a leaf: net one more node.
    """
    pat = build(WORDS)
    before = pat.node_count()
    assert pat.insert(b"shell", 99) is None
    assert pat.get(b"shells") == 1  # untouched by the split
    assert pat.get(b"shell") == 99
    assert pat.is_valid()  # the arm's point: the split lands back in the invariant
    assert pat.node_count() == before + 1


def test_empty_patricia_has_no_keys_and_a_root_only_node_count() -> None:
    """Mirrors `empty_patricia_has_no_keys_and_a_root_only_node_count`."""
    pat: Patricia[int] = Patricia()
    assert len(pat) == 0
    assert pat.node_count() == 1
    assert pat.get(b"") is None
    assert pat.get(b"x") is None
    assert pat.longest_prefix(b"x") is None
    assert pat.keys() == []
    assert pat.is_valid()  # vacuously: the root has no children to check


def test_insert_overwrite_returns_the_old_value_and_does_not_grow_len() -> None:
    """Mirrors `insert_overwrite_returns_the_old_value_and_does_not_grow_len`."""
    pat: Patricia[int] = Patricia()
    assert pat.insert(b"a", 1) is None
    assert len(pat) == 1
    assert pat.insert(b"a", 2) == 1
    assert len(pat) == 1
    assert pat.get(b"a") == 2


def test_empty_key_is_a_valid_key() -> None:
    """Mirrors `empty_key_is_a_valid_key`: the root holds it, needing no edge."""
    pat: Patricia[int] = Patricia()
    assert pat.insert(b"", 7) is None
    assert pat.get(b"") == 7
    assert pat.longest_prefix(b"anything") == b""
    assert pat.is_valid()


def test_node_count_is_bounded_by_twice_len() -> None:
    """Mirrors `node_count_is_bounded_by_twice_len`.

    `n` values give at most `n` leaves and at most `n - 1` valueless branching nodes below the
    root, plus the root: at most `2n` nodes. The bound is by key *count*, where a trie's is by
    total key *length* -- which is the difference collapsing the chains makes.
    """
    pat = build(WORDS)
    assert pat.node_count() <= 2 * len(pat)


def test_a_stored_none_is_still_a_key() -> None:
    """The same divergence `test_trie.py` pins, and for the same reason: Lean's `Option α` does
    not survive the trip to Python, so presence is tracked apart from the value and `contains`
    stays exact."""
    pat: Patricia[None] = Patricia()
    pat.insert(b"k", None)
    assert len(pat) == 1
    assert pat.keys() == [b"k"]
    assert pat.contains(b"k")
    assert pat.get(b"k") is None


def deep_chain(depth: int) -> Patricia[int]:
    """A `depth`-deep chain of single-byte edges, every node holding a value.

    Built bottom-up rather than through `insert`, for the reason the Rust's `deep_chain` gives:
    each `insert` re-descends the whole chain, so building depth `n` that way is O(n^2) in byte
    comparisons. This is O(n), and it is itself the demonstration that nothing in this module
    forces recursion to *build* a deep tree -- only to walk one.
    """
    node: _Node[int] = _Node(b"a")
    node.value = 0
    node.has_value = True
    for _ in range(1, depth):
        parent: _Node[int] = _Node(b"a")
        parent.value = 0
        parent.has_value = True
        parent.children[ord("a")] = node
        node = parent
    pat: Patricia[int] = Patricia()
    pat.root.children[ord("a")] = node
    pat._len = depth
    return pat


def test_a_deep_chain_survives_a_raised_recursion_limit() -> None:
    """A deep chain in a Patricia tree -- harder to reach than in a trie.

    Every edge eats at least one byte, so a single long key is *one* edge: reaching depth takes
    many keys sharing a growing prefix, one value per level, which is what `deep_chain` builds.
    `node_count` and `keys` both recurse once per level, so the limit is raised
    explicitly here rather than pretended away -- the default 1 000 would raise `RecursionError`
    two thirds of the way down. The descents -- `get`, `longest_prefix` -- are loops and pass at
    any limit.
    """
    depth = 3_000
    pat = deep_chain(depth)
    key = b"a" * depth

    assert pat.get(key) == 0  # a loop: unaffected by the limit
    assert pat.longest_prefix(key + b"bb") == key

    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(depth + 1_000)
    try:
        assert pat.is_branches_unless_word_ends() and pat.is_no_empty_branches()
        assert pat.node_count() == depth + 1
        assert len(pat.keys()) == depth
    finally:
        sys.setrecursionlimit(previous)


# --- remove ----------------------------------------------------------------------------------

ops = st.lists(
    st.tuples(st.booleans(), st.lists(SYMBOLS, max_size=6).map(bytes)), max_size=60
)
"""`(insert?, key)` pairs: an insert stores the step's index, a remove takes the key out."""


@given(ops)
@settings(deadline=None)
def test_insert_and_remove_keep_the_shape(steps: list[tuple[bool, bytes]]) -> None:
    """Mirrors `insert_and_remove_keep_the_shape`: inserts and removes mixed, against a `dict`.
    After every step -- the answer it returned, `len`, the keys, `is_valid`, and the shape of a
    tree built by inserting the dict's keys afresh, which is the one tree that key set has. A remove that left a merge undone or a valueless leaf behind answers
    every query right and fails here, at the step that did it."""
    pat: Patricia[int] = Patricia()
    model: dict[bytes, int] = {}
    for i, (is_insert, key) in enumerate(steps):
        if is_insert:
            assert pat.insert(key, i) == model.get(key)
            model[key] = i
        else:
            assert pat.remove(key) == model.pop(key, None)
        assert len(pat) == len(model)
        assert pat.keys() == sorted(model)
        assert pat.is_valid(), f"invalid after step {i}"
        rebuilt: Patricia[int] = Patricia()
        for k in sorted(model):
            rebuilt.insert(k, model[k])
        assert shape(pat.root) == shape(rebuilt.root)
    for _, key in steps:
        assert pat.get(key) == model.get(key)


def test_removing_a_leaf_re_collapses_its_parent() -> None:
    """Removing a leaf leaves its parent valueless with one child, and the parent is merged into
    that child."""
    pat: Patricia[int] = Patricia()
    for i, w in enumerate([b"analogy", b"analysis", b"an"]):
        pat.insert(w, i)
    assert shape(pat.root) == {b"an": (2, {b"al": (None, {b"ogy": (0, {}), b"ysis": (1, {})})})}
    assert pat.remove(b"analysis") == 1
    assert shape(pat.root) == {b"an": (2, {b"alogy": (0, {})})}
    assert pat.is_valid()


def test_removing_an_inner_key_merges_its_node_into_the_only_child() -> None:
    pat: Patricia[int] = Patricia()
    pat.insert(b"ab", 0)
    pat.insert(b"abcd", 1)
    assert pat.remove(b"ab") == 0
    assert shape(pat.root) == {b"abcd": (1, {})}
    assert pat.remove(b"abc") is None  # inside a label: nothing changes
    assert pat.remove(b"abcd") == 1
    assert (len(pat), pat.node_count()) == (0, 1)


def test_remove_leaves_the_root_alone() -> None:
    """The root stays, valueless with one child, when that is what is left: the exemption."""
    pat: Patricia[int] = Patricia()
    pat.insert(b"", 0)
    pat.insert(b"xy", 1)
    assert pat.remove(b"") == 0
    assert shape(pat.root) == {b"xy": (1, {})}
    assert pat.is_valid()
    assert pat.remove(b"") is None


# --- is_valid: one hand-built tree per piece ---------------------------------------------------
# Each starts from a valid tree and breaks one thing by writing the nodes directly, as no operation
# would. Mirrors the Rust's trees in `unit_tests/patricia.rs`, less the order case: a `dict` has no
# child order to break.


def _valued(label: bytes, value: int) -> _Node[int]:
    node: _Node[int] = _Node(label)
    node.value = value
    node.has_value = True
    return node


def _conjuncts(pat: Patricia[int]) -> list[bool]:
    """`is_valid`'s five checks in its order: the three pieces, then the layout."""
    return [
        pat.is_distinct_first_letters(),
        pat.is_branches_unless_word_ends(),
        pat.is_no_empty_branches(),
        pat.is_children_filed_by_head(),
        pat.is_len_matches(),
    ]


def _ab() -> Patricia[int]:
    pat: Patricia[int] = Patricia()
    pat.insert(b"ab", 0)
    pat.insert(b"b", 1)
    assert pat.is_valid()
    return pat


def test_a_valueless_leaf_breaks_is_branches_unless_word_ends_alone() -> None:
    """The case that separates box invariant 3 from box invariant 4: a valueless leaf breaks only
    the first."""
    pat = _ab()
    pat.root.children[3] = _Node(b"\x03")
    assert _conjuncts(pat) == [True, False, True, True, True]
    assert pat.check_valid() == "invariant 3 (branches_unless_word_ends)"


def test_a_child_filed_under_another_byte_breaks_children_filed_by_head_alone() -> None:
    """The label begins with 3, the key says 4: heads still distinct."""
    pat = _ab()
    pat.root.children[4] = _valued(b"\x03", 2)
    pat._len += 1
    assert _conjuncts(pat) == [True, True, True, False, True]
    assert pat.check_valid() == "layout (children_filed_by_head)"


def test_a_wrong_len_breaks_len_matches_alone() -> None:
    pat = _ab()
    pat._len += 1
    assert _conjuncts(pat) == [True, True, True, True, False]
    assert pat.check_valid() == "layout (len_matches)"


def test_two_labels_with_one_head_break_is_distinct_first_letters() -> None:
    """A sibling of `ab` that also begins with `a`, filed under another key: `dict` keys are
    distinct, so children filed by their heads have distinct heads, and the key of one of the two
    is not its head."""
    pat = _ab()
    pat.root.children[5] = _valued(b"a\x09", 2)
    pat._len += 1
    assert _conjuncts(pat) == [False, True, True, False, True]
    assert pat.check_valid() == "invariant 2 (distinct_first_letters)"


def test_two_empty_labels_share_the_head_none() -> None:
    """The Lean's `head?` gives an empty label the head `none`; one is a head like any other, two
    are a repeat. Read from the labels, not the keys, which differ."""
    pat = _ab()
    pat.root.children[6] = _valued(b"", 2)
    pat._len += 1
    assert pat.is_distinct_first_letters()
    pat.root.children[7] = _valued(b"", 3)
    pat._len += 1
    assert not pat.is_distinct_first_letters()
    assert not pat.is_no_empty_branches() and not pat.is_children_filed_by_head()


def test_the_root_is_exempt_from_box_invariant_3_but_not_from_the_heads() -> None:
    """A valueless root with one child keeps box invariant 3; its child list is still read for
    heads."""
    pat: Patricia[int] = Patricia()
    pat.insert(b"xy", 0)
    assert pat.is_valid()
    pat.root.children[ord("y")] = _valued(b"x", 1)
    pat._len += 1
    assert pat.is_branches_unless_word_ends()
    assert not pat.is_distinct_first_letters()


def test_a_str_key_is_refused() -> None:
    """A key is `bytes`; `insert` refuses a `str` rather than store a label `keys()` cannot join."""
    pat: Patricia[int] = Patricia()
    with pytest.raises(TypeError, match="bytes"):
        pat.insert("tea", 1)  # type: ignore[arg-type]
    assert len(pat) == 0
    assert pat.is_valid()


def test_a_relabelled_edge_fails_a_check_only_when_its_first_letter_moves() -> None:
    """Box invariant 1 is what `get` means. Relabel the `she` edge to start with another letter
    and it is filed under the wrong byte; change it after the first letter and the tree is a legal
    one for other words, which only a comparison with the words put in can see."""
    pat: Patricia[int] = Patricia()
    pat.insert(b"she", 1)
    pat.insert(b"shells", 2)
    edge = pat.root.children[ord("s")]
    edge.label = b"xhe"
    assert pat.check_valid() == "layout (children_filed_by_head)"
    edge.label = b"sx"
    assert pat.check_valid() is None
    assert sorted(pat.keys()) == [b"sx", b"sxlls"]
