# SPDX-License-Identifier: Apache-2.0
"""The trie, checked the way `rust/crates/algodesign/src/strings/trie.rs` checks it, plus the two
measurements the chapter prints.

The fixed cases mirror that module's `#[test]`s one for one; the property test is the Python's
own, because the Rust's trie carries its differential inside `patricia.rs`'s proptest (which
compares the two structures against each other and against a `BTreeMap`). Here the trie is
compared against a `dict` directly, so a trie bug cannot hide behind a matching Patricia bug.
"""

import sys
from collections.abc import Iterator

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from algodesign.strings.patricia import Patricia
from algodesign.strings.trie import ALPHABET, Trie, _Node

# Alphabet `{0, 1, 2}`, small enough that generated keys share prefixes constantly -- which is
# the only way the branching, the shared spine and `longest_prefix`'s backtracking get exercised
# at all. The Rust's proptest generates `0u8..3` for the same reason.
SYMBOLS = st.integers(min_value=0, max_value=2)
keys = st.lists(st.lists(SYMBOLS, max_size=6).map(bytes), max_size=30)
probes = st.lists(st.lists(SYMBOLS, max_size=7).map(bytes), min_size=1, max_size=10)


def every_prefix(key: bytes) -> Iterator[bytes]:
    """Every prefix of `key`, the empty one included."""
    for cut in range(len(key) + 1):
        yield key[:cut]


@given(keys, probes)
@settings(max_examples=50, deadline=None)
def test_matches_a_dict_on_every_query(ks: list[bytes], qs: list[bytes]) -> None:
    """Every operation against a `dict`, which knows nothing about tries.

    Duplicate keys are left in the generator on purpose, so overwrite -- and the old value
    `insert` returns -- is exercised too. Lean: `get_insert` is the statement being checked when
    `get` is asked for a key just inserted; the other keys are the Python's own obligation, since
    that theorem says nothing about them.
    """
    trie: Trie[int] = Trie()
    oracle: dict[bytes, int] = {}
    for i, k in enumerate(ks):
        assert trie.insert(k, i) == oracle.get(k)
        oracle[k] = i
        assert len(trie) == len(oracle)

    assert trie.keys() == sorted(oracle)

    for q in list(qs) + list(ks):
        assert trie.get(q) == oracle.get(q)
        assert trie.contains(q) == (q in oracle)

        longest = max(
            (k for k in oracle if q.startswith(k)), key=len, default=None
        )
        assert trie.longest_prefix(q) == longest

        for p in every_prefix(q):
            assert trie.keys_with_prefix(p) == sorted(k for k in oracle if k.startswith(p))


def test_stores_and_retrieves() -> None:
    """Mirrors `stores_and_retrieves`. `shell` is a path in the trie but not a key: the node is
    there, holding no value."""
    trie: Trie[int] = Trie()
    trie.insert(b"she", 0)
    trie.insert(b"shells", 1)
    trie.insert(b"sea", 2)
    assert trie.get(b"shells") == 1
    assert trie.get(b"shell") is None
    assert not trie.contains(b"shell")
    assert trie.keys_with_prefix(b"sh") == [b"she", b"shells"]
    assert trie.longest_prefix(b"shellsort") == b"she" + b"lls"


def test_empty_trie_has_no_keys_and_a_root_only_node_count() -> None:
    """Mirrors `empty_trie_has_no_keys_and_a_root_only_node_count`. The root is always there, so
    the count is 1 -- the convention `Patricia.node_count` repeats so the two compare."""
    trie: Trie[int] = Trie()
    assert len(trie) == 0
    assert trie.node_count() == 1
    assert trie.get(b"") is None
    assert trie.get(b"x") is None
    assert trie.longest_prefix(b"x") is None
    assert trie.keys() == []


def test_insert_overwrite_returns_the_old_value_and_does_not_grow_len() -> None:
    """Mirrors `insert_overwrite_returns_the_old_value_and_does_not_grow_len`."""
    trie: Trie[int] = Trie()
    assert trie.insert(b"a", 1) is None
    assert len(trie) == 1
    assert trie.insert(b"a", 2) == 1
    assert len(trie) == 1
    assert trie.get(b"a") == 2


def test_empty_key_is_a_valid_key() -> None:
    """Mirrors `empty_key_is_a_valid_key`: the root holds a value like any other node, and it is
    then a prefix of everything."""
    trie: Trie[int] = Trie()
    assert trie.insert(b"", 7) is None
    assert trie.get(b"") == 7
    assert trie.longest_prefix(b"anything") == b""


def test_keys_with_prefix_of_an_absent_path_is_empty() -> None:
    """Mirrors `keys_with_prefix_of_an_absent_path_is_empty`."""
    trie: Trie[int] = Trie()
    trie.insert(b"she", 0)
    assert trie.keys_with_prefix(b"zz") == []


def test_a_stored_none_is_still_a_key() -> None:
    """The one place this rendering has to say something the Rust does not.

    Rust's node holds `Option<V>`, which nests, so `Some(None)` and `None` are different values.
    Python's `None` does not nest, so presence is tracked separately and `contains` is the exact
    question; `get` keeps the ordinary mapping convention and cannot tell the two apart. What
    must not happen is the structure losing count of the key, and that is what this pins.
    """
    trie: Trie[None] = Trie()
    trie.insert(b"k", None)
    assert len(trie) == 1
    assert trie.keys() == [b"k"]
    assert trie.contains(b"k")
    assert trie.get(b"k") is None
    assert not trie.contains(b"absent")


def test_the_worked_example_counts_seventeen_nodes() -> None:
    """The chapter's worked example, half of it: `she/shells/sea/shore/seashore` as a trie.

    Seventeen nodes, root included -- one per distinct non-empty prefix of the five words, plus
    the root. `test_patricia.py` pins the other half at eight: path compression saves nine nodes.
    """
    words = [b"she", b"shells", b"sea", b"shore", b"seashore"]
    trie: Trie[int] = Trie()
    for i, w in enumerate(words):
        trie.insert(w, i)

    distinct_prefixes = {p for w in words for p in every_prefix(w)}
    assert len(distinct_prefixes) == 17  # the root's empty path is one of them
    assert trie.node_count() == 17
    assert trie.keys() == sorted(words)


def test_the_r_way_trie_is_larger_than_the_strings_it_stores() -> None:
    """A trie is not always smaller -- with a sparse alphabet and no shared prefixes it is
    dramatically larger, and this is the arithmetic that says so.

    Six keys, distinct first bytes, twenty-four bytes each, nothing shared. The trie spends a
    node per byte, and the R-way shape spends `ALPHABET` child slots per node whether or not they
    are used, so the structure holding 144 bytes of keys carries 37 120 child slots -- more than
    two hundred slots for every byte it was given. Path compression is one of the two things that
    fix it: the same keys, the same bytes, six edges and seven nodes.

    These are counts, not timings. Nothing here is a performance claim; it is the size of the
    representation. The slot count is computed rather than
    observed, because this rendering files children in a `dict` -- `ALPHABET` is the Rust's
    array, named here so the number is checkable instead of asserted.
    """
    words = [bytes([c]) * 24 for c in b"bdfhjl"]
    trie: Trie[int] = Trie()
    pat: Patricia[int] = Patricia()
    for i, w in enumerate(words):
        trie.insert(w, i)
        pat.insert(w, i)

    stored_bytes = sum(len(w) for w in words)
    assert stored_bytes == 144
    # One node per byte of key, plus the root: 6 keys of 24 bytes, none of them shared.
    assert trie.node_count() == 1 + 6 * 24
    assert trie.node_count() == 145
    assert trie.node_count() * ALPHABET == 37_120  # the R-way array's child slots
    assert trie.node_count() * ALPHABET > 200 * stored_bytes

    # One edge per key, plus the root -- the labels hold the same 144 bytes.
    assert pat.node_count() == 1 + 6
    assert pat.node_count() == 7
    assert pat.keys() == trie.keys()  # Lean: words_perm_ofTrie, as sorted lists


def test_a_long_thin_trie_survives_a_raised_recursion_limit() -> None:
    """A long, thin trie, in the language that is allowed to recurse.

    A single 5 000-byte key is a 5 000-deep chain, and `keys`, `keys_with_prefix` and
    `node_count` walk it by recursion because that is how a tree walk reads. The limit is
    therefore raised explicitly here rather than pretended away: the default is 1 000, so without
    this the walk raises `RecursionError` at depth 1 000 and the reader would learn nothing about
    where the real ceiling is. The descents -- `insert`, `get`, `longest_prefix` -- are loops and
    would pass at any limit.
    """
    depth = 5_000
    key = b"a" * depth
    trie: Trie[int] = Trie()
    trie.insert(key, 1)

    assert trie.get(key) == 1  # a loop: unaffected by the limit
    assert trie.longest_prefix(key + b"bb") == key

    # The documented limit: at the default, the walks run out of frames on this chain.
    assert sys.getrecursionlimit() < depth
    with pytest.raises(RecursionError):
        trie.keys()

    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(depth + 1_000)
    try:
        assert trie.node_count() == depth + 1
        assert trie.keys() == [key]
        assert trie.keys_with_prefix(b"a" * (depth // 2)) == [key]
    finally:
        sys.setrecursionlimit(previous)


# --- remove ----------------------------------------------------------------------------------

ops = st.lists(
    st.tuples(st.booleans(), st.lists(SYMBOLS, max_size=6).map(bytes)), max_size=60
)
"""`(insert?, key)` pairs: an insert stores the step's index, a remove takes the key out."""


@given(ops)
@settings(deadline=None)
def test_insert_and_remove_match_a_dict_and_keep_the_shape(
    steps: list[tuple[bool, bytes]],
) -> None:
    """Mirrors `matches_a_btreemap_and_keeps_its_count` with its removes: after every step, the
    answer it returned, `len`, the keys, `node_count` against a trie built by inserting the
    dict's keys afresh, and `is_valid`. A remove that cleared the value but left its
    path answers every query right and fails the count and `is_no_dead_branches`, at the step that
    did it."""
    trie: Trie[int] = Trie()
    model: dict[bytes, int] = {}
    for i, (is_insert, key) in enumerate(steps):
        if is_insert:
            assert trie.insert(key, i) == model.get(key)
            model[key] = i
        else:
            assert trie.remove(key) == model.pop(key, None)
        assert len(trie) == len(model)
        assert trie.keys() == sorted(model)
        rebuilt: Trie[int] = Trie()
        for k in model:
            rebuilt.insert(k, model[k])
        assert trie.node_count() == rebuilt.node_count()
        assert trie.is_valid(), f"invalid after step {i}"
    for _, key in steps:
        assert trie.get(key) == model.get(key)


def test_remove_takes_only_the_unshared_suffix_of_the_path() -> None:
    """Mirrors the Rust test of the same name: `remove` walks back up to the first node another
    key still needs."""
    trie: Trie[int] = Trie()
    for i, w in enumerate([b"she", b"shells", b"sea"]):
        trie.insert(w, i)
    before = trie.node_count()
    assert trie.remove(b"shell") is None  # a bare prefix: nothing changes
    assert trie.remove(b"shellsort") is None  # absent
    assert trie.node_count() == before
    assert trie.remove(b"shells") == 1
    assert trie.node_count() == before - 3
    assert trie.remove(b"she") == 0
    assert trie.node_count() == before - 5
    assert trie.get(b"sea") == 2
    assert trie.remove(b"sea") == 2
    assert (len(trie), trie.node_count()) == (0, 1)


def test_removing_a_key_that_others_extend_keeps_their_path() -> None:
    trie: Trie[int] = Trie()
    trie.insert(b"", 0)
    trie.insert(b"ab", 1)
    trie.insert(b"abc", 2)
    before = trie.node_count()
    assert trie.remove(b"ab") == 1
    assert trie.node_count() == before
    assert trie.remove(b"") == 0
    assert trie.longest_prefix(b"abcd") == b"abc"


def test_a_stored_none_is_removed_and_reported_as_none() -> None:
    """`remove` answers `None` for a stored `None` too, as `get` does; `contains` separates the
    two before the call."""
    trie: Trie[int | None] = Trie()
    trie.insert(b"k", None)
    assert trie.contains(b"k")
    assert trie.remove(b"k") is None
    assert not trie.contains(b"k") and len(trie) == 0


# --- is_valid ------------------------------------------------------------------------------------


def test_a_dead_branch_breaks_is_no_dead_branches_alone() -> None:
    """Mirrors the Rust's hand-built dead branch: a valueless, childless node under byte 3, written
    into the nodes directly, as no operation would leave it."""
    trie: Trie[int] = Trie()
    trie.insert(b"ab", 0)
    trie.root.children[3] = _Node()
    assert trie.is_distinct_letters()
    assert not trie.is_no_dead_branches()
    assert trie.is_len_matches()
    assert trie.check_valid() == "invariant 3 (no_dead_branches)"


def test_a_wrong_len_breaks_len_matches_alone() -> None:
    trie: Trie[int] = Trie()
    trie.insert(b"ab", 0)
    trie._len += 1
    assert trie.is_no_dead_branches()
    assert not trie.is_len_matches()
    assert trie.check_valid() == "layout (len_matches)"


def test_the_empty_trie_is_valid() -> None:
    """The root is exempt from `is_no_dead_branches`: the empty trie is one valueless, childless
    node."""
    trie: Trie[int] = Trie()
    assert trie.is_valid()


def test_a_str_key_is_refused() -> None:
    """A key is `bytes`. A `str` would be stored under its characters and then break `keys()`,
    which rebuilds each key from byte values, so `insert` refuses it."""
    trie: Trie[int] = Trie()
    with pytest.raises(TypeError, match="bytes"):
        trie.insert("tea", 1)  # type: ignore[arg-type]
    assert len(trie) == 0
    assert trie.is_valid()
