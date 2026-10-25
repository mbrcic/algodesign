# SPDX-License-Identifier: Apache-2.0
"""The type every ordered structure in this chapter asks of its keys: they can be compared."""

from __future__ import annotations

from typing import Any, Protocol


class SupportsLT(Protocol):
    """Keys with a total order whose `==` agrees with it: `a == b` exactly when neither `a < b`
    nor `b < a`. Numbers (but not `nan`), strings, bytes, and tuples of those qualify; a class
    that defines only `__lt__` does not.

    The protocol can ask only for `<`; the agreement of `==` is the caller's promise. Some of the
    chapter's procedures decide a match with `==` (the BST's `insert` and `floor`, binary search,
    the B-tree, the LSM-tree), the others with two `<` tests, so a key that breaks the promise
    gets different answers from different structures.
    """

    def __lt__(self, other: Any, /) -> bool: ...
