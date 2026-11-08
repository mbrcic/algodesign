# SPDX-License-Identifier: Apache-2.0
"""The Search chapter: one module per search structure or algorithm.

The trees and the LSM-tree are classes, exported by name. The two searches are functions, reached
through their modules: `binary_search.search`, `sequential_search.contains`,
`sequential_search.build`. `workbench` is the chapter's design project's bench, not a structure.
"""

from __future__ import annotations

from . import binary_search, sequential_search, workbench
from .bst import BST
from .btree import BTree
from .llrb import LLRB
from .lsm import LSM
from .red_black_standard import RBTree
from .treap import Treap

__all__ = [
    "BST",
    "BTree",
    "LLRB",
    "LSM",
    "RBTree",
    "Treap",
    "binary_search",
    "sequential_search",
    "workbench",
]
