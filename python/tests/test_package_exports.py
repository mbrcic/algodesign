# SPDX-License-Identifier: Apache-2.0
"""What the topic packages export, pinned.

Each package's `__all__` is held to a literal list, and every name in it imports from the package.
Every module imports as a module: a function exported under its own module's name (`binary_search`,
`suffix_array`, `lcp`) would replace the module on the package, so `import
algodesign.strings.suffix_array as S` would give the function.
"""

from __future__ import annotations

import importlib
import pkgutil
import types

import pytest

import algodesign.contracts as contracts
import algodesign.geometry as geometry
import algodesign.searching as searching
import algodesign.strings as strings

EXPORTS = {
    contracts: {"ball_weighing"},
    geometry: {
        "GaussianProjection", "HNSW", "KDTree", "LSHIndex", "PStable", "RaBitQ", "RangeTree1D",
        "RangeTree2D", "SignCodes", "SimHash", "hull", "orientation", "point", "scan",
    },
    searching: {
        "BST", "BTree", "LLRB", "LSM", "RBTree", "Treap", "binary_search", "sequential_search",
        "workbench",
    },
    strings: {
        "BOOK_BASE", "BOOK_MOD", "SAMPLE", "SENTINEL", "SEPARATOR",
        "BitIndex", "ByteIndex", "Corpus", "FMIndex", "Patricia", "PlainFMIndex", "Quote",
        "Records", "Trie", "backward_search", "bwt", "rabin_karp", "lcp", "parse", "show", "suffix_array",
    },
}


@pytest.mark.parametrize("package", list(EXPORTS), ids=lambda p: p.__name__)
def test_every_exported_name_is_the_one_listed_and_imports_from_the_package(
    package: types.ModuleType,
) -> None:
    assert set(package.__all__) == EXPORTS[package]
    namespace: dict[str, object] = {}
    exec(f"from {package.__name__} import *", namespace)
    assert EXPORTS[package] <= set(namespace)
    for name in package.__all__:
        assert getattr(package, name) is namespace[name]


@pytest.mark.parametrize("package", list(EXPORTS), ids=lambda p: p.__name__)
def test_every_module_imports_as_a_module(package: types.ModuleType) -> None:
    """`import package.module as M` resolves `M` as an attribute of the package, so a function
    bound to that name on the package would be what `M` is. Every module must come back as
    itself, both through `importlib` and through the `import ... as` statement."""
    names = [info.name for info in pkgutil.iter_modules(package.__path__)]
    assert {"ball_weighing", "binary_search", "scan", "suffix_array"} & set(names)
    for name in names:
        module = importlib.import_module(f"{package.__name__}.{name}")
        namespace: dict[str, object] = {}
        exec(f"import {package.__name__}.{name} as imported", namespace)
        assert namespace["imported"] is module, name
        assert isinstance(module, types.ModuleType)
