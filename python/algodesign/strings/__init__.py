# SPDX-License-Identifier: Apache-2.0
"""The Strings chapter: string matching and text indexing.

The modules follow the chapter's order, each building on the ones before it:

- `rabin_karp` -- fingerprint search;
- `trie`, `patricia` -- dictionaries over byte keys;
- `suffix_array`, `lcp` -- the sorted suffixes of a text, every occurrence of a pattern found by
  binary search over them, their common prefixes, and the longest repeated substring they find;
- `bwt` -- the Burrows-Wheeler transform and its inverse;
- `count_index`, `fm_index` -- rank, select and occ, and the FM-index built on them, its
  last column compressed by `chunked_wavelet` (fixed-length chunks, a `wavelet_tree` each) and its
  sample marker by `rrr`; `fm_index_plain` is the same index uncompressed, which the tests hold
  it to;
  `backward_search` checks backward search's state against the text;
- `records` -- from a search hit back to the whole record that contains it.

Texts, patterns and keys are `bytes`; positions are plain `int`s. Invalid input raises `ValueError`.
`parse` and `show` translate between the chapter's written form, where the sentinel is `$` and the
separator `|`, and those bytes: `bwt.encode(parse("banana$"))` runs the chapter's example.

Classes and constants are exported by name; functions are reached through their modules
(`rabin_karp.search`, `suffix_array.search`, `lcp.longest_repeat`, `bwt.encode`, ...). The module
`naive` holds the plain scan and the slow reference versions the tests compare against; import it
as `algodesign.strings.naive`.
"""

from __future__ import annotations

from . import backward_search, bwt, lcp, rabin_karp, suffix_array
from ._constants import SENTINEL, SEPARATOR, parse, show
from .count_index import BitIndex, ByteIndex
from .fm_index import SAMPLE, FMIndex
from .fm_index_plain import PlainFMIndex
from .patricia import Patricia
from .rabin_karp import BOOK_BASE, BOOK_MOD
from .records import Corpus, Quote, Records
from .trie import Trie

__all__ = [
    "BOOK_BASE",
    "BOOK_MOD",
    "SAMPLE",
    "SENTINEL",
    "SEPARATOR",
    "BitIndex",
    "ByteIndex",
    "Corpus",
    "FMIndex",
    "Patricia",
    "PlainFMIndex",
    "Quote",
    "Records",
    "Trie",
    "backward_search",
    "bwt",
    "lcp",
    "parse",
    "rabin_karp",
    "show",
    "suffix_array",
]
