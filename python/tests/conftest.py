# SPDX-License-Identifier: Apache-2.0
"""Test-session configuration shared by every chapter's tests."""

import os
import sys

import pytest
from hypothesis import HealthCheck, settings

# Under mutation testing (`mutmut run` sets MUTANT_UNDER_TEST) every call goes through mutmut's
# trampoline and runs several times slower, which trips Hypothesis's input-generation and
# deadline checks on tests that are fine at normal speed. Those checks guard the tests' speed,
# not their verdicts, so the mutation run switches them off and changes nothing else: the same
# examples are drawn, and an ordinary `pytest` run never loads this profile.
settings.register_profile(
    "mutation",
    deadline=None,
    suppress_health_check=[HealthCheck.too_slow, HealthCheck.data_too_large],
)

# The trampoline also adds frames to every call, so the tests that build deliberately deep
# structures (a 500-node BST path, a 5000-deep trie) overflow a limit that holds for the plain
# code. Scale every limit, including the ones those tests set themselves, by the same factor.
_TRAMPOLINE_DEPTH_FACTOR = 4

if "MUTANT_UNDER_TEST" in os.environ:
    settings.load_profile("mutation")
    _set_limit = sys.setrecursionlimit
    sys.setrecursionlimit = lambda limit: _set_limit(limit * _TRAMPOLINE_DEPTH_FACTOR)
    _set_limit(sys.getrecursionlimit() * _TRAMPOLINE_DEPTH_FACTOR)


def pytest_collection_modifyitems(config: pytest.Config, items: list[pytest.Item]) -> None:
    """Under mutation testing, skip the two tests *about* the recursion limit.

    They build 5000-deep chains and check that raising the limit is enough; mutmut's trampoline
    also goes through C calls, whose depth limit no Python setting raises, so under it they
    measure the trampoline, not the code. Every other test runs.
    """
    if "MUTANT_UNDER_TEST" not in os.environ:
        return
    skip = pytest.mark.skip(reason="measures recursion depth, which mutmut's trampoline changes")
    for item in items:
        if "survives_a_raised_recursion_limit" in item.name:
            item.add_marker(skip)
