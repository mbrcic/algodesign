/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Searching.RedBlackStandard.Spec
public import AlgoDesign.Searching.RedBlackStandard.Basic
public import AlgoDesign.Searching.RedBlackStandard.Search
public import AlgoDesign.Searching.RedBlackStandard.Balance
public import AlgoDesign.Searching.RedBlackStandard.Insert
public import AlgoDesign.Searching.RedBlackStandard.Delete
public import AlgoDesign.Searching.RedBlackStandard.Cost
public import AlgoDesign.Searching.RedBlackStandard.Rotations

/-! The standard (CLRS) red-black tree. Its specification (the invariant and what each update
owes) is in `RedBlackStandard/Spec.lean`; this file imports the whole structure. -/
