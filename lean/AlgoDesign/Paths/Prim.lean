/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Kruskal

/-!
# Prim's links: what Prim owes

Source: the Paths chapter, "After the big snow": Prim's method has no proof of its own; it is
checked against Kruskal's links on many graphs.

[tested] → `Prim.ReturnsKruskalLinks`: on a well-formed network, Prim's method returns Kruskal's
links, each once, in some order. Tested, not proved: Prim has no Lean walk, and a separate
Lean–Rust check holds the Rust's `prim` to this statement on every network of its corpus, comparing
Prim's links sorted with the Lean's `kruskal` sorted, so a link Prim adds twice fails it too.
-/

@[expose] public section

namespace AlgoDesign.Paths.Prim

/-- **Prim returns Kruskal's links, as a set**: on a well-formed network, the links `prim` returns
are the links the library's `kruskal` keeps, each once, in some order. Tested, not proved. -/
def ReturnsKruskalLinks (prim : LinkNetwork → List ℕ) : Prop :=
  ∀ N : LinkNetwork, N.WellFormed → (prim N).Perm (Kruskal.kruskal N)

end AlgoDesign.Paths.Prim
