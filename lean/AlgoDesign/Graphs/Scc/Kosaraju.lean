/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Scc.Basic

/-!
# Strong components: Kosaraju–Sharir

Source: Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms* (4th ed.), §20.5,
STRONGLY-CONNECTED-COMPONENTS, p. 577: a depth-first walk on the graph records the order vertices
finish (`finishOrder`, `Scc/Basic.lean`); a second walk on the reversed rows takes roots in
decreasing finishing order, and each root's walk is one group. Groups are found in topological
order of the graph of groups and numbered in the order found; a group's members are listed in the
order the second walk enters them.

Kept as the second method, the oracle the tests compare Algorithm T against. That its groups are
the strong components, numbered in topological order, is argued, not proved: CLRS Lemma 20.14 and
Theorem 20.15 (pp. 579–580). It is checked by `decide` on the examples, and on any one graph the
checker (`check_eq_none_iff`) turns a passing check into a proof.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Scc

/-- The second pass: roots in decreasing finishing order, each new root's walk on the reversed
rows giving one group, its members in the order entered. -/
def secondPass (g : Digraph) : Dfs × List (List ℕ) :=
  (finishOrder g).reverse.foldl
    (fun st r =>
      if st.1.seen r then st
      else
        let d := Dfs.visit g.into (fuel g) { st.1 with entered := [] } r
        (d, st.2 ++ [d.entered]))
    (Dfs.init, [])

/-- **Kosaraju–Sharir** in CLRS's pass order: groups numbered in the order found. -/
def kosarajuSharir (g : Digraph) : Components :=
  let groups := (secondPass g).2
  ⟨(List.range g.n).map fun v => groups.findIdx fun m => v ∈ m, groups⟩

/-- **Kosaraju–Sharir's promise** [argued]: on a well-formed graph, its groups are the strong
components, numbered in topological order, and its member lists agree with them (CLRS Lemma 20.14
and Theorem 20.15). -/
def KosarajuPromise : Prop :=
  ∀ g : Digraph, g.WellFormed →
    IsSccPartition g (kosarajuSharir g).groupOf ∧ IdsTopological g (kosarajuSharir g).groupOf ∧
      MembersAgree g (kosarajuSharir g)

example : kosarajuSharir ⟨3, [(0, 1), (1, 0), (1, 2)]⟩ = ⟨[0, 0, 1], [[0, 1], [2]]⟩ := by decide

example : kosarajuSharir ⟨7, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 3), (4, 3), (1, 5),
    (5, 5), (5, 3), (5, 6), (6, 1)]⟩ =
    ⟨[0, 0, 0, 1, 1, 0, 0], [[0, 2, 1, 6, 5], [3, 4]]⟩ := by decide

end AlgoDesign.Graphs.Scc
