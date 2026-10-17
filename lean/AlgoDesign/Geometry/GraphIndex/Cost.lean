/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Geometry.GraphIndex.Spec

/-!
# The graph index: memory per place

The box's "memory, a fixed number of links per place" follows from box invariant 1: a node on
`L` layers stores at most `m0` links on layer 0 and `m` on each of the `L - 1` above
(`linksPerPlaceAtMost_of_valid`). The per-query cost is measured (the HNSW table in
the chapter), not proved. Rust:
the lists `Hnsw::neighbors` reads.
-/

@[expose] public section

namespace AlgoDesign.Geometry

namespace HNSW

variable {d : ℕ} {α : Type}

/-- A sum over layers `0, …, L - 1` with layer 0 at most `m0` and every other at most `m`. -/
theorem sum_range_le_cap (f : ℕ → ℕ) (m m0 : ℕ) (h0 : f 0 ≤ m0) (h : ∀ l, 0 < l → f l ≤ m) :
    ∀ L, 0 < L → ((List.range L).map f).sum ≤ m0 + m * (L - 1)
  | 0, hL => absurd hL (lt_irrefl 0)
  | 1, _ => by simpa using h0
  | L + 2, _ => by
    have ih := sum_range_le_cap f m m0 h0 h (L + 1) (Nat.succ_pos L)
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have := h (L + 1) (Nat.succ_pos L)
    have hm : m * (L + 2 - 1) = m * L + m := by
      rw [show L + 2 - 1 = L + 1 by omega, Nat.mul_succ]
    rw [hm]; simp only [Nat.add_sub_cancel] at ih; omega

/-- **A valid graph stores a fixed number of links per place.** -/
theorem linksPerPlaceAtMost_of_valid {g : HNSW d α} (hg : Valid g) : LinksPerPlaceAtMost g := by
  intro v hv
  have hpos := hg.2.1.1 v hv
  refine sum_range_le_cap (fun l => (g.neighbors v l).length) g.m g.m0 ?_ (fun l hl => ?_) _ hpos
  · simpa [cap] using hg.1 v hv 0 hpos
  · by_cases hlt : l < g.layers v
    · have := hg.1 v hv l hlt
      simpa [cap, Nat.pos_iff_ne_zero.mp hl] using this
    · simp only [neighbors, layers] at hlt ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp

end HNSW

end AlgoDesign.Geometry
