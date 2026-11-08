/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Decide

/-! # Bridges, cut vertices and blocks: pieces, the reported blocks, doubled links

Two graphs with the same pieces have as many; what it means for the reported blocks to be the
network's; and why a doubled link, or a loop, is never a bridge. -/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

open Relation

/-- Two graphs on the same vertices with the same pieces have as many of them. -/
theorem pieces_congr {g h : Graph} (hn : g.n = h.n)
    (hc : ∀ u v, g.Connected u v ↔ h.Connected u v) : pieces g = pieces h := by
  unfold pieces
  rw [hn]
  congr 1
  refine List.filter_congr fun v _ => ?_
  simp only [hc]

/-- **The reported blocks are the network's**: a link has a block exactly when it is not a loop,
two such links share one exactly when they are in one block, each block lists exactly its links,
and every isolated vertex is a block alone. -/
def BlocksAgree (g : Graph) (r : Report) : Prop :=
  (∀ e < g.links.length, (r.blockOfLink.getD e none = none ↔ ¬ NonLoop g e)) ∧
  (∀ e < g.links.length, ∀ f < g.links.length, NonLoop g e → NonLoop g f →
    (r.blockOfLink.getD e none = r.blockOfLink.getD f none ↔ SameBlock g e f)) ∧
  (∀ e < g.links.length, (r.blockOfLink.getD e none).all (· < r.blocks.length)) ∧
  (∀ e < g.links.length, ∀ k < r.blocks.length,
    (r.blockOfLink.getD e none = some k ↔ e ∈ r.blocks.getD k [])) ∧
  ∀ v < g.n, IsolatedVertex g v →
    ∃ k < r.blocks.length, r.blocks.getD k [] = [] ∧ r.blockVertices.getD k [] = [v]

/-! ## A doubled link is never a bridge -/

/-- Graphs whose links join the same pairs have the same pieces. -/
theorem connected_congr {g h : Graph} (hl : ∀ u v, g.Link u v ↔ h.Link u v) (u v : ℕ) :
    g.Connected u v ↔ h.Connected u v := by
  have : g.Link = h.Link := by funext u v; exact propext (hl u v)
  simp only [Graph.Connected, this]

/-- A link deleted from a graph, with another link left joining its two ends, joins the same
pairs. -/
theorem link_deleteLink_iff {g : Graph} {e : ℕ}
    (hkeep : ∀ p, g.links[e]? = some p → (p ∈ g.links.eraseIdx e ∨ p.swap ∈ g.links.eraseIdx e))
    (u v : ℕ) : (deleteLink g e).Link u v ↔ g.Link u v := by
  simp only [Graph.Link, deleteLink]
  constructor
  · rintro (h | h)
    · exact Or.inl (List.mem_of_mem_eraseIdx h)
    · exact Or.inr (List.mem_of_mem_eraseIdx h)
  · have key : ∀ x y, (x, y) ∈ g.links →
        (x, y) ∈ g.links.eraseIdx e ∨ (y, x) ∈ g.links.eraseIdx e := by
      intro x y hxy
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hxy
      by_cases hje : j = e
      · subst hje
        exact hkeep _ hj
      · exact Or.inl (List.mem_eraseIdx_iff_getElem?.mpr ⟨j, hje, hj⟩)
    rintro (h | h)
    · exact key u v h
    · exact (key v u h).symm

/-- **A link with a doubled twin is never a bridge**: another link joins the same two vertices, so
deleting the first joins the same pairs and leaves the same pieces. -/
theorem not_isBridge_of_twin {g : Graph} {e f a b : ℕ} (he : g.links[e]? = some (a, b))
    (hf : Joins g f a b) (hef : f ≠ e) : ¬ IsBridge g e := by
  rintro ⟨-, hlt⟩
  have hkeep : ∀ p, g.links[e]? = some p →
      (p ∈ g.links.eraseIdx e ∨ p.swap ∈ g.links.eraseIdx e) := by
    intro p hp
    rw [he] at hp
    cases hp
    rcases hf with hf | hf
    · exact Or.inl (List.mem_eraseIdx_iff_getElem?.mpr ⟨f, hef, hf⟩)
    · exact Or.inr (List.mem_eraseIdx_iff_getElem?.mpr ⟨f, hef, hf⟩)
  have := pieces_congr (g := deleteLink g e) (h := g) rfl
    (connected_congr (link_deleteLink_iff hkeep))
  omega

/-- **A loop is never a bridge**: deleting it joins the same pairs of different vertices, and a
vertex is always in its own piece. -/
theorem not_isBridge_of_loop {g : Graph} {e a : ℕ} (he : g.links[e]? = some (a, a)) :
    ¬ IsBridge g e := by
  rintro ⟨-, hlt⟩
  have hc : ∀ u v, (deleteLink g e).Connected u v ↔ g.Connected u v := by
    intro u v
    constructor
    · intro h
      induction h with
      | refl => exact ReflTransGen.refl
      | tail _ hbc ih =>
        refine ih.tail ?_
        simp only [Graph.Link, deleteLink] at hbc ⊢
        exact hbc.imp List.mem_of_mem_eraseIdx List.mem_of_mem_eraseIdx
    · intro h
      induction h with
      | refl => exact ReflTransGen.refl
      | tail _ hbc ih =>
        rename_i b c _
        by_cases hb : b = c
        · exact hb ▸ ih
        · refine ih.tail ?_
          have key : ∀ x y, x ≠ y → (x, y) ∈ g.links → (x, y) ∈ g.links.eraseIdx e := by
            intro x y hxy hm
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
            refine List.mem_eraseIdx_iff_getElem?.mpr ⟨j, fun hje => ?_, hj⟩
            subst hje
            rw [he] at hj
            cases hj
            exact hxy rfl
          rcases hbc with h | h
          · exact Or.inl (key b c hb h)
          · exact Or.inr (key c b (Ne.symm hb) h)
  have := pieces_congr (g := deleteLink g e) (h := g) rfl hc
  omega

end AlgoDesign.Graphs.Blocks
