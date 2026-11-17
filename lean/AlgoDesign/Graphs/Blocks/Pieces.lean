/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find

/-!
# Bridges, cut vertices and blocks: pieces under deletion

`pieces` counts the pieces of a graph, each at its smallest vertex, its *head* (`IsHead`). Deleting
links only splits pieces: every head stays a head, and the count grows by the number of new heads
(`pieces_eq_add`). This reads the two deletions of the specification in plain graph terms:

- `isBridge_iff`: a link is a bridge exactly when its two ends are apart once it is deleted;
- `isCutVertex_iff`: a vertex is a cut vertex exactly when it separates two other vertices.

On the way, `link_deleteLink` and `link_isolate` say which links the two deletions keep, and
`mem_of_connected_closed` is the induction along a path.
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

open Relation

variable {g : Graph}

/-! ## Links kept by the deletions -/

/-- A link of the graph without `e`: another link joins the two vertices. -/
theorem link_deleteLink {e x y : ℕ} :
    (deleteLink g e).Link x y ↔ ∃ i, i ≠ e ∧ Joins g i x y := by
  simp only [Graph.Link, deleteLink, List.mem_eraseIdx_iff_getElem?, Joins]
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact ⟨i, hi, Or.inl h⟩
    · exact ⟨i, hi, Or.inr h⟩
  · rintro ⟨i, hi, h | h⟩
    · exact Or.inl ⟨i, hi, h⟩
    · exact Or.inr ⟨i, hi, h⟩

theorem link_isolate {w x y : ℕ} :
    (isolate g w).Link x y ↔ g.Link x y ∧ x ≠ w ∧ y ≠ w := by
  simp only [Graph.Link, isolate, List.mem_filter, decide_eq_true_eq]
  tauto

/-! ## Paths -/

/-- A set closed under links holds everything connected to its members. -/
theorem mem_of_connected_closed {h : Graph} {S : ℕ → Prop}
    (hS : ∀ x y, h.Link x y → S x → S y) {u v : ℕ} (huv : h.Connected u v) (hu : S u) :
    S v := by
  induction huv with
  | refl => exact hu
  | tail _ hl ih => exact hS _ _ hl ih

/-- Being in one piece goes both ways. -/
theorem connected_symm {h : Graph} {u v : ℕ} (huv : h.Connected u v) : h.Connected v u := by
  induction huv with
  | refl => exact ReflTransGen.refl
  | tail _ hl ih => exact ReflTransGen.head (Or.symm hl) ih

/-- Links kept keep pieces together. -/
theorem connected_mono {h h' : Graph} (hl : ∀ x y, h.Link x y → h'.Link x y) {u v : ℕ}
    (huv : h.Connected u v) : h'.Connected u v :=
  mem_of_connected_closed (S := h'.Connected u) (fun _ _ hxy hx => hx.tail (hl _ _ hxy)) huv
    ReflTransGen.refl

theorem connected_trans {h : Graph} {u v w : ℕ} (huv : h.Connected u v) (hvw : h.Connected v w) :
    h.Connected u w :=
  ReflTransGen.trans huv hvw

theorem connected_of_link {h : Graph} {u v : ℕ} (hl : h.Link u v) : h.Connected u v :=
  ReflTransGen.single hl

/-! ## Heads: each piece at its smallest vertex -/

/-- `v` is the smallest vertex of its piece. -/
def IsHead (h : Graph) (v : ℕ) : Prop := ∀ u < v, ¬ h.Connected u v

instance (h : Graph) : DecidablePred (IsHead h) := fun v => by unfold IsHead; infer_instance

/-- The heads among the vertices. -/
def heads (h : Graph) : Finset ℕ := (Finset.range h.n).filter (IsHead h)

theorem pieces_eq_card (h : Graph) : pieces h = (heads h).card := by
  simp [pieces, heads, IsHead, Finset.card, Finset.filter_val, Multiset.range]

/-- Two heads in one piece are the same vertex. -/
theorem isHead_eq {h : Graph} {a b : ℕ} (ha : IsHead h a) (hb : IsHead h b)
    (hab : h.Connected a b) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hab (hb a hlt)
  · exact heq
  · exact absurd (connected_symm hab) (ha b hgt)

/-- Every vertex has the head of its piece at or below it. -/
theorem exists_head (h : Graph) (x : ℕ) : ∃ m ≤ x, IsHead h m ∧ h.Connected m x := by
  have hex : ∃ m, h.Connected m x := ⟨x, ReflTransGen.refl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex ReflTransGen.refl, fun u hu hum => ?_,
    Nat.find_spec hex⟩
  exact Nat.find_min hex hu (connected_trans hum (Nat.find_spec hex))

/-- Deleting links keeps every head: the pieces only split. -/
theorem heads_subset {g h : Graph} (hn : h.n = g.n)
    (hc : ∀ u v, h.Connected u v → g.Connected u v) : heads g ⊆ heads h := by
  intro v hv
  simp only [heads, Finset.mem_filter, Finset.mem_range] at hv ⊢
  exact ⟨hn ▸ hv.1, fun u hu huv => hv.2 u hu (hc u v huv)⟩

/-- Deleting links adds one piece per new head. -/
theorem pieces_eq_add {g h : Graph} (hn : h.n = g.n)
    (hc : ∀ u v, h.Connected u v → g.Connected u v) :
    pieces h = pieces g + (heads h \ heads g).card := by
  rw [pieces_eq_card, pieces_eq_card, ← Finset.card_sdiff_add_card_eq_card (heads_subset hn hc)]
  omega

/-- A new head: a head after the deletion that was not one before. -/
theorem mem_new_heads {g h : Graph} (hn : h.n = g.n) {v : ℕ} :
    v ∈ heads h \ heads g ↔ v < g.n ∧ IsHead h v ∧ ¬ IsHead g v := by
  simp only [heads, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, hn]
  tauto

/-- A piece that splits gives a new head: `p` and `q` are in the piece of the head `m`, and `p`
keeps `m` but loses `q`, so the head of `q`'s new piece is not a head before. -/
theorem exists_new_head {g h : Graph} (hn : h.n = g.n)
    (hc : ∀ u v, h.Connected u v → g.Connected u v) {m p q : ℕ} (hm : IsHead g m)
    (hpm : h.Connected p m) (hmq : g.Connected m q) (hpq : ¬ h.Connected p q) (hq : q < g.n) :
    (heads h \ heads g).Nonempty := by
  obtain ⟨m', hm'q, hm', hm'c⟩ := exists_head h q
  refine ⟨m', (mem_new_heads hn).mpr ⟨by omega, hm', fun hg' => hpq ?_⟩⟩
  obtain rfl : m = m' := isHead_eq hm hg' (connected_trans hmq (connected_symm (hc _ _ hm'c)))
  exact connected_trans hpm hm'c

/-! ## Bridges -/

theorem link_of_deleteLink {e x y : ℕ} (hl : (deleteLink g e).Link x y) : g.Link x y := by
  obtain ⟨i, -, hi | hi⟩ := link_deleteLink.mp hl
  · exact Or.inl (List.mem_iff_getElem?.mpr ⟨i, hi⟩)
  · exact Or.inr (List.mem_iff_getElem?.mpr ⟨i, hi⟩)

theorem connected_of_deleteLink {e x y : ℕ} (h : (deleteLink g e).Connected x y) :
    g.Connected x y :=
  connected_mono (fun _ _ => link_of_deleteLink) h

/-- A link of the graph is kept when `e` is deleted, or it joins the two ends of `e`. -/
theorem link_deleteLink_or {e a b x y : ℕ} (he : g.links[e]? = some (a, b)) (hl : g.Link x y) :
    (deleteLink g e).Link x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have key : ∀ p q, (p, q) ∈ g.links → (deleteLink g e).Link p q ∨ (p = a ∧ q = b) := by
    intro p q hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
    by_cases hje : j = e
    · subst hje
      rw [he] at hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      exact Or.inr ⟨hj.1.symm, hj.2.symm⟩
    · exact Or.inl (link_deleteLink.mpr ⟨j, hje, Or.inl hj⟩)
  rcases hl with h | h
  · exact (key x y h).imp id Or.inl
  · rcases key y x h with h | h
    · exact Or.inl (Or.symm h)
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)

/-- **A bridge is a link whose ends are left apart when it is deleted.** -/
theorem isBridge_iff (hg : g.WellFormed) {e a b : ℕ} (he : g.links[e]? = some (a, b)) :
    IsBridge g e ↔ ¬ (deleteLink g e).Connected a b := by
  obtain ⟨helt, -⟩ := List.getElem?_eq_some_iff.mp he
  have hab : a < g.n ∧ b < g.n := hg _ (List.mem_iff_getElem?.mpr ⟨e, he⟩)
  have hsub : ∀ u v, (deleteLink g e).Connected u v → g.Connected u v :=
    fun _ _ => connected_of_deleteLink
  constructor
  · rintro ⟨-, hlt⟩ hdab
    have hc : ∀ u v, (deleteLink g e).Connected u v ↔ g.Connected u v := by
      refine fun u v => ⟨hsub u v, fun huv =>
        mem_of_connected_closed (S := (deleteLink g e).Connected u) ?_ huv ReflTransGen.refl⟩
      intro x y hl hx
      rcases link_deleteLink_or he hl with hl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hx.tail hl
      · exact connected_trans hx hdab
      · exact connected_trans hx (connected_symm hdab)
    have := pieces_congr (g := deleteLink g e) (h := g) rfl hc
    omega
  · intro hdab
    refine ⟨helt, ?_⟩
    rw [pieces_eq_add (g := g) (h := deleteLink g e) rfl hsub]
    suffices (heads (deleteLink g e) \ heads g).Nonempty by
      have := this.card_pos
      omega
    obtain ⟨m, -, hm, hma⟩ := exists_head g a
    have hgab : g.Connected a b :=
      connected_of_link (Or.inl (List.mem_iff_getElem?.mpr ⟨e, he⟩))
    have hm2 : (deleteLink g e).Connected a m ∨ (deleteLink g e).Connected b m := by
      refine mem_of_connected_closed
        (S := fun z => (deleteLink g e).Connected a z ∨ (deleteLink g e).Connected b z) ?_
        (connected_symm hma) (Or.inl ReflTransGen.refl)
      intro x y hl hx
      rcases link_deleteLink_or he hl with hl | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hx.imp (fun h => h.tail hl) (fun h => h.tail hl)
      · exact Or.inr ReflTransGen.refl
      · exact Or.inl ReflTransGen.refl
    rcases hm2 with h | h
    · exact exists_new_head rfl hsub hm h (connected_trans hma hgab) hdab hab.2
    · exact exists_new_head rfl hsub hm h hma (fun h => hdab (connected_symm h)) hab.1

/-! ## Cut vertices -/

theorem connected_of_isolate {w x y : ℕ} (h : (isolate g w).Connected x y) : g.Connected x y :=
  connected_mono (fun _ _ hl => (link_isolate.mp hl).1) h

/-- An isolated vertex is connected to itself alone. -/
theorem eq_of_isolate_connected {w x : ℕ} (h : (isolate g w).Connected w x) : x = w :=
  mem_of_connected_closed (S := (· = w)) (fun _ _ hl hx => absurd hx (link_isolate.mp hl).2.1)
    h rfl

/-- An isolated vertex is the head of its own piece. -/
theorem isHead_isolate (w : ℕ) : IsHead (isolate g w) w := fun u hu huw => by
  have := eq_of_isolate_connected (connected_symm huw)
  omega

/-- A vertex that separates two others is neither of them. -/
theorem ne_of_separates {w x y : ℕ} (h : Separates g w x y) : w ≠ x ∧ w ≠ y :=
  ⟨h.1, h.2.1⟩

/-- A vertex that separates two others is in their piece. -/
theorem connected_of_separates {w x y : ℕ} (h : Separates g w x y) : g.Connected x w := by
  by_contra hxw
  apply h.2.2.2
  refine (mem_of_connected_closed (h := g)
    (S := fun z => (isolate g w).Connected x z ∧ g.Connected x z) ?_ h.2.2.1
    ⟨ReflTransGen.refl, ReflTransGen.refl⟩).1
  intro p q hl ⟨hp1, hp2⟩
  have hq2 : g.Connected x q := hp2.tail hl
  have hne : ∀ z, g.Connected x z → z ≠ w := fun z hz hzw => hxw (hzw ▸ hz)
  exact ⟨hp1.tail (link_isolate.mpr ⟨hl, hne p hp2, hne q hq2⟩), hq2⟩

/-- **A cut vertex is a vertex whose deletion separates two other vertices.** -/
theorem isCutVertex_iff (_hg : g.WellFormed) {w : ℕ} (hw : w < g.n) :
    IsCutVertex g w ↔ ∃ x < g.n, ∃ y < g.n, Separates g w x y := by
  have hsub : ∀ u v, (isolate g w).Connected u v → g.Connected u v :=
    fun _ _ => connected_of_isolate
  have hcount := pieces_eq_add (g := g) (h := isolate g w) rfl hsub
  have hcut : IsCutVertex g w ↔ 1 < (heads (isolate g w) \ heads g).card := by
    unfold IsCutVertex
    constructor
    · rintro ⟨-, h⟩
      omega
    · intro h
      exact ⟨hw, by omega⟩
  rw [hcut, Finset.one_lt_card]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hne⟩
    rw [mem_new_heads (g := g) (h := isolate g w) rfl] at hv₁ hv₂
    have key : ∀ v, v < g.n ∧ IsHead (isolate g w) v ∧ ¬ IsHead g v → v ≠ w →
        (∃ x < g.n, ∃ y < g.n, Separates g w x y) ∨ (IsHead g w ∧ g.Connected w v) := by
      rintro v ⟨hvn, hvi, hvg⟩ hvw
      obtain ⟨m, hmv, hm, hmc⟩ := exists_head g v
      by_cases hmw : m = w
      · exact Or.inr ⟨hmw ▸ hm, hmw ▸ hmc⟩
      have hmlt : m < v := lt_of_le_of_ne hmv (fun h => hvg (h ▸ hm))
      exact Or.inl ⟨m, by omega, v, hvn, Ne.symm hmw, Ne.symm hvw, hmc, hvi m hmlt⟩
    have pair : ∀ v v', v ≠ v' → (v < g.n ∧ IsHead (isolate g w) v ∧ ¬ IsHead g v) →
        (v' < g.n ∧ IsHead (isolate g w) v' ∧ ¬ IsHead g v') → v ≠ w →
        ∃ x < g.n, ∃ y < g.n, Separates g w x y := by
      intro v v' hne hv hv' hvw
      rcases key v hv hvw with h | ⟨hw', hwv⟩
      · exact h
      have hv'w : v' ≠ w := fun h => hv'.2.2 (h ▸ hw')
      rcases key v' hv' hv'w with h | ⟨-, hwv'⟩
      · exact h
      exact ⟨v, hv.1, v', hv'.1, Ne.symm hvw, Ne.symm hv'w,
        connected_trans (connected_symm hwv) hwv', fun h => hne (isHead_eq hv.2.1 hv'.2.1 h)⟩
    by_cases h₁ : v₁ = w
    · exact pair v₂ v₁ (Ne.symm hne) hv₂ hv₁ (fun h => hne (h₁.trans h.symm))
    · exact pair v₁ v₂ hne hv₁ hv₂ h₁
  · rintro ⟨x, hx, y, hy, hs⟩
    obtain ⟨hwx, hwy, hxy, hixy⟩ := hs
    have hxw : g.Connected x w := connected_of_separates ⟨hwx, hwy, hxy, hixy⟩
    obtain ⟨m, -, hm, hmx⟩ := exists_head g x
    obtain ⟨a, hax, ha, hac⟩ := exists_head (isolate g w) x
    obtain ⟨b, hby, hb, hbc⟩ := exists_head (isolate g w) y
    have hab : a ≠ b := fun h => hixy (connected_trans (connected_symm hac) (h ▸ hbc))
    have haw : a ≠ w := fun h => hwx (eq_of_isolate_connected (h ▸ hac)).symm
    have hbw : b ≠ w := fun h => hwy (eq_of_isolate_connected (h ▸ hbc)).symm
    have hma : g.Connected m a := connected_trans hmx (connected_symm (hsub _ _ hac))
    have hmb : g.Connected m b :=
      connected_trans (connected_trans hmx hxy) (connected_symm (hsub _ _ hbc))
    have hnew : ∀ c, c < g.n → IsHead (isolate g w) c → g.Connected m c → c ≠ m →
        c ∈ heads (isolate g w) \ heads g := fun c hcn hci hmc hcm =>
      (mem_new_heads (g := g) (h := isolate g w) rfl).mpr
        ⟨hcn, hci, fun hc => hcm (isHead_eq hm hc hmc).symm⟩
    by_cases hmw : m = w
    · subst hmw
      exact ⟨a, hnew a (by omega) ha hma haw, b, hnew b (by omega) hb hmb hbw, hab⟩
    have hwnew : w ∈ heads (isolate g w) \ heads g :=
      (mem_new_heads (g := g) (h := isolate g w) rfl).mpr
      ⟨hw, isHead_isolate w, fun hw' => hmw (isHead_eq hm hw' (connected_trans hmx hxw))⟩
    by_cases hia : (isolate g w).Connected a m
    · have hbm : b ≠ m := fun h => hab (isHead_eq ha hb (h ▸ hia))
      exact ⟨b, hnew b (by omega) hb hmb hbm, w, hwnew, hbw⟩
    · have ham : a ≠ m := fun h => hia (h ▸ ReflTransGen.refl)
      exact ⟨a, hnew a (by omega) ha hma ham, w, hwnew, haw⟩

end AlgoDesign.Graphs.Blocks
