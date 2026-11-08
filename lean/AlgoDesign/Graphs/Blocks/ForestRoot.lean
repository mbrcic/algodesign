/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Forest

/-!
# The block-cut forest: rooting and meeting

Given a parent map `D` on the nodes `0 .. size r - 1` (a root is its own parent) and a rank `ρ`
that strictly drops from a non-root to its parent, `TreeSpec` says that `around` joins each node
exactly to its parent and its children, and that the first vertex of each tree sits on the tree's
root. Under it, `root` gives every node of a vertex's tree the parent `D` and the depth `ddepth`
(`parent_eq`), and `separators` answers `none` exactly for ends in different trees, and otherwise
lists the cut vertices whose node has a child above exactly one end (`separators_spec`).
-/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

namespace Forest

/-- `a` is `x` or above it: following `D` from `x` reaches `a`. -/
def DAnc (D : ℕ → ℕ) (a x : ℕ) : Prop := Relation.ReflTransGen (fun y z => D z = y ∧ z ≠ y) a x

/-- The root above `x`. -/
def top (D ρ : ℕ → ℕ) (x : ℕ) : ℕ := D^[ρ x] x

/-- Steps from `x` up to its root, with `k` steps of fuel. -/
def ddepthAux (D : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => if D x = x then 0 else ddepthAux D k (D x) + 1

/-- Steps from `x` up to its root. -/
def ddepth (D ρ : ℕ → ℕ) (x : ℕ) : ℕ := ddepthAux D (ρ x) x

/-- **A rooted forest on the report's nodes**: `D` is a parent map ranked by `ρ`, `around` joins
each node to its parent and its children, and the first vertex of each tree sits on its root. -/
structure TreeSpec (r : Report) (n : ℕ) (D ρ : ℕ → ℕ) : Prop where
  /-- A node's parent is a node. -/
  lt : ∀ x < size r, D x < size r
  /-- The rank drops from a non-root to its parent. -/
  rank : ∀ x < size r, D x ≠ x → ρ (D x) < ρ x
  /-- The nodes around `x` are its parent, unless `x` is a root, and its children. -/
  around : ∀ x < size r, ∀ y, y ∈ around r x ↔
    y < size r ∧ ((D x ≠ x ∧ y = D x) ∨ (D y = x ∧ y ≠ x))
  /-- Each vertex's node is a node. -/
  node_lt : ∀ p < n, nodeOfVertex r p < size r
  /-- The first vertex of a tree sits on its root. -/
  first : ∀ p < n, (∀ q < p, top D ρ (nodeOfVertex r q) ≠ top D ρ (nodeOfVertex r p)) →
    D (nodeOfVertex r p) = nodeOfVertex r p

variable {r : Report} {n : ℕ} {D ρ : ℕ → ℕ}

namespace TreeSpec

variable (h : TreeSpec r n D ρ)
include h

theorem iterate_lt {x : ℕ} (hx : x < size r) (k : ℕ) : D^[k] x < size r := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact h.lt _ ih

theorem iterate_root : ∀ (k : ℕ) {x : ℕ}, x < size r → ρ x ≤ k → D (D^[k] x) = D^[k] x := by
  intro k
  induction k with
  | zero =>
    intro x hx hk
    by_contra hne
    have := h.rank x hx hne
    simp at hne; omega
  | succ k ih =>
    intro x hx hk
    rw [Function.iterate_succ_apply]
    by_cases hr : D x = x
    · rw [hr, Function.iterate_fixed hr]; exact hr
    · exact ih (h.lt x hx) (by have := h.rank x hx hr; omega)

theorem iterate_eq_top {x : ℕ} (hx : x < size r) {k : ℕ} (hk : ρ x ≤ k) :
    D^[k] x = top D ρ x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply, top,
    Function.iterate_fixed (h.iterate_root _ hx le_rfl)]

theorem top_lt {x : ℕ} (hx : x < size r) : top D ρ x < size r := h.iterate_lt hx _

theorem top_root {x : ℕ} (hx : x < size r) : D (top D ρ x) = top D ρ x :=
  h.iterate_root _ hx le_rfl

theorem top_parent {x : ℕ} (hx : x < size r) : top D ρ (D x) = top D ρ x := by
  by_cases hr : D x = x
  · rw [hr]
  · have h1 := h.iterate_eq_top (h.lt x hx) (le_of_lt (h.rank x hx hr))
    have h2 := h.iterate_eq_top hx (Nat.le_succ (ρ x))
    rw [Function.iterate_succ_apply] at h2
    rw [← h1, h2]

theorem ddepthAux_eq : ∀ (k m : ℕ) {x : ℕ}, x < size r → ρ x ≤ k → ρ x ≤ m →
    ddepthAux D k x = ddepthAux D m x := by
  intro k
  induction k with
  | zero =>
    intro m x hx hk hm
    have hr : D x = x := by
      by_contra hne; have := h.rank x hx hne; omega
    cases m <;> simp [ddepthAux, hr]
  | succ k ih =>
    intro m x hx hk hm
    by_cases hr : D x = x
    · cases m <;> simp [ddepthAux, hr]
    · have := h.rank x hx hr
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [ddepthAux, hr, ↓reduceIte]
      rw [ih m (h.lt x hx) (by omega) (by omega)]

omit h in
theorem ddepth_root {x : ℕ} (hr : D x = x) : ddepth D ρ x = 0 := by
  unfold ddepth; cases ρ x <;> simp [ddepthAux, hr]

theorem ddepth_parent {x : ℕ} (hx : x < size r) (hr : D x ≠ x) :
    ddepth D ρ x = ddepth D ρ (D x) + 1 := by
  have := h.rank x hx hr
  unfold ddepth
  obtain ⟨k, hk⟩ : ∃ k, ρ x = k + 1 := ⟨ρ x - 1, by omega⟩
  rw [hk]
  simp only [ddepthAux, hr, ↓reduceIte]
  rw [h.ddepthAux_eq k _ (h.lt x hx) (by omega) le_rfl]

theorem root_of_ddepth {x : ℕ} (hx : x < size r) (h0 : ddepth D ρ x = 0) : D x = x := by
  by_contra hr; rw [h.ddepth_parent hx hr] at h0; omega

theorem ddepth_le_card : ∀ (m : ℕ) {x : ℕ}, ρ x < m → x < size r →
    ddepth D ρ x ≤ ((Finset.range (size r)).filter fun y => ρ y < ρ x).card := by
  intro m
  induction m with
  | zero => intro x hm; omega
  | succ m ih =>
    intro x hm hx
    by_cases hr : D x = x
    · rw [ddepth_root hr]; exact Nat.zero_le _
    · have hd := h.rank x hx hr
      rw [h.ddepth_parent hx hr]
      have := ih (by omega) (h.lt x hx)
      have hsub : insert (D x) ((Finset.range (size r)).filter fun y => ρ y < ρ (D x)) ⊆
          (Finset.range (size r)).filter fun y => ρ y < ρ x := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hy ⊢
        rcases hy with rfl | ⟨h1, h2⟩
        · exact ⟨h.lt x hx, hd⟩
        · exact ⟨h1, by omega⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp)] at hc
      omega

theorem ddepth_lt {x : ℕ} (hx : x < size r) : ddepth D ρ x < size r := by
  have h1 := h.ddepth_le_card (ρ x + 1) (Nat.lt_succ_self _) hx
  have h2 : ((Finset.range (size r)).filter fun y => ρ y < ρ x) ⊆
      (Finset.range (size r)).erase x := fun y hy => by
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hy ⊢
      exact ⟨by rintro rfl; omega, hy.1⟩
  have h3 := Finset.card_le_card h2
  rw [Finset.card_erase_of_mem (by simpa using hx), Finset.card_range] at h3
  omega

end TreeSpec

theorem dAnc_iff {x : ℕ} (hr : D x ≠ x) (c : ℕ) : DAnc D c x ↔ c = x ∨ DAnc D c (D x) := by
  unfold DAnc
  rw [Relation.ReflTransGen.cases_tail_iff]
  constructor
  · rintro (rfl | ⟨w, hw, hD, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (hD ▸ hw)
  · rintro (rfl | hw)
    · exact Or.inl rfl
    · exact Or.inr ⟨D x, hw, rfl, Ne.symm hr⟩

theorem TreeSpec.ddepth_lt_of_dAnc (h : TreeSpec r n D ρ) {a b : ℕ} (hab : DAnc D a b)
    (hb : b < size r) : a = b ∨ ddepth D ρ a < ddepth D ρ b := by
  induction hab with
  | refl => exact Or.inl rfl
  | tail _ hst ih =>
    obtain ⟨hD, hne⟩ := hst
    subst hD
    rw [h.ddepth_parent hb (Ne.symm hne)]
    rcases ih (h.lt _ hb) with e | e
    · right; rw [e]; omega
    · right; omega

theorem top_of_root {x : ℕ} (hx : D x = x) : top D ρ x = x := Function.iterate_fixed hx _

/-- `explore`'s step at a node `y` around the popped node `x`. -/
def visit (x : ℕ) (t : (ℕ → Option ℕ) × (ℕ → ℕ) × List ℕ) (y : ℕ) :
    (ℕ → Option ℕ) × (ℕ → ℕ) × List ℕ :=
  if t.1 y = none then
    (Function.update t.1 y (some x), Function.update t.2.1 y (t.2.1 x + 1), y :: t.2.2)
  else t

theorem explore_succ (k : ℕ) (par : ℕ → Option ℕ) (dep : ℕ → ℕ) (x : ℕ) (stack : List ℕ) :
    explore r (k + 1) (par, dep) (x :: stack) =
      explore r k (((around r x).foldl (visit x) (par, dep, stack)).1,
        ((around r x).foldl (visit x) (par, dep, stack)).2.1)
        ((around r x).foldl (visit x) (par, dep, stack)).2.2 := rfl

theorem explore_nil (k : ℕ) (s : (ℕ → Option ℕ) × (ℕ → ℕ)) : explore r k s [] = s := by
  cases k <;> rfl

/-- The pass over the nodes around `x` gives each node of `L` without a parent the parent `x` and
the depth one below `x`, and pushes exactly those nodes. -/
theorem foldl_visit (x : ℕ) (L : List ℕ) (par : ℕ → Option ℕ) (dep : ℕ → ℕ) (st : List ℕ)
    (hx : par x ≠ none) :
    ∃ new, (L.foldl (visit x) (par, dep, st)).2.2 = new ++ st ∧ new.Nodup ∧
      (∀ y, y ∈ new ↔ par y = none ∧ y ∈ L) ∧
      (∀ y, (L.foldl (visit x) (par, dep, st)).1 y =
        if par y = none ∧ y ∈ L then some x else par y) ∧
      (∀ y, (L.foldl (visit x) (par, dep, st)).2.1 y =
        if par y = none ∧ y ∈ L then dep x + 1 else dep y) := by
  induction L generalizing par dep st with
  | nil => exact ⟨[], by simp⟩
  | cons y L ih =>
    rw [List.foldl_cons]
    by_cases hy : par y = none
    · have hxy : x ≠ y := fun e => hx (e ▸ hy)
      have hv : visit x (par, dep, st) y = (Function.update par y (some x),
          Function.update dep y (dep x + 1), y :: st) := by simp [visit, hy]
      rw [hv]
      have hx' : Function.update par y (some x) x ≠ none := by
        rw [Function.update_of_ne hxy]; exact hx
      obtain ⟨new, h1, h2, h3, h4, h5⟩ := ih _ (Function.update dep y (dep x + 1)) (y :: st) hx'
      have hyn : y ∉ new := by
        intro hm; have := ((h3 y).1 hm).1; simp at this
      refine ⟨new ++ [y], by simp [h1], ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨h2, List.nodup_singleton y, ?_⟩
        simp only [List.mem_singleton]
        rintro a ha b rfl rfl; exact hyn ha
      · intro z
        rw [List.mem_append, h3]
        by_cases hz : z = y
        · subst hz; simp [hy]
        · simp [hz]
      · intro z
        rw [h4]
        by_cases hz : z = y
        · subst hz; simp [hy]
        · simp [hz]
      · intro z
        rw [h5, Function.update_of_ne hxy]
        by_cases hz : z = y
        · subst hz; simp [hy]
        · simp [hz]
    · have hv : visit x (par, dep, st) y = (par, dep, st) := by simp [visit, hy]
      rw [hv]
      obtain ⟨new, h1, h2, h3, h4, h5⟩ := ih par dep st hx
      refine ⟨new, h1, h2, ?_, ?_, ?_⟩
      · intro z; rw [h3]
        by_cases hz : z = y
        · subst hz; simp [hy]
        · simp [hz]
      · intro z; rw [h4]
        by_cases hz : z = y
        · subst hz; simp [hy]
        · simp [hz]
      · intro z; rw [h5]
        by_cases hz : z = y
        · subst hz; simp [hy]
        · simp [hz]

/-- The number of nodes without a parent yet. -/
def unset (r : Report) (par : ℕ → Option ℕ) : ℕ :=
  ((Finset.range (size r)).filter fun y => par y = none).card

/-- If a tree's root has a parent and every node with a parent that is off the stack has all its
children with parents, then every node of the tree has a parent. -/
theorem TreeSpec.all_set (h : TreeSpec r n D ρ) {a : ℕ} {par : ℕ → Option ℕ}
    (hpa : par a ≠ none)
    (hcl : ∀ z, z < size r → top D ρ z = a → par z ≠ none →
      ∀ c, c < size r → D c = z → c ≠ z → par c ≠ none) :
    ∀ m z, ρ z < m → z < size r → top D ρ z = a → par z ≠ none := by
  intro m
  induction m with
  | zero => intro z hz; omega
  | succ m ih =>
    intro z hm hz ht
    by_cases hr : D z = z
    · rw [top_of_root hr] at ht; subst ht; exact hpa
    · have := h.rank z hz hr
      have ht' : top D ρ (D z) = a := by rw [h.top_parent hz, ht]
      exact hcl (D z) (h.lt z hz) ht' (ih (D z) (by omega) (h.lt z hz) ht') z hz rfl
        (fun e => hr e.symm)

/-- **Walking one tree**: started from a stack inside the tree of the root `a`, with enough fuel,
`explore` gives every node of the tree its parent `D` and depth `ddepth`, and touches no other
node. -/
theorem TreeSpec.explore_spec (h : TreeSpec r n D ρ) {a : ℕ} :
    ∀ (k : ℕ) (par : ℕ → Option ℕ) (dep : ℕ → ℕ) (stack : List ℕ),
    stack.length + unset r par < k → par a ≠ none →
    (∀ z ∈ stack, z < size r ∧ top D ρ z = a ∧ par z ≠ none) →
    (∀ z, z < size r → top D ρ z = a → par z ≠ none →
      par z = some (D z) ∧ dep z = ddepth D ρ z) →
    (∀ z, z < size r → top D ρ z = a → par z ≠ none → par (D z) ≠ none) →
    (∀ z, z < size r → top D ρ z = a → par z ≠ none → z ∉ stack →
      ∀ c, c < size r → D c = z → c ≠ z → par c ≠ none) →
    (∀ z, ¬ (z < size r ∧ top D ρ z = a) →
      (explore r k (par, dep) stack).1 z = par z ∧ (explore r k (par, dep) stack).2 z = dep z) ∧
    (∀ z, z < size r → top D ρ z = a →
      (explore r k (par, dep) stack).1 z = some (D z) ∧
      (explore r k (par, dep) stack).2 z = ddepth D ρ z) := by
  intro k
  induction k with
  | zero => intro par dep stack hk; omega
  | succ k ih =>
    intro par dep stack hk hpa hst hc hd he
    cases stack with
    | nil =>
      rw [explore_nil]
      refine ⟨fun z _ => ⟨rfl, rfl⟩, fun z hz ht => hc z hz ht ?_⟩
      exact h.all_set hpa (fun z hz ht hp => he z hz ht hp List.not_mem_nil) _ z
        (Nat.lt_succ_self _) hz ht
    | cons x rest =>
      obtain ⟨hxS, hxt, hxp⟩ := hst x List.mem_cons_self
      obtain ⟨new, h1, h2, h3, h4, h5⟩ := foldl_visit x (Forest.around r x) par dep rest hxp
      rw [explore_succ]
      set t := (Forest.around r x).foldl (visit x) (par, dep, rest) with ht
      have hL : ∀ y, y ∈ Forest.around r x → y < size r ∧ top D ρ y = a := by
        intro y hy
        obtain ⟨hyS, (⟨-, rfl⟩ | ⟨rfl, -⟩)⟩ := (h.around x hxS y).1 hy
        · exact ⟨hyS, by rw [h.top_parent hxS, hxt]⟩
        · exact ⟨hyS, by rw [← h.top_parent hyS, hxt]⟩
      have hnew : ∀ y, par y = none → y ∈ Forest.around r x → D y = x ∧ y ≠ x := by
        intro y hy hya
        obtain ⟨-, (⟨-, rfl⟩ | hc')⟩ := (h.around x hxS y).1 hya
        · exact absurd hy (hd x hxS hxt hxp)
        · exact hc'
      have hmono : ∀ y, par y ≠ none → t.1 y = par y := fun y hy => by rw [h4]; simp [hy]
      have hdmono : ∀ y, par y ≠ none → t.2.1 y = dep y := fun y hy => by rw [h5]; simp [hy]
      have hset : ∀ y, t.1 y ≠ none → par y ≠ none ∨ y ∈ new := by
        intro y hy
        by_cases hp : par y = none
        · right; rw [h3]; by_contra hn; rw [h4] at hy; simp only [hn, ↓reduceIte] at hy; exact hy hp
        · exact Or.inl hp
      have hpos : ∀ y, y ∈ Forest.around r x → t.1 y ≠ none := by
        intro y hy
        by_cases hp : par y = none
        · rw [h4]; simp [hp, hy]
        · rw [hmono y hp]; exact hp
      have hU : unset r t.1 + new.length = unset r par := by
        have hsub : new.toFinset ⊆ (Finset.range (size r)).filter fun y => par y = none := by
          intro y hy
          rw [List.mem_toFinset, h3] at hy
          simpa [hy.1] using (hL y hy.2).1
        have heq : ((Finset.range (size r)).filter fun y => t.1 y = none) =
            ((Finset.range (size r)).filter fun y => par y = none) \ new.toFinset := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset, h3, h4]
          by_cases hp : par y = none <;> by_cases hy : y ∈ Forest.around r x <;> simp [hp, hy]
        unfold unset
        rw [heq, Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup h2]
        have := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup h2] at this
        omega
      refine (fun hh => ?_) (ih t.1 t.2.1 t.2.2 ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨ih1, ih2⟩ := hh
        refine ⟨fun z hz => ?_, ih2⟩
        have hzn : ¬ (par z = none ∧ z ∈ Forest.around r x) := fun hh => hz (hL z hh.2)
        rw [(ih1 z hz).1, (ih1 z hz).2, h4, h5]
        simp [hzn]
      · rw [h1, List.length_append]
        simp only [List.length_cons] at hk
        omega
      · rw [hmono a hpa]; exact hpa
      · intro z hz
        rw [h1, List.mem_append] at hz
        rcases hz with hz | hz
        · obtain ⟨hp, hza⟩ := (h3 z).1 hz
          exact ⟨(hL z hza).1, (hL z hza).2, hpos z hza⟩
        · obtain ⟨a1, a2, a3⟩ := hst z (List.mem_cons_of_mem _ hz)
          exact ⟨a1, a2, by rw [hmono z a3]; exact a3⟩
      · intro z hz hzt hzp
        by_cases hp : par z = none ∧ z ∈ Forest.around r x
        · obtain ⟨hDz, hzx⟩ := hnew z hp.1 hp.2
          rw [h4, h5]
          simp only [hp, and_self, ↓reduceIte]
          refine ⟨by rw [hDz], ?_⟩
          rw [h.ddepth_parent hz (by rw [hDz]; exact Ne.symm hzx), hDz,
            (hc x hxS hxt hxp).2]
        · rw [h4, h5]
          simp only [hp, ↓reduceIte]
          have hpz : par z ≠ none := by
            intro e; apply hzp; rw [h4]; simp only [hp, ↓reduceIte]; exact e
          exact hc z hz hzt hpz
      · intro z hz hzt hzp
        rcases hset z hzp with hp | hp
        · rw [hmono _ (hd z hz hzt hp)]; exact hd z hz hzt hp
        · obtain ⟨hp1, hp2⟩ := (h3 z).1 hp
          rw [(hnew z hp1 hp2).1, hmono x hxp]; exact hxp
      · intro z hz hzt hzp hzs c hc hDc hcz
        rw [h1, List.mem_append, not_or] at hzs
        by_cases hzx : z = x
        · subst hzx
          exact hpos c ((h.around z hz c).2 ⟨hc, Or.inr ⟨hDc, hcz⟩⟩)
        · rcases hset z hzp with hp | hp
          · have := he z hz hzt hp (by
              rw [List.mem_cons, not_or]; exact ⟨hzx, hzs.2⟩) c hc hDc hcz
            rw [hmono c this]; exact this
          · exact absurd hp hzs.1

/-- Some vertex before `m` has its node in the tree of `x`. -/
def Placed (r : Report) (D ρ : ℕ → ℕ) (m x : ℕ) : Prop :=
  ∃ q < m, top D ρ (nodeOfVertex r q) = top D ρ x

theorem placed_succ {m x : ℕ} :
    Placed r D ρ (m + 1) x ↔ Placed r D ρ m x ∨ top D ρ (nodeOfVertex r m) = top D ρ x := by
  constructor
  · rintro ⟨q, hq, e⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
    · exact Or.inl ⟨q, hq, e⟩
    · exact Or.inr e
  · rintro (⟨q, hq, e⟩ | e)
    · exact ⟨q, by omega, e⟩
    · exact ⟨m, by omega, e⟩

theorem root_zero : root r 0 = (fun _ => none, fun _ => 0) := rfl

theorem root_succ (m : ℕ) : root r (m + 1) =
    if (root r m).1 (nodeOfVertex r m) = none then
      explore r (size r + 1) (Function.update (root r m).1 (nodeOfVertex r m)
        (some (nodeOfVertex r m)), (root r m).2) [nodeOfVertex r m]
    else root r m := by
  rw [root, root, List.range_succ, List.foldl_append]; rfl

/-- **Rooting**: after trying the vertices below `m`, a node in the tree of one of them has parent
`D` and depth `ddepth`; any other node has neither. -/
theorem TreeSpec.root_spec (h : TreeSpec r n D ρ) : ∀ m ≤ n, ∀ x < size r,
    (Placed r D ρ m x → (root r m).1 x = some (D x) ∧ (root r m).2 x = ddepth D ρ x) ∧
    (¬ Placed r D ρ m x → (root r m).1 x = none ∧ (root r m).2 x = 0) := by
  intro m
  induction m with
  | zero =>
    intro _ x _
    refine ⟨fun ⟨q, hq, _⟩ => absurd hq (Nat.not_lt_zero q), fun _ => ?_⟩
    simp [root_zero]
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    have haS := h.node_lt m (by omega)
    set a := nodeOfVertex r m with ha_def
    by_cases hpl : Placed r D ρ m a
    · have hs : (root r m).1 a ≠ none := by rw [((ih a haS).1 hpl).1]; simp
      rw [root_succ, ← ha_def]; simp only [hs, ↓reduceIte]
      intro x hx
      have hiff : Placed r D ρ (m + 1) x ↔ Placed r D ρ m x := by
        rw [placed_succ]
        refine ⟨?_, Or.inl⟩
        rintro (hx' | e)
        · exact hx'
        · obtain ⟨q, hq, e'⟩ := hpl; exact ⟨q, hq, e'.trans e⟩
      rw [hiff]; exact ih x hx
    · have hs : (root r m).1 a = none := ((ih a haS).2 hpl).1
      have hroot : D a = a := h.first m (by omega) (fun q hq e => hpl ⟨q, hq, e⟩)
      have hta : top D ρ a = a := top_of_root hroot
      rw [root_succ, ← ha_def]; simp only [hs, ↓reduceIte]
      set par := Function.update (root r m).1 a (some a) with hpar
      have hpa : par a = some a := by rw [hpar, Function.update_self]
      have hone : ∀ z, z < size r → top D ρ z = a → par z ≠ none → z = a := by
        intro z hz hzt hzp
        by_contra hza
        rw [hpar, Function.update_of_ne hza] at hzp
        refine hzp ((ih z hz).2 fun hp => hpl ?_).1
        obtain ⟨q, hq, e⟩ := hp
        exact ⟨q, hq, e.trans (hzt.trans hta.symm)⟩
      have hU : unset r par < size r := by
        have hsub : ((Finset.range (size r)).filter fun y => par y = none) ⊆
            (Finset.range (size r)).erase a := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase] at hy ⊢
          exact ⟨by rintro rfl; rw [hpa] at hy; simp at hy, hy.1⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (by simpa using haS), Finset.card_range] at this
        unfold unset; omega
      obtain ⟨hfr, htr⟩ := h.explore_spec (a := a) (size r + 1) par (root r m).2 [a]
        (by simp; omega) (by rw [hpa]; simp)
        (by intro z hz; simp only [List.mem_singleton] at hz; subst hz
            exact ⟨haS, hta, by rw [hpa]; simp⟩)
        (by
          intro z hz hzt hzp
          obtain rfl := hone z hz hzt hzp
          refine ⟨by rw [hpa, hroot], ?_⟩
          rw [ddepth_root hroot]
          exact ((ih a haS).2 hpl).2)
        (by
          intro z hz hzt hzp
          obtain rfl := hone z hz hzt hzp
          rw [hroot]; exact hzp)
        (by
          intro z hz hzt hzp hzs
          obtain rfl := hone z hz hzt hzp
          simp at hzs)
      intro x hx
      by_cases hxt : top D ρ x = a
      · have hpl' : Placed r D ρ (m + 1) x := placed_succ.2 (Or.inr (by rw [hta, hxt]))
        exact ⟨fun _ => htr x hx hxt, fun hn => absurd hpl' hn⟩
      · have hxa : x ≠ a := by rintro rfl; exact hxt hta
        have hiff : Placed r D ρ (m + 1) x ↔ Placed r D ρ m x := by
          rw [placed_succ, hta]
          exact ⟨fun h' => h'.resolve_right (fun e => hxt e.symm), Or.inl⟩
        rw [hiff, (hfr x fun hh => hxt hh.2).1, (hfr x fun hh => hxt hh.2).2, hpar,
          Function.update_of_ne hxa]
        exact ih x hx

theorem forest_parent_length (g : Graph) : (forest g r).parent.length = size r := by
  simp [forest]

theorem forest_nodeOf {g : Graph} {u : ℕ} (hu : u < g.n) :
    (forest g r).nodeOf.getD u 0 = nodeOfVertex r u := by
  simp [forest, hu]

/-- **Parents and depths**: on every node in the tree of a vertex's node, the forest's parent is
`D` and its depth is the number of steps up. -/
theorem parent_eq (h : TreeSpec r n D ρ) {g : Graph} (hn : g.n = n) {x : ℕ} (hx : x < size r)
    (hp : ∃ p < n, top D ρ (nodeOfVertex r p) = top D ρ x) :
    (forest g r).parent.getD x x = D x ∧ (forest g r).depth.getD x 0 = ddepth D ρ x := by
  have := (h.root_spec n le_rfl x hx).1 hp
  simp [forest, hn, hx, this.1, this.2]

theorem meet_step_ge (f : Forest) {k x y : ℕ} (passed : List ℕ) (hxy : x ≠ y)
    (hd : f.depth.getD y 0 ≤ f.depth.getD x 0) :
    meet f (k + 1) x y passed =
      if f.parent.getD x x = x then none
      else meet f k (f.parent.getD x x) y (f.parent.getD x x :: passed) := by
  have hd' : ¬ f.depth.getD x 0 < f.depth.getD y 0 := by omega
  simp only [meet, hxy, hd', ↓reduceIte]

theorem meet_step_lt (f : Forest) {k x y : ℕ} (passed : List ℕ) (hxy : x ≠ y)
    (hd : f.depth.getD x 0 < f.depth.getD y 0) :
    meet f (k + 1) x y passed =
      if f.parent.getD y y = y then none
      else meet f k (f.parent.getD y y) x (f.parent.getD y y :: passed) := by
  simp only [meet, hxy, hd, ↓reduceIte]

/-- Node `z` has a child above exactly one of `x` and `y`. -/
def Splits (D : ℕ → ℕ) (z x y : ℕ) : Prop :=
  ∃ c, D c = z ∧ c ≠ z ∧ (DAnc D c x ↔ ¬ DAnc D c y)

theorem not_splits_self (z x : ℕ) : ¬ Splits D z x x := by
  rintro ⟨c, -, -, hc⟩; tauto

theorem splits_comm (z x y : ℕ) : Splits D z x y ↔ Splits D z y x := by
  unfold Splits
  refine exists_congr fun c => and_congr_right fun _ => and_congr_right fun _ => ?_
  tauto

theorem splits_step {z x y : ℕ} (hr : D x ≠ x) (hxy : ¬ DAnc D x y) :
    Splits D z x y ↔ z = D x ∨ Splits D z (D x) y := by
  have key : z = D x → Splits D z x y := by
    rintro rfl
    exact ⟨x, rfl, Ne.symm hr, iff_of_true Relation.ReflTransGen.refl hxy⟩
  constructor
  · rintro ⟨c, hcz, hc, hiff⟩
    by_cases hcx : c = x
    · left; rw [← hcz, hcx]
    · right
      refine ⟨c, hcz, hc, ?_⟩
      rw [← hiff, dAnc_iff hr]
      simp [hcx]
  · rintro (e | ⟨c, hcz, hc, hiff⟩)
    · exact key e
    · by_cases hcx : c = x
      · exact key (by rw [← hcz, hcx])
      · refine ⟨c, hcz, hc, ?_⟩
        rw [← hiff, dAnc_iff hr]
        simp [hcx]

theorem TreeSpec.placed_parent (h : TreeSpec r n D ρ) {m x : ℕ} (hx : x < size r)
    (hp : Placed r D ρ m x) : Placed r D ρ m (D x) := by
  obtain ⟨q, hq, e⟩ := hp
  exact ⟨q, hq, by rw [h.top_parent hx, e]⟩

theorem TreeSpec.not_dAnc (h : TreeSpec r n D ρ) {x y : ℕ} (hy : y < size r) (hxy : x ≠ y)
    (hd : ddepth D ρ y ≤ ddepth D ρ x) : ¬ DAnc D x y := by
  intro ha
  rcases h.ddepth_lt_of_dAnc ha hy with e | e
  · exact hxy e
  · omega

/-- What `meet` collects: the nodes stepped onto are, besides those already passed, exactly the
nodes with a child above exactly one of the two ends. -/
theorem TreeSpec.meet_some (h : TreeSpec r n D ρ) {g : Graph} (hn : g.n = n) :
    ∀ (k x y : ℕ) (passed l : List ℕ), x < size r → Placed r D ρ n x → y < size r →
      Placed r D ρ n y → meet (forest g r) k x y passed = some l →
      ∀ z, z ∈ l ↔ z ∈ passed ∨ Splits D z x y := by
  intro k
  induction k with
  | zero => intro x y passed l _ _ _ _ hm; simp [meet] at hm
  | succ k ih =>
    intro x y passed l hx hpx hy hpy hm z
    by_cases hxy : x = y
    · subst hxy
      simp only [meet, ↓reduceIte, Option.some.injEq] at hm
      subst hm
      simp [not_splits_self]
    · obtain ⟨hPx, hdx⟩ := parent_eq h hn hx hpx
      obtain ⟨hPy, hdy⟩ := parent_eq h hn hy hpy
      by_cases hd : ddepth D ρ y ≤ ddepth D ρ x
      · rw [meet_step_ge _ _ hxy (by rw [hdx, hdy]; exact hd), hPx] at hm
        by_cases hr : D x = x
        · simp [hr] at hm
        · simp only [hr, ↓reduceIte] at hm
          rw [ih _ _ _ _ (h.lt x hx) (h.placed_parent hx hpx) hy hpy hm z,
            splits_step hr (h.not_dAnc hy hxy hd)]
          simp only [List.mem_cons]; tauto
      · rw [meet_step_lt _ _ hxy (by rw [hdx, hdy]; omega), hPy] at hm
        by_cases hr : D y = y
        · simp [hr] at hm
        · simp only [hr, ↓reduceIte] at hm
          rw [ih _ _ _ _ (h.lt y hy) (h.placed_parent hy hpy) hx hpx hm z, splits_comm z x y,
            splits_step hr (h.not_dAnc hx (Ne.symm hxy) (by omega))]
          simp only [List.mem_cons]; tauto

/-- `meet`, with fuel above the two depths, fails exactly on ends in different trees. -/
theorem TreeSpec.meet_none (h : TreeSpec r n D ρ) {g : Graph} (hn : g.n = n) :
    ∀ (k x y : ℕ) (passed : List ℕ), x < size r → Placed r D ρ n x → y < size r →
      Placed r D ρ n y → ddepth D ρ x + ddepth D ρ y < k →
      (meet (forest g r) k x y passed = none ↔ top D ρ x ≠ top D ρ y) := by
  intro k
  induction k with
  | zero => intro x y passed _ _ _ _ hk; omega
  | succ k ih =>
    intro x y passed hx hpx hy hpy hk
    by_cases hxy : x = y
    · subst hxy
      simp [meet]
    · obtain ⟨hPx, hdx⟩ := parent_eq h hn hx hpx
      obtain ⟨hPy, hdy⟩ := parent_eq h hn hy hpy
      by_cases hd : ddepth D ρ y ≤ ddepth D ρ x
      · rw [meet_step_ge _ _ hxy (by rw [hdx, hdy]; exact hd), hPx]
        by_cases hr : D x = x
        · simp only [hr, ↓reduceIte, true_iff]
          rw [ddepth_root hr] at hd
          have hry := h.root_of_ddepth hy (by omega)
          rw [top_of_root hr, top_of_root hry]; exact hxy
        · simp only [hr, ↓reduceIte]
          rw [ih _ _ _ (h.lt x hx) (h.placed_parent hx hpx) hy hpy
            (by rw [h.ddepth_parent hx hr] at hk; omega), h.top_parent hx]
      · rw [meet_step_lt _ _ hxy (by rw [hdx, hdy]; omega), hPy]
        by_cases hr : D y = y
        · simp only [hr, ↓reduceIte, true_iff]
          rw [ddepth_root hr] at hd
          omega
        · simp only [hr, ↓reduceIte]
          rw [ih _ _ _ (h.lt y hy) (h.placed_parent hy hpy) hx hpx
            (by rw [h.ddepth_parent hy hr] at hk; omega), h.top_parent hy, ne_comm]

/-- **Meeting**: for vertices `u v < n`, `separators` answers `none` exactly when their nodes have
different roots; otherwise it lists the cut vertices whose node `z` is neither end and has a child
`c` (`D c = z`, `c ≠ z`) above exactly one of the two ends. -/
theorem separators_spec (h : TreeSpec r n D ρ) {g : Graph} (hn : g.n = n) {u v : ℕ}
    (hu : u < n) (hv : v < n) :
    let x := nodeOfVertex r u; let y := nodeOfVertex r v
    ((forest g r).separators u v = none ↔ top D ρ x ≠ top D ρ y) ∧
    ∀ l, (forest g r).separators u v = some l → ∀ q, q ∈ l ↔ ∃ k < r.cutVertices.length,
      r.cutVertices[k]? = some q ∧ r.blocks.length + k ≠ x ∧ r.blocks.length + k ≠ y ∧
      ∃ c, D c = r.blocks.length + k ∧ c ≠ r.blocks.length + k ∧
        (DAnc D c x ↔ ¬ DAnc D c y) := by
  intro x y
  have hx : x < size r := h.node_lt u hu
  have hy : y < size r := h.node_lt v hv
  have hpx : Placed r D ρ n x := ⟨u, hu, rfl⟩
  have hpy : Placed r D ρ n y := ⟨v, hv, rfl⟩
  have hsep : (forest g r).separators u v = (meet (forest g r) (2 * size r + 1) x y []).map
      fun passed => (List.range r.cutVertices.length).filterMap fun k =>
        if r.blocks.length + k ∈ passed ∧ r.blocks.length + k ≠ x ∧ r.blocks.length + k ≠ y
        then r.cutVertices[k]? else none := by
    simp only [separators, forest_parent_length, forest_nodeOf (hn ▸ hu),
      forest_nodeOf (hn ▸ hv)]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hsep, Option.map_eq_none_iff]
    exact h.meet_none hn _ x y [] hx hpx hy hpy
      (by have := h.ddepth_lt hx; have := h.ddepth_lt hy; omega)
  · intro l hl q
    rw [hsep, Option.map_eq_some_iff] at hl
    obtain ⟨passed, hm, rfl⟩ := hl
    have hmem := h.meet_some hn _ x y [] passed hx hpx hy hpy hm
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨k, hk, he⟩
      split_ifs at he with hc
      exact ⟨k, List.mem_range.1 hk, he, hc.2.1, hc.2.2, by simpa [Splits] using (hmem _).1 hc.1⟩
    · rintro ⟨k, hk, he, h1, h2, hs⟩
      refine ⟨k, List.mem_range.2 hk, ?_⟩
      have hc : r.blocks.length + k ∈ passed ∧ r.blocks.length + k ≠ x ∧
          r.blocks.length + k ≠ y := ⟨(hmem _).2 (Or.inr hs), h1, h2⟩
      simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
      exact he

theorem filterMap_range_sublist :
    ∀ (L : List ℕ) (p : ℕ → Prop) [DecidablePred p],
      ((List.range L.length).filterMap fun k => if p k then L[k]? else none).Sublist L
  | [], _, _ => by simp
  | a :: L, p, _ => by
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map]
    have ih := filterMap_range_sublist L (fun k => p (k + 1))
    have e : ((fun k => if p k then (a :: L)[k]? else none) ∘ Nat.succ) =
        fun k => if p (k + 1) then L[k]? else none := by
      funext k; simp
    rw [e]
    by_cases h0 : p 0
    · simp only [h0, ↓reduceIte, List.getElem?_cons_zero]
      exact ih.cons_cons a
    · simp only [h0, ↓reduceIte]
      exact ih.cons a

/-- `separators` lists cut vertices in the order of `r.cutVertices`. -/
theorem separators_sublist {g : Graph} {u v : ℕ} {l : List ℕ}
    (hl : (forest g r).separators u v = some l) : l.Sublist r.cutVertices := by
  simp only [separators, Option.map_eq_some_iff] at hl
  obtain ⟨passed, -, rfl⟩ := hl
  exact filterMap_range_sublist r.cutVertices _

end Forest

end AlgoDesign.Graphs.Blocks
