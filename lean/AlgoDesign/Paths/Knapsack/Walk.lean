/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Paths.Knapsack.Basic

/-!
# Knapsack as a longest path: the walk

Source: Ahuja, Magnanti and Orlin, *Network Flows* (1993), p. 102: the table loop "is just a
special implementation of one of the standard algorithms for solving shortest path problems",
relaxation in an order with no arrow going back.

The walk fills the table layer by layer, which is a topological order of the vertices. From each
reached vertex `(i, w)` of the last layer filled, by increasing `w`, it tries the skip, then the
take when it fits; a move raises its end's known gain when it gains more, or reaches it first. The
vertices are never built as a graph.
-/

@[expose] public section

namespace AlgoDesign.Paths.Knapsack

/-! ## The walk -/

/-- **Relax** the vertex `x` of the next layer with the gain `b`: keep `b` if `x` has no known gain
or `b` is more. -/
def relax (f : ℕ → Option ℤ) (x : ℕ) (b : ℤ) : ℕ → Option ℤ :=
  if (f x).all (· < b) then Function.update f x (some b) else f

/-- **Try the moves out of `(i, w)`**, a vertex of the layer `row`, deciding item `it`: if `w` is
reached, the skip, then the take if it fits; the next layer and the count of moves tried. -/
def tryMoves (it : Item) (C : ℕ) (row : ℕ → Option ℤ) (acc : (ℕ → Option ℤ) × ℕ) (w : ℕ) :
    (ℕ → Option ℤ) × ℕ :=
  match row w with
  | none => acc
  | some b =>
    if w + it.weight ≤ C then
      (relax (relax acc.1 w b) (w + it.weight) (b + it.value), acc.2 + 2)
    else (relax acc.1 w b, acc.2 + 1)

/-- **The start**: only `(0, 0)` reached, with gain 0. -/
def start (_ : List Item) (_ : ℕ) : State :=
  ⟨0, fun i w => if i = 0 ∧ w = 0 then some 0 else none, 0⟩

/-- **One step**: fill the next layer from the last one filled, trying the moves out of each of
its vertices by increasing weight. -/
def step (items : List Item) (C : ℕ) (st : State) : State :=
  if st.decided < items.length then
    let r := (List.range (C + 1)).foldl
      (tryMoves (item items st.decided) C (st.best st.decided)) (fun _ => none, st.tried)
    ⟨st.decided + 1, Function.update st.best (st.decided + 1) r.1, r.2⟩
  else st

/-- **The walk**: one step per item, then the answer read off the table. -/
def knapsack (items : List Item) (C : ℕ) : Packing :=
  answer items C ((step items C)^[items.length] (start items C))

/-! ## Trying the moves of a layer -/

theorem omax_assoc (a b c : Option ℤ) : max (max a b) c = max a (max b c) := by
  cases a <;> cases b <;> cases c <;> simp [max_assoc]

theorem omax_shuffle (a b c d : Option ℤ) : max (max a b) (max c d) = max (max a c) (max b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [max_left_comm, max_comm]

theorem relax_eq (f : ℕ → Option ℤ) (x : ℕ) (b : ℤ) :
    relax f x b = Function.update f x (max (f x) (some b)) := by
  unfold relax
  cases hfx : f x with
  | none => simp
  | some c =>
    by_cases hcb : c < b
    · simp [hcb, max_eq_right hcb.le]
    · simp only [Option.all_some, hcb, decide_false, Bool.false_eq_true, ite_false,
        Option.max_some_some, max_eq_left (not_lt.1 hcb)]
      rw [← hfx, Function.update_eq_self]

/-- **What trying the moves out of `(i, k)` does to the next layer at `x`**: the gain the skip
brings if `x = k`, and the gain the take brings if it fits and `x = k + weight`, kept when more. -/
theorem tryMoves_fst (it : Item) (C : ℕ) (row : ℕ → Option ℤ) (acc : (ℕ → Option ℤ) × ℕ)
    (k x : ℕ) : (tryMoves it C row acc k).1 x = max (acc.1 x) (max (if k = x then row k else none)
      (if k + it.weight = x ∧ x ≤ C then (row k).map (· + it.value) else none)) := by
  unfold tryMoves
  cases hr : row k with
  | none => simp
  | some b =>
    split_ifs with hC h1 h2 h2 h1 h2 h2
    all_goals simp only [relax_eq, Function.update_apply]
    all_goals split_ifs <;> first
      | omega
      | (subst_vars; simp only [Option.max_none_right, Option.max_none_left, Option.map_some,
          omax_assoc])

theorem tryMoves_snd (it : Item) (C : ℕ) (row : ℕ → Option ℤ) (acc : (ℕ → Option ℤ) × ℕ)
    (k : ℕ) : (tryMoves it C row acc k).2 ≤ acc.2 + 2 := by
  unfold tryMoves
  cases row k with
  | none => simp
  | some b => split_ifs <;> simp

/-- **The next layer is the better of each vertex's two moves in**, the table loop: after trying
the moves out of the vertices of weight below `k`, the vertex `x` holds the better of the skip from
`x` and the take from `x - weight`, among those tried. -/
theorem foldl_tryMoves_fst (it : Item) (C : ℕ) (row : ℕ → Option ℤ) (t k x : ℕ) :
    ((List.range k).foldl (tryMoves it C row) (fun _ => none, t)).1 x =
      max (if x < k then row x else none)
        (if it.weight ≤ x ∧ x - it.weight < k ∧ x ≤ C then (row (x - it.weight)).map (· + it.value)
          else none) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, tryMoves_fst, ih,
      omax_shuffle]
    congr 1
    · split_ifs <;> first | omega | (subst_vars; simp)
    · split_ifs <;> first | omega | (rw [show x - it.weight = k by omega]; simp) | simp

theorem foldl_tryMoves_snd (it : Item) (C : ℕ) (row : ℕ → Option ℤ) (t k : ℕ) :
    ((List.range k).foldl (tryMoves it C row) (fun _ => none, t)).2 ≤ t + 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have := tryMoves_snd it C row ((List.range k).foldl (tryMoves it C row) (fun _ => none, t)) k
    omega

/-! ## The invariants along the walk -/

variable {items : List Item} {C : ℕ}

theorem step_of_lt {st : State} (h : st.decided < items.length) :
    step items C st =
      let r := (List.range (C + 1)).foldl
        (tryMoves (item items st.decided) C (st.best st.decided)) (fun _ => none, st.tried)
      ⟨st.decided + 1, Function.update st.best (st.decided + 1) r.1, r.2⟩ := by
  unfold step
  simp only [h, ↓reduceIte]

theorem step_of_not_lt {st : State} (h : ¬ st.decided < items.length) : step items C st = st := by
  unfold step
  simp only [h, ↓reduceIte]

theorem valid_start : Valid items C (start items C) := by
  refine ⟨fun i hi w _ => ?_, Nat.zero_le _⟩
  obtain rfl : i = 0 := Nat.le_zero.1 hi
  simpa [start] using longestTo_zero (items := items) (C := C) w

/-- **A step keeps the walk legal**: each vertex of the new layer holds the better of its two
moves in, which is the largest gain into it. -/
theorem valid_step {st : State} (h : Valid items C st) : Valid items C (step items C st) := by
  by_cases hd : st.decided < items.length
  · rw [step_of_lt hd]
    refine ⟨fun i hi w hw => ?_, hd⟩
    simp only at hi ⊢
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · rw [Function.update_of_ne (by omega)]
      exact h.1 i (by omega) w hw
    · rw [Function.update_self, foldl_tryMoves_fst]
      have h₁ := h.1 _ le_rfl w hw
      have h₂ := h.1 _ le_rfl (w - (item items st.decided).weight) (by omega)
      have hs := longestTo_succ hd h₁ h₂
      have e₁ : (if w < C + 1 then st.best st.decided w else none) = st.best st.decided w := by
        simp only [show w < C + 1 by omega, ↓reduceIte]
      have e₂ : ((item items st.decided).weight ≤ w ∧ w - (item items st.decided).weight < C + 1 ∧
          w ≤ C) ↔ ((item items st.decided).weight ≤ w ∧ w ≤ C) := by omega
      rw [e₁]
      simp only [e₂]
      exact hs
  · rw [step_of_not_lt hd]
    exact h

/-- **The walk after `k` steps**: legal, `k` items decided, at most two moves tried from each
vertex of the layers before. -/
theorem iterate_spec (k : ℕ) (hk : k ≤ items.length) :
    Valid items C ((step items C)^[k] (start items C)) ∧
      ((step items C)^[k] (start items C)).decided = k ∧
      ((step items C)^[k] (start items C)).tried ≤ 2 * (k * (C + 1)) := by
  induction k with
  | zero => exact ⟨valid_start, rfl, by simp [start]⟩
  | succ k ih =>
    obtain ⟨hv, hd, ht⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    have hlt : ((step items C)^[k] (start items C)).decided < items.length := by omega
    refine ⟨valid_step hv, ?_, ?_⟩
    · rw [step_of_lt hlt]; simp [hd]
    · rw [step_of_lt hlt]
      simp only
      have := foldl_tryMoves_snd (item items ((step items C)^[k] (start items C)).decided) C
        (((step items C)^[k] (start items C)).best ((step items C)^[k] (start items C)).decided)
        ((step items C)^[k] (start items C)).tried (C + 1)
      have hm : (k + 1) * (C + 1) = k * (C + 1) + (C + 1) := by rw [Nat.add_mul, Nat.one_mul]
      rw [hm]
      omega

/-! ## Walking back -/

/-- **Walking back from a reached vertex `(i, w)` gives items worth its gain and weighing `w`**,
listed in increasing order among the first `i`. -/
theorem chosen_spec {st : State} (h : Valid items C st) :
    ∀ i ≤ st.decided, ∀ w ≤ C, ∀ b, st.best i w = some b →
      (chosen items st.best i w).Sublist (List.range i) ∧
        weightOf items (chosen items st.best i w) = w ∧
        valueOf items (chosen items st.best i w) = b := by
  intro i
  induction i with
  | zero =>
    intro _ w hw b hb
    have := (h.1 0 (Nat.zero_le _) w hw).unique (longestTo_zero w)
    rw [hb] at this
    split_ifs at this with hw0
    · subst hw0
      simp only [Option.some.injEq] at this
      subst this
      simp [chosen, weightOf, valueOf]
  | succ i ih =>
    intro hi w hw b hb
    have hin : i < items.length := by have := h.2; unfold DecidedAtMostItems at this; omega
    have hrec := (h.1 (i + 1) hi w hw).unique
      (longestTo_succ hin (h.1 i (by omega) w hw)
        (h.1 i (by omega) (w - (item items i).weight) (by omega)))
    rw [hb] at hrec
    simp only [hw, and_true] at hrec
    rw [chosen]
    split_ifs with hc
    · obtain ⟨hwt, htw⟩ := hc
      cases hb2 : st.best i (w - (item items i).weight) with
      | none => rw [hb2] at htw; simp [takeWins] at htw
      | some b2 =>
        rw [hb2] at htw
        simp only [takeWins] at htw
        have hbv : b = b2 + (item items i).value := by
          simp only [hwt, ↓reduceIte, hb2, Option.map_some] at hrec
          cases hbw : st.best i w with
          | none => rw [hbw] at hrec; simpa using hrec
          | some c =>
            rw [hbw] at htw hrec
            simp only [Option.all_some, decide_eq_true_eq] at htw
            simp only [Option.max_some_some, Option.some.injEq] at hrec
            omega
        obtain ⟨h1, h2, h3⟩ := ih (by omega) (w - (item items i).weight) (by omega) b2 hb2
        refine ⟨?_, ?_, ?_⟩
        · rw [List.range_succ]; exact h1.append (List.Sublist.refl _)
        · simp only [weightOf, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil] at h2 ⊢
          omega
        · simp only [valueOf, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil] at h3 ⊢
          omega
    · have hbw : st.best i w = some b := by
        by_cases hwt : (item items i).weight ≤ w
        · simp only [hwt, ↓reduceIte] at hrec
          have htw : takeWins (st.best i (w - (item items i).weight)) (item items i).value
              (st.best i w) = false := by
            simpa [hwt] using hc
          cases hb2 : st.best i (w - (item items i).weight) with
          | none => rw [hb2] at hrec; simpa using hrec.symm
          | some b2 =>
            rw [hb2] at htw hrec
            simp only [takeWins] at htw
            cases hbw : st.best i w with
            | none => rw [hbw] at htw; simp at htw
            | some c =>
              rw [hbw] at htw hrec
              simp only [Option.all_some, decide_eq_false_iff_not, not_le] at htw
              simp only [Option.map_some, Option.max_some_some, Option.some.injEq] at hrec
              rw [Option.some.injEq]
              omega
        · simp only [hwt, ↓reduceIte] at hrec
          simpa using hrec.symm
      obtain ⟨h1, h2, h3⟩ := ih (by omega) w hw b hbw
      refine ⟨?_, h2, h3⟩
      rw [List.range_succ]
      exact h1.trans (List.sublist_append_left _ _)

/-! ## The best end -/

theorem keepBetter_spec (row : ℕ → Option ℤ) (acc : Option (ℤ × ℕ)) (x : ℕ) :
    (∀ b w, keepBetter row acc x = some (b, w) → acc = some (b, w) ∨ (w = x ∧ row x = some b)) ∧
    (∀ c ∈ row x, ∃ b w, keepBetter row acc x = some (b, w) ∧ c ≤ b) ∧
    (∀ b₀ w₀, acc = some (b₀, w₀) → ∃ b w, keepBetter row acc x = some (b, w) ∧ b₀ ≤ b) ∧
    (keepBetter row acc x = none → acc = none) := by
  unfold keepBetter
  cases hx : row x with
  | none => exact ⟨fun _ _ h => Or.inl h, by simp, fun b₀ w₀ h => ⟨b₀, w₀, h, le_rfl⟩, id⟩
  | some b =>
    cases acc with
    | none =>
      refine ⟨fun b' w' h => Or.inr ?_, fun c hc => ⟨b, x, rfl, ?_⟩, by simp, by simp⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.2.symm, by rw [h.1]⟩
      · simp only [Option.mem_def, Option.some.injEq] at hc; omega
    | some a =>
      obtain ⟨b₀, w₀⟩ := a
      by_cases hlt : b₀ < b
      · simp only [hlt, ↓reduceIte]
        refine ⟨fun b' w' h => Or.inr ?_, fun c hc => ⟨b, x, rfl, ?_⟩, fun b₁ w₁ h => ⟨b, x, rfl,
          ?_⟩, by simp⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨h.2.symm, by rw [h.1]⟩
        · simp only [Option.mem_def, Option.some.injEq] at hc; omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · simp only [hlt, ↓reduceIte]
        refine ⟨fun b' w' h => Or.inl h, fun c hc => ⟨b₀, w₀, rfl, ?_⟩, fun b₁ w₁ h => ⟨b₀, w₀,
          rfl, ?_⟩, by simp⟩
        · simp only [Option.mem_def, Option.some.injEq] at hc; omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega

/-- What keeping the better gain over the weights `ws` gives: a weight among them, or the one
before, with the most known gain, at least as much as before; and something whenever some
weight has a known gain. -/
theorem foldl_keepBetter (row : ℕ → Option ℤ) :
    ∀ (ws : List ℕ) (acc : Option (ℤ × ℕ)),
      (∀ b w, ws.foldl (keepBetter row) acc = some (b, w) →
        (acc = some (b, w) ∨ (w ∈ ws ∧ row w = some b)) ∧ (∀ x ∈ ws, ∀ c ∈ row x, c ≤ b) ∧
          ∀ b₀ w₀, acc = some (b₀, w₀) → b₀ ≤ b) ∧
      (ws.foldl (keepBetter row) acc = none → acc = none ∧ ∀ x ∈ ws, row x = none)
  | [], acc => by
    refine ⟨fun b w h => ⟨Or.inl h, by simp, fun b₀ w₀ h₀ => ?_⟩, fun h => ⟨h, by simp⟩⟩
    simp only [List.foldl_nil] at h
    rw [h, Option.some.injEq, Prod.mk.injEq] at h₀
    rw [h₀.1]
  | x :: ws, acc => by
    obtain ⟨ih₁, ih₂⟩ := foldl_keepBetter row ws (keepBetter row acc x)
    obtain ⟨k₁, k₂, k₃, k₄⟩ := keepBetter_spec row acc x
    simp only [List.foldl_cons]
    refine ⟨fun b w h => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := ih₁ b w h
      refine ⟨?_, fun y hy c hc => ?_, fun b₀ w₀ h₀ => ?_⟩
      · rcases h1 with h1 | h1
        · rcases k₁ b w h1 with h1 | ⟨rfl, hb⟩
          · exact Or.inl h1
          · exact Or.inr ⟨List.mem_cons_self, hb⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1.1, h1.2⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · obtain ⟨b₁, w₁, he, hle⟩ := k₂ c hc
          exact hle.trans (h3 b₁ w₁ he)
        · exact h2 y hy c hc
      · obtain ⟨b₁, w₁, he, hle⟩ := k₃ b₀ w₀ h₀
        exact hle.trans (h3 b₁ w₁ he)
    · obtain ⟨h1, h2⟩ := ih₂ h
      refine ⟨k₄ h1, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · cases hc : row y with
        | none => rfl
        | some c =>
          obtain ⟨b₁, w₁, he, -⟩ := k₂ c hc
          rw [h1] at he
          cases he
      · exact h2 y hy

/-! ## The promise -/

/-- The table the walk ends with, every item decided. -/
abbrev final (items : List Item) (C : ℕ) : State := (step items C)^[items.length] (start items C)

/-- **The answer is the best value, and the chosen items fit and give it.** -/
theorem knapsack_spec (items : List Item) (C : ℕ) :
    IsBest items C (knapsack items C).value ∧ Fits items C (knapsack items C).items ∧
      valueOf items (knapsack items C).items = (knapsack items C).value := by
  obtain ⟨hv, hd, -⟩ := iterate_spec (items := items) (C := C) items.length le_rfl
  set st := final items C
  have hlast : ∀ w ≤ C, LongestTo items C (items.length, w) (st.best items.length w) :=
    fun w hw => hv.1 _ hd.ge w hw
  -- every packing that fits is a path into the last layer
  have hpath := (paths_are_packings items C).2
  have hempty : Fits items C [] := ⟨List.nil_sublist _, by simp [weightOf]⟩
  have h0 : st.best items.length 0 ≠ none := by
    intro h
    have := (hlast 0 (Nat.zero_le C)).1 _ (by simpa [weightOf] using (hpath [] hempty).1)
    rw [h] at this
    exact this
  have hk : knapsack items C = answer items C st := rfl
  obtain ⟨hs, hn⟩ := foldl_keepBetter (st.best items.length) (List.range (C + 1)) none
  cases hbe : bestEnd (st.best items.length) (List.range (C + 1)) with
  | none =>
    exact absurd ((hn hbe).2 0 (List.mem_range.2 (Nat.succ_pos C))) h0
  | some bw =>
    obtain ⟨b, w⟩ := bw
    obtain ⟨hmem, hmax, -⟩ := hs b w hbe
    obtain ⟨hwC, hbw⟩ : w ≤ C ∧ st.best items.length w = some b := by
      rcases hmem with h | ⟨hw, hb⟩
      · cases h
      · exact ⟨Nat.lt_succ_iff.1 (List.mem_range.1 hw), hb⟩
    have hans : knapsack items C = ⟨b, chosen items st.best items.length w⟩ := by
      rw [hk]; unfold answer; rw [hbe]
    obtain ⟨h1, h2, h3⟩ := chosen_spec hv items.length hd.ge w hwC b hbw
    have hfit : Fits items C (chosen items st.best items.length w) := ⟨h1, by rw [h2]; exact hwC⟩
    rw [hans]
    refine ⟨⟨⟨_, hfit, h3⟩, fun S hS => ?_⟩, hfit, h3⟩
    obtain ⟨hp, -, hg⟩ := hpath S hS
    have hat := (hlast _ hS.2).1 _ hp
    rw [hg] at hat
    cases hc : st.best items.length (weightOf items S) with
    | none => rw [hc] at hat; exact absurd hat id
    | some c =>
      rw [hc] at hat
      exact le_trans (α := ℤ) hat
        (hmax _ (List.mem_range.2 (Nat.lt_succ_of_le hS.2)) c hc)

/-- **At most two moves tried from each vertex before the last layer.** -/
theorem knapsack_cost (items : List Item) (C : ℕ) :
    (final items C).tried ≤ 2 * (items.length * (C + 1)) :=
  (iterate_spec items.length le_rfl).2.2

end AlgoDesign.Paths.Knapsack
