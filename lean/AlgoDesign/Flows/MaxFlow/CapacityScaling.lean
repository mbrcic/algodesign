/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.RulesBasic

/-!
# Max flow: capacity scaling's path rule

Source: Ahuja, Magnanti and Orlin, *Network Flows* (1993), §7.3; the Flow chapter, "Max flow".

The rule keeps a threshold Δ, first the largest power of two not above the largest capacity of any
arrow (0 if every capacity is 0). A round runs Edmonds–Karp's search over residual arrows with room
of at least Δ. If it labels the sink, the round adds the path traced back, by its bottleneck, and
keeps Δ. Otherwise it halves Δ and searches again within the same round; when the search with
Δ = 1 finds nothing, the round adds nothing and keeps 0. A threshold of 0 searches like 1: every
arrow of a path needs some room.
-/

@[expose] public section

namespace AlgoDesign.Flows

/-- The largest power of two not above `c`, found by doubling from `p` at most `k` times. -/
def topPowerOfTwoFrom (c : ℕ) : ℕ → ℕ → ℕ
  | 0, p => p
  | k + 1, p => if 2 * p ≤ c then topPowerOfTwoFrom c k (2 * p) else p

/-- **The largest power of two not above `c`**, and 0 for 0. -/
def topPowerOfTwo (c : ℕ) : ℕ := if c = 0 then 0 else topPowerOfTwoFrom c c 1

/-- The largest capacity of any arrow; 0 when there is none. -/
def maxCapacity (N : Network) : ℕ := (N.ids.map N.capOf).foldl max 0

/-- **One round** from threshold `Δ`, in at most `k` searches: search with `Δ`; if it finds a path,
add it by its bottleneck and keep `Δ`; otherwise halve `Δ` and search again, and after the
search with `Δ` of 1 or less finds nothing, add nothing and keep 0. A `Δ` of 0 searches like 1,
since the search asks every arrow for some room as well. -/
def scalingRound (N : Network) (f : Flow) : ℕ → ℕ → ℕ × List Augmentation
  | 0, _ => (0, [])
  | k + 1, Δ =>
    match shortestPath N f Δ with
    | some p => (Δ, [byBottleneck N f p])
    | none => if Δ ≤ 1 then (0, []) else scalingRound N f k (Δ / 2)

/-- **Capacity scaling's path rule**: the threshold is kept between rounds; a round searches with
it, halving it until a path turns up or no path is left. -/
def capacityScaling : PathRule where
  Memory := ℕ
  start N := topPowerOfTwo (maxCapacity N)
  round N Δ f := scalingRound N f (Δ + 1) Δ

theorem scalingRound_cases (N : Network) (f : Flow) : ∀ k Δ, (scalingRound N f k Δ).2 = [] ∨
    ∃ D p, shortestPath N f D = some p ∧ (scalingRound N f k Δ).2 = [byBottleneck N f p]
  | 0, _ => Or.inl rfl
  | k + 1, Δ => by
    unfold scalingRound
    split
    · exact Or.inr ⟨Δ, _, ‹_›, rfl⟩
    · split_ifs
      · exact Or.inl rfl
      · exact scalingRound_cases N f k (Δ / 2)

/-- A round that adds nothing ran a search with a threshold of 1 or less that found nothing. -/
theorem scalingRound_nil (N : Network) (f : Flow) : ∀ k Δ, Δ + 1 ≤ k →
    (scalingRound N f k Δ).2 = [] → ∃ D ≤ 1, shortestPath N f D = none
  | 0, _, hk, _ => absurd hk (by omega)
  | k + 1, Δ, hk, hr => by
    unfold scalingRound at hr
    split at hr
    · simp at hr
    · split_ifs at hr with hΔ
      · exact ⟨Δ, hΔ, ‹_›⟩
      · exact scalingRound_nil N f k (Δ / 2) (by omega) hr

/-- Capacity scaling's rule keeps the promise of every path rule. -/
theorem capacityScaling_promise : capacityScaling.Promise where
  sendsAlong := fun N h (Δ : ℕ) f _ => by
    change FitInTurn N f (scalingRound N f (Δ + 1) Δ).2
    rcases scalingRound_cases N f (Δ + 1) Δ with he | ⟨D, p, hp, he⟩ <;> rw [he]
    · trivial
    · exact ⟨(shortestPath_sends h hp).1, trivial⟩
  addsAtLeastOne := fun N h (Δ : ℕ) f _ x hx => by
    change x ∈ (scalingRound N f (Δ + 1) Δ).2 at hx
    rcases scalingRound_cases N f (Δ + 1) Δ with he | ⟨D, p, hp, he⟩ <;> rw [he] at hx
    · simp at hx
    · rw [List.mem_singleton.1 hx]; exact (shortestPath_sends h hp).2
  noneOnlyWhenDone := fun N h (Δ : ℕ) f _ hr p hp => by
    obtain ⟨D, hD, hn⟩ := scalingRound_nil N f (Δ + 1) Δ le_rfl hr
    exact shortestPath_none h hn p hp.1 fun a ha => fits_of_le_one hD (hp.2.2 a ha)

end AlgoDesign.Flows
