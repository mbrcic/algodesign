/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Flows.MaxFlow.RulesBasic

/-!
# Max flow: Edmonds–Karp's path rule

Source: Edmonds and Karp, "Theoretical improvements in algorithmic efficiency for network flow
problems" (1972); the Flow chapter, "Max flow".

A round searches first in, first out from the source over residual arrows with room, in adjacency
order, and stops as soon as the sink is labeled. If the sink is labeled, the round adds one path,
the one traced back from the sink, by its bottleneck; otherwise it adds nothing. The rule keeps
nothing between rounds.
-/

@[expose] public section

namespace AlgoDesign.Flows

/-- **Edmonds–Karp's path rule**: one fewest-arrows path per round, by its bottleneck. -/
def edmondsKarp : PathRule where
  Memory := Unit
  start _ := ()
  round N _ f :=
    ((), match shortestPath N f 1 with
      | some p => [byBottleneck N f p]
      | none => [])

/-- Edmonds–Karp's rule keeps the promise of every path rule. -/
theorem edmondsKarp_promise : edmondsKarp.Promise where
  sendsAlong N h _ f _ := by
    change FitInTurn N f (match shortestPath N f 1 with
      | some p => [byBottleneck N f p] | none => [])
    split
    · exact ⟨(shortestPath_sends h ‹_›).1, trivial⟩
    · trivial
  addsAtLeastOne N h _ f _ x hx := by
    change x ∈ (match shortestPath N f 1 with
      | some p => [byBottleneck N f p] | none => []) at hx
    split at hx
    · rw [List.mem_singleton.1 hx]; exact (shortestPath_sends h ‹_›).2
    · simp at hx
  noneOnlyWhenDone N h _ f _ hr p hp := by
    change (match shortestPath N f 1 with
      | some p => [byBottleneck N f p] | none => []) = [] at hr
    split at hr
    · simp at hr
    · exact shortestPath_none h ‹_› p hp.1 fun a ha => fits_of_le_one le_rfl (hp.2.2 a ha)

/-! ## At most n·m added paths -/

/-- **What the bottleneck counts say**, for `cnt a` the number of added paths whose bottleneck
was the residual arrow `a`: an arrow emptied `c` times belongs to the network, `2c ≤ n`, its tail
is at least `2(c - 1)` arrows away and its head at least `2c - 1`, and once it has room again its
tail is at least `2c` away. -/
def CountsKept (N : Network) (g : Flow) (cnt : ResidualArrow → ℕ) : Prop :=
  ∀ a, cnt a ≠ 0 → a.id < N.g.arrows.length ∧ 2 * cnt a ≤ N.g.n ∧
    FarAtLeast N g (a.tail N) (2 * (cnt a - 1)) ∧ FarAtLeast N g (a.head N) (2 * cnt a - 1) ∧
    (0 < a.residualCapacity N g → FarAtLeast N g (a.tail N) (2 * cnt a))

/-- All the counts, arrow by arrow of the network. -/
def countTotal (N : Network) (cnt : ResidualArrow → ℕ) : ℕ :=
  ((List.range N.g.arrows.length).map fun i => cnt (.along i) + cnt (.back i)).sum

theorem countTotal_le {N : Network} {g : Flow} {cnt : ResidualArrow → ℕ}
    (hK : CountsKept N g cnt) : countTotal N cnt ≤ N.g.n * N.g.arrows.length := by
  have hb : ∀ a, 2 * cnt a ≤ N.g.n := fun a => by
    by_cases ha : cnt a = 0
    · omega
    · exact (hK a ha).2.1
  have := sum_range_le (g := fun i => cnt (.along i) + cnt (.back i)) (b := N.g.n)
    (fun i => by have := hb (.along i); have := hb (.back i); omega) N.g.arrows.length
  rw [countTotal, Nat.mul_comm]
  exact this

theorem countTotal_bump (N : Network) (cnt : ResidualArrow → ℕ) {b : ResidualArrow}
    (hb : b.id < N.g.arrows.length) :
    countTotal N (Function.update cnt b (cnt b + 1)) = countTotal N cnt + 1 := by
  set G : ℕ → ℕ := fun i => cnt (.along i) + cnt (.back i)
  have e : (fun i => Function.update cnt b (cnt b + 1) (.along i) +
      Function.update cnt b (cnt b + 1) (.back i)) = Function.update G b.id (G b.id + 1) := by
    funext i
    by_cases hi : i = b.id
    · subst hi
      cases b <;> simp [G, ResidualArrow.id] <;> omega
    · rw [Function.update_of_ne hi]
      cases b <;> simp_all [G, ResidualArrow.id]
  unfold countTotal
  rw [e]
  exact sum_range_bump _ hb

/-- **Adding the path the search finds keeps what the counts say**, with one more count for an
arrow of the path that it empties. -/
theorem countsKept_step {N : Network} (h : N.WellFormed) {g : Flow} (hg : IsFlow N g)
    {p : List ResidualArrow} (hp : shortestPath N g 1 = some p) {cnt : ResidualArrow → ℕ}
    (hK : CountsKept N g cnt) : ∃ b ∈ p, b.id < N.g.arrows.length ∧
      CountsKept N ((byBottleneck N g p).apply g) (Function.update cnt b (cnt b + 1)) := by
  have hc := shortestPath_climbs h hp
  have hls : (search N g 1).level N.sink = some p.length := hc.level_end
  have hlen : g.length = N.g.arrows.length := hg.2.2
  have hids : ∀ c ∈ (byBottleneck N g p).path, c.id < g.length := fun c hc' =>
    hlen ▸ ends_ids_lt hc.1 c hc'
  have hpn : p.length < N.g.n := hc.length_lt h
  obtain ⟨b, hb, hbr⟩ := bottleneck_mem (f := g) (N := N) (ne_nil_of_ends h hc.1)
  obtain ⟨k, hk, hk', hkl⟩ := shortestPath_levels h hp hls hb
  have hbk : 2 * cnt b ≤ k := by
    by_cases hcb : cnt b = 0
    · omega
    · obtain ⟨r, hre, hrr, hrl⟩ := search_near hk
      have := (hK b hcb).2.2.2.2 (hc.2.2 b hb).1 r hre hrr
      omega
  have hfar : ∀ {v K}, FarAtLeast N g v K → FarAtLeast N ((byBottleneck N g p).apply g) v K :=
    fun hK' => shortestPath_far h hlen hp hls hK'
  refine ⟨b, hb, ends_ids_lt hc.1 b hb, fun a ha => ?_⟩
  by_cases hab : a = b
  · subst hab
    simp only [Function.update_self] at ha ⊢
    refine ⟨ends_ids_lt hc.1 a hb, by omega, hfar ((search_far h hls hk (by omega)).mono
      (by omega)), hfar ((search_far h hls hk' hkl).mono (by omega)), fun hr => ?_⟩
    rw [residualCapacity_apply_mem N hids hc.ids_nodup hb] at hr
    simp [byBottleneck, hbr] at hr
  · simp only [Function.update_of_ne hab] at ha ⊢
    obtain ⟨hid, hn, h1, h2, h3⟩ := hK a ha
    refine ⟨hid, hn, hfar h1, hfar h2, fun hr => ?_⟩
    rcases residualCapacity_apply_grow_mem (x := byBottleneck N g p) hc hids hr with
      h0 | ⟨d, hd, hne, hdid⟩
    · exact hfar (h3 h0)
    · obtain ⟨hct, hch⟩ := ResidualArrow.ends_of_partner N hne hdid
      obtain ⟨j, hj, hj', hjl⟩ := shortestPath_levels h hp hls hd
      obtain ⟨r, hre, hrr, hrl⟩ := search_near hj
      have := h2 r (by rw [hre, hch]) hrr
      rw [hct]
      exact hfar ((search_far h hls hj' hjl).mono (by omega))

/-- The counts so far and the paths the remaining rounds add come to at most n·m. -/
theorem edmondsKarp_runRounds {N : Network} (h : N.WellFormed) :
    ∀ (k : ℕ) (g : Flow) (cnt : ResidualArrow → ℕ), IsFlow N g → CountsKept N g cnt →
      countTotal N cnt + (edmondsKarp.runRounds N k () g).1.flatten.length ≤
        N.g.n * N.g.arrows.length
  | 0, _, _, _, hK => by simpa [PathRule.runRounds] using countTotal_le hK
  | k + 1, g, cnt, hg, hK => by
    cases hp : shortestPath N g 1 with
    | none =>
      rw [edmondsKarp.runRounds_nil N k (m' := ()) (show edmondsKarp.round N () g = ((), []) by
        change ((), match shortestPath N g 1 with
          | some p => [byBottleneck N g p] | none => []) = _
        rw [hp])]
      simpa using countTotal_le hK
    | some p =>
      rw [edmondsKarp.runRounds_cons N k (m' := ())
        (show edmondsKarp.round N () g = ((), [byBottleneck N g p]) by
          change ((), match shortestPath N g 1 with
            | some p => [byBottleneck N g p] | none => []) = _
          rw [hp])]
      obtain ⟨b, -, hbid, hK'⟩ := countsKept_step h hg hp hK
      have hflow := (apply_isFlow h hg (shortestPath_sends h hp).1).1
      have := edmondsKarp_runRounds h k _ _ hflow hK'
      rw [countTotal_bump N cnt hbid] at this
      have e : applyAll g [byBottleneck N g p] = (byBottleneck N g p).apply g := rfl
      rw [e]
      simp only [List.flatten_cons, List.length_append, List.length_singleton]
      omega

/-- **At most n·m added paths** with Edmonds–Karp's rule. -/
theorem edmondsKarp_augmentations :
    (edmondsKarp.ops edmondsKarp_promise).AugmentationsAtMostNM := by
  intro N h
  have := edmondsKarp_runRounds h (totalCapacity N + 1) (Flow.zero N) (fun _ => 0)
    (zero_isFlow N) fun _ ha => absurd rfl ha
  have h0 : countTotal N (fun _ => 0) = 0 := by simp [countTotal]
  rw [h0, Nat.zero_add] at this
  exact this

/-- **A bound set by the network's size alone** with Edmonds–Karp's rule: n·m added paths. -/
theorem edmondsKarp_bound : (edmondsKarp.ops edmondsKarp_promise).BoundSetBySize :=
  ⟨fun n m => n * m, edmondsKarp_augmentations⟩

end AlgoDesign.Flows
