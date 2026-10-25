/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import Cslib.Init
public import Mathlib.Data.List.Basic
public import AlgoDesign.Strings.RankSelect.Basic

/-!
# The two-level rank directory computes `rank`

Sources: Jacobson (FOCS 1989); Navarro, *Compact Data Structures*, §4.2.2.

Blocks of `B` positions, superblocks of `k` blocks. Per-block popcounts (`blockCounts`), then one
pass keeping a running total (`buildUpTo`, keeping `Directory.Valid`). `rankTwoLevel_eq` and
`occTwoLevel_eq`: the queries over it answer `rank` and `occ`. Machine words, integer widths,
`select`'s samples and the byte-to-dense map are not modelled.
-/

@[expose] public section

namespace AlgoDesign.Strings

/-- Set positions in a list of bits. `rank b i` is `pop (b.take i)`. -/
def pop (l : List Bool) : Nat := (l.filter id).length

theorem pop_append (l m : List Bool) : pop (l ++ m) = pop l + pop m := by
  simp [pop, List.filter_append]

/-- `rank` over a longer prefix is `rank` over the shorter one plus the bits in between. -/
theorem rank_add (b : List Bool) (a c : Nat) :
    rank b (a + c) = rank b a + pop ((b.drop a).take c) := by
  change pop (b.take (a + c)) = pop (b.take a) + _
  rw [List.take_add, pop_append]

/-! ## Division facts the directory's indexing runs on -/

/-- Blocks needed to cover `n` positions at width `B`: `⌈n / B⌉`. -/
def numBlocks (B n : Nat) : Nat := (n + B - 1) / B

private theorem split_div (j k : Nat) (hk : 0 < k) : ∃ q r, r < k ∧ j = r + q * k :=
  ⟨j / k, j % k, Nat.mod_lt _ hk, (Nat.mod_add_div' j k).symm⟩

/-- One more position adds a superblock exactly when the new block opens one. -/
private theorem ceil_succ (j k : Nat) (hk : 0 < k) :
    (j + 1 + k - 1) / k = (j + k - 1) / k + (if j % k = 0 then 1 else 0) := by
  obtain ⟨q, r, hr, rfl⟩ := split_div j k hk
  rw [show r + q * k + 1 + k - 1 = (r + k) + q * k by omega,
    show r + q * k + k - 1 = (r + k - 1) + q * k by omega,
    Nat.add_mul_div_right _ _ hk, Nat.add_mul_div_right _ _ hk, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hr, Nat.add_div_right _ hk, Nat.div_eq_of_lt hr]
  by_cases h0 : r = 0
  · subst h0
    rw [show 0 + k - 1 = k - 1 by omega, Nat.div_eq_of_lt (by omega : k - 1 < k)]
    simp; omega
  · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    simp [h0]

/-- A position below `n` lies in one of the first `⌈n / k⌉` groups of `k`. -/
private theorem div_lt_ceil (a n k : Nat) (hk : 0 < k) (ha : a < n) :
    a / k < (n + k - 1) / k := by
  have h1 : a / k ≤ (n - 1) / k := Nat.div_le_div_right (by omega)
  rw [show n + k - 1 = (n - 1) + k by omega, Nat.add_div_right _ hk]
  omega

/-- The blocks cover the vector. -/
private theorem len_le_numBlocks_mul (B n : Nat) (hB : 0 < B) : n ≤ numBlocks B n * B := by
  have := Nat.lt_div_mul_add (a := n + B - 1) hB
  unfold numBlocks
  omega

/-- Every block but the last ends inside the vector. -/
private theorem mul_lt_of_lt_numBlocks (B n j : Nat) (hj : j < numBlocks B n) :
    j * B < n := by
  have h1 : (j + 1) * B ≤ numBlocks B n * B := Nat.mul_le_mul_right _ hj
  have h2 : numBlocks B n * B ≤ n + B - 1 := Nat.div_mul_le_self _ _
  rw [Nat.succ_mul] at h1
  by_cases hB : B = 0
  · subst hB; simp [numBlocks] at hj
  · omega

/-! ## The block counts -/

/-- One population count per block of `B` positions. -/
def blockCounts (B : Nat) (b : List Bool) : List Nat :=
  (List.range (numBlocks B b.length)).map fun j => pop ((b.drop (j * B)).take B)

theorem length_blockCounts (B : Nat) (b : List Bool) :
    (blockCounts B b).length = numBlocks B b.length := by
  simp [blockCounts]

/-- The first `j` block counts sum to `rank` at position `j · B`. -/
theorem sum_take_blockCounts (B : Nat) (b : List Bool) :
    ∀ j, j ≤ numBlocks B b.length → ((blockCounts B b).take j).sum = rank b (j * B) := by
  intro j
  induction j with
  | zero => intro _; simp [rank]
  | succ j ih =>
    intro hj
    have hlt : j < (blockCounts B b).length := by rw [length_blockCounts]; omega
    rw [List.take_succ_eq_append_getElem hlt, List.sum_append, ih (by omega), Nat.succ_mul,
      rank_add]
    simp [blockCounts]

/-! ## The directory, built as `from_block_counts` builds it -/

/-- One build step over block `j` with count `c`: open a superblock if `j` starts one, record the
total relative to it, then add `c`. -/
def dirStep (k : Nat) (d : Directory) (j c : Nat) : Directory :=
  let supers := if j % k = 0 then d.supers ++ [d.total] else d.supers
  { supers := supers, blocks := d.blocks ++ [d.total - supers[j / k]!], total := d.total + c }

/-- The loop's first `j` iterations. -/
def buildUpTo (k : Nat) (counts : List Nat) : Nat → Directory
  | 0 => ⟨[], [], 0⟩
  | j + 1 => dirStep k (buildUpTo k counts j) j counts[j]!

/-- `TwoLevel::from_block_counts`. -/
def fromBlockCounts (k : Nat) (counts : List Nat) : Directory :=
  buildUpTo k counts counts.length

/-- The directory over a bit vector: `BitIndex::new`. -/
def directory (B k : Nat) (b : List Bool) : Directory :=
  fromBlockCounts k (blockCounts B b)

private theorem getElem!_append_left {l : List Nat} {i : Nat} (x : Nat) (h : i < l.length) :
    (l ++ [x])[i]! = l[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos l i h, List.getElem_append_left h]

private theorem getElem!_append_right (l : List Nat) (x : Nat) : (l ++ [x])[l.length]! = x := by
  rw [getElem!_pos _ _ (by simp)]; simp

/-- The build keeps `Directory.Valid` after every block. -/
theorem Directory.valid_buildUpTo (k : Nat) (hk : 0 < k) (counts : List Nat) :
    ∀ j, j ≤ counts.length → Directory.Valid k counts j (buildUpTo k counts j) := by
  intro j
  induction j with
  | zero =>
    intro _
    unfold Directory.Valid Directory.RunningTotalRight Directory.OneSuperblockPerGroup
      Directory.SuperblocksHoldTotals Directory.OneEntryPerBlock Directory.BlocksCountFromSuperblock
    refine ⟨by simp [buildUpTo], ?_, fun s hs => by simp [buildUpTo] at hs, by simp [buildUpTo],
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    simp only [buildUpTo, List.length_nil, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | succ j ih =>
    intro hj
    obtain ⟨htot, hslen, hsup, hblen, hblk⟩ := ih (by omega)
    unfold Directory.RunningTotalRight at htot
    unfold Directory.OneSuperblockPerGroup at hslen
    unfold Directory.SuperblocksHoldTotals at hsup
    unfold Directory.OneEntryPerBlock at hblen
    unfold Directory.BlocksCountFromSuperblock at hblk
    have hjlt : j < counts.length := by omega
    have hsum : (counts.take (j + 1)).sum = (counts.take j).sum + counts[j]! := by
      rw [List.take_succ_eq_append_getElem hjlt, List.sum_append, getElem!_pos counts j hjlt]
      simp
    -- The superblock list after this step, and what it holds.
    have hceil := ceil_succ j k hk
    have hdivmul : ∀ s, s * k ≤ j → (counts.take (s * k)).sum ≤ (counts.take j).sum := by
      intro s hs
      have := List.take_append_drop (s * k) (counts.take j)
      rw [List.take_take, Nat.min_eq_left hs] at this
      conv_rhs => rw [← this]
      rw [List.sum_append]; omega
    set d := buildUpTo k counts j with hd
    have hnew : (if j % k = 0 then d.supers ++ [d.total] else d.supers).length
        = (j + 1 + k - 1) / k := by
      rw [hceil]; split <;> simp [hslen]
    have hnewv : ∀ s, s < (if j % k = 0 then d.supers ++ [d.total] else d.supers).length →
        (if j % k = 0 then d.supers ++ [d.total] else d.supers)[s]!
          = (counts.take (s * k)).sum := by
      intro s hs
      split
      · rename_i hmod
        by_cases hsl : s < d.supers.length
        · rw [getElem!_append_left _ hsl]; exact (getElem!_pos _ s hsl).trans (hsup s hsl)
        · have hs' : s = d.supers.length := by
            simp only [hmod, ↓reduceIte, List.length_append, List.length_singleton] at hs; omega
          -- A superblock opens at block `j = s · k`.
          have hsj : s * k = j := by
            obtain ⟨q, r, hr, hq⟩ := split_div j k hk
            have hr0 : r = 0 := by
              rw [hq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr] at hmod; exact hmod
            subst hr0
            have hq' : (j + k - 1) / k = q := by
              rw [hq, show 0 + q * k + k - 1 = (k - 1) + q * k by omega,
                Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt (by omega : k - 1 < k)]
              simp
            rw [hs', hslen, hq', hq]; simp
          rw [hs', getElem!_append_right, htot, ← hs', hsj]
      · rename_i hmod
        simp only [hmod, ↓reduceIte] at hs
        exact (getElem!_pos _ s hs).trans (hsup s hs)
    -- Block `j` lies in superblock `j / k`, which exists after this step.
    have hjk : j / k < (if j % k = 0 then d.supers ++ [d.total] else d.supers).length := by
      rw [hnew]; exact div_lt_ceil j (j + 1) k hk (by omega)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change d.total + counts[j]! = _
      rw [htot, hsum]
    · exact hnew
    · exact fun s hs => (getElem!_pos _ s hs).symm.trans (hnewv s hs)
    · change (d.blocks ++ _).length = j + 1
      simp [hblen]
    · intro i hi
      change (d.blocks ++ [d.total - _])[i]? = _
      by_cases hij : i < j
      · rw [List.getElem?_append_left (by omega)]; exact hblk i hij
      · have hi' : i = j := by omega
        subst hi'
        rw [List.getElem?_append_right (by omega), hblen, Nat.sub_self, List.getElem?_cons_zero,
          hnewv _ hjk, htot]

/-- The finished directory. -/
theorem Directory.valid_directory (B k : Nat) (hk : 0 < k) (b : List Bool) :
    Directory.Valid k (blockCounts B b) (numBlocks B b.length) (directory B k b) := by
  have := Directory.valid_buildUpTo k hk (blockCounts B b) (numBlocks B b.length)
    (by rw [length_blockCounts]; exact Nat.le_refl _)
  unfold directory fromBlockCounts
  rw [length_blockCounts]
  exact this

/-! ## The queries -/

/-- `BitIndex::rank`: the total at or past the end; otherwise superblock + block + the popcount of
the block's positions before `i`. -/
def rankTwoLevel (B k : Nat) (b : List Bool) (i : Nat) : Nat :=
  let d := directory B k b
  if b.length ≤ i then d.total
  else
    let blk := i / B
    d.supers[blk / k]! + d.blocks[blk]! + pop ((b.drop (blk * B)).take (i - blk * B))

/-- The checkpoint before block `blk`: superblock plus relative count, which is `rank` at the
block's start. -/
private theorem checkpoint (B k : Nat) (_hB : 0 < B) (hk : 0 < k) (b : List Bool) (blk : Nat)
    (hblk : blk < numBlocks B b.length) :
    (directory B k b).supers[blk / k]! + (directory B k b).blocks[blk]! = rank b (blk * B) := by
  obtain ⟨-, hslen, hsup, -, hblk'⟩ := Directory.valid_directory B k hk b
  unfold Directory.OneSuperblockPerGroup at hslen
  unfold Directory.SuperblocksHoldTotals at hsup
  unfold Directory.BlocksCountFromSuperblock at hblk'
  have hs : blk / k < (directory B k b).supers.length := by
    rw [hslen]; exact div_lt_ceil blk _ k hk hblk
  have hle : blk / k * k ≤ blk := Nat.div_mul_le_self _ _
  rw [getElem!_pos (directory B k b).supers _ hs, hsup _ hs, List.getElem!_eq_getElem?_getD,
    hblk' _ hblk,
    Option.getD_some, sum_take_blockCounts B b _ (by omega),
    sum_take_blockCounts B b _ (by omega)]
  have := rank_mono b (Nat.mul_le_mul_right B hle)
  omega

/-- The total is the population count of the whole vector. -/
private theorem total_eq (B k : Nat) (hB : 0 < B) (hk : 0 < k) (b : List Bool) (i : Nat)
    (hi : b.length ≤ i) : (directory B k b).total = rank b i := by
  obtain ⟨htot, -, -, -, -⟩ := Directory.valid_directory B k hk b
  unfold Directory.RunningTotalRight at htot
  rw [htot, sum_take_blockCounts B b _ (Nat.le_refl _)]
  simp only [rank, List.take_of_length_le hi,
    List.take_of_length_le (len_le_numBlocks_mul B b.length hB)]

/-- The two-level directory computes `rank`, for every position and both widths. -/
theorem rankTwoLevel_eq (B k : Nat) (hB : 0 < B) (hk : 0 < k) (b : List Bool) (i : Nat) :
    rankTwoLevel B k b i = rank b i := by
  unfold rankTwoLevel
  split
  · exact total_eq B k hB hk b i (by omega)
  · rename_i hi
    dsimp only
    have hblk : i / B < numBlocks B b.length := div_lt_ceil i _ B hB (by omega)
    rw [checkpoint B k hB hk b _ hblk, ← rank_add]
    congr 1
    have := Nat.div_mul_le_self i B
    omega

/-! ## `occ` through the same directory -/

/-- `occ` is `rank` over the bit vector "is this position `c`". -/
theorem occ_eq_rank_map (s : List Nat) (c i : Nat) : occ s c i = rank (s.map (· == c)) i := by
  simp only [occ, rank, ← List.map_take, List.filter_map, List.length_map]
  rfl

/-- The same identification on a slice. -/
private theorem pop_map_slice (s : List Nat) (c a m : Nat) :
    pop (((s.map (· == c)).drop a).take m) = (((s.drop a).take m).filter (· == c)).length := by
  simp only [pop, ← List.map_drop, ← List.map_take, List.filter_map, List.length_map]
  rfl

/-- Models `ByteIndex::occ`: no scan when the block's checkpoints agree; otherwise scan from the
nearer end of the block. -/
def occTwoLevel (B k : Nat) (s : List Nat) (c i : Nat) : Nat :=
  let d := directory B k (s.map (· == c))
  if s.length ≤ i then d.total
  else
    let blk := i / B
    let start := blk * B
    let stop := min (start + B) s.length
    let before := d.supers[blk / k]! + d.blocks[blk]!
    let after := if blk + 1 = d.blocks.length then d.total
      else d.supers[(blk + 1) / k]! + d.blocks[blk + 1]!
    if before = after then before
    else if i - start ≤ (stop - start) / 2 then
      before + (((s.drop start).take (i - start)).filter (· == c)).length
    else after - (((s.drop i).take (stop - i)).filter (· == c)).length

/-- The directory computes `occ`, through every branch. -/
theorem occTwoLevel_eq (B k : Nat) (hB : 0 < B) (hk : 0 < k) (s : List Nat) (c i : Nat) :
    occTwoLevel B k s c i = occ s c i := by
  rw [occ_eq_rank_map]
  set b := s.map (· == c) with hb
  have hlen : b.length = s.length := by simp [hb]
  unfold occTwoLevel
  rw [← hb]
  dsimp only
  split
  · exact total_eq B k hB hk b i (by omega)
  · rename_i hi
    have hnb : numBlocks B b.length = (directory B k b).blocks.length :=
      (Directory.valid_directory B k hk b).2.2.2.1.symm
    have hblk : i / B < numBlocks B b.length := div_lt_ceil i _ B hB (by omega)
    have hle := Nat.div_mul_le_self i B
    have hlt : i < i / B * B + B := Nat.lt_div_mul_add hB
    have hbefore := checkpoint B k hB hk b _ hblk
    -- The checkpoint on the block's far side is `rank` at the block's end.
    have hafter : (if i / B + 1 = (directory B k b).blocks.length then (directory B k b).total
        else (directory B k b).supers[(i / B + 1) / k]! + (directory B k b).blocks[i / B + 1]!)
        = rank b (min (i / B * B + B) s.length) := by
      split
      · rename_i hlast
        have hcover := len_le_numBlocks_mul B b.length hB
        rw [hnb, ← hlast, Nat.add_mul, Nat.one_mul] at hcover
        rw [total_eq B k hB hk b (min (i / B * B + B) s.length) (by omega)]
      · rename_i hnot
        have hnext : i / B + 1 < numBlocks B b.length := by omega
        have := mul_lt_of_lt_numBlocks B _ _ hnext
        rw [Nat.add_mul, Nat.one_mul] at this
        rw [checkpoint B k hB hk b _ hnext, Nat.add_mul, Nat.one_mul]
        congr 1; omega
    rw [hbefore, hafter]
    have hmono1 := rank_mono b (show i / B * B ≤ i by omega)
    have hmono2 := rank_mono b (show i ≤ min (i / B * B + B) s.length by omega)
    split
    · omega
    · split
      · rw [← pop_map_slice, ← hb, ← rank_add]
        congr 1; omega
      · rw [← pop_map_slice, ← hb]
        have := rank_add b i (min (i / B * B + B) s.length - i)
        rw [show i + (min (i / B * B + B) s.length - i) = min (i / B * B + B) s.length by omega]
          at this
        omega

end AlgoDesign.Strings
