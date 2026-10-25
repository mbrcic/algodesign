/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Blocks.Spec

/-! # Bridges, cut vertices and blocks: deciding the definitions

The meaning by deletion, links and loops, the walk's first invariant piece and its helpers decide
on a concrete graph, so `decide` checks small cases. Whether two links share a block decides
through a search over paths (`Blocks/Cycles.lean`), and so do the second piece and `Valid`
(`Blocks/Walk.lean`). -/

@[expose] public section

namespace AlgoDesign.Graphs.Blocks

instance (g : Graph) (e : ℕ) : Decidable (IsBridge g e) := by unfold IsBridge; infer_instance
instance (g : Graph) (v : ℕ) : Decidable (IsCutVertex g v) := by unfold IsCutVertex; infer_instance
instance (g : Graph) (w u v : ℕ) : Decidable (Separates g w u v) := by
  unfold Separates; infer_instance

instance (g : Graph) (i a b : ℕ) : Decidable (Joins g i a b) := by unfold Joins; infer_instance

instance (g : Graph) (i : ℕ) : Decidable (NonLoop g i) := by unfold NonLoop; infer_instance

instance (g : Graph) (v : ℕ) : Decidable (IsolatedVertex g v) := by
  unfold IsolatedVertex; infer_instance

namespace Walk

variable {g : Graph}

instance (w : Walk) (f : ℕ) : Decidable (Taken (g := g) w f) := by
  unfold Taken; infer_instance

end Walk

instance (w : Walk) : Decidable (ClimbBackIsEarliest w) := by
  unfold ClimbBackIsEarliest; infer_instance

end AlgoDesign.Graphs.Blocks
