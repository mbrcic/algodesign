/-
Copyright (c) 2026 Mario Brcic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Brcic
-/

module

public import AlgoDesign.Graphs.Workbench.Spec
public import AlgoDesign.Graphs.Scc.Reach

/-! # The design project's contract: deciding its pieces on one plan

Each piece of the contract asks something of every plan. On one plan (the tasks, the arrows and
the tasks done) and one candidate's answers, each piece is a claim about those answers alone, and
it decides, so `decide` judges small plans. They are the pieces the Python judge checks, one
function each (`workbench.py`): `EachOnceOn` is `is_each_once`, `ReadyNowOn` `is_ready_now`,
`LaterOnesOn` `is_later_ones`, `KnottedOn` `is_knotted`, `BlockedOnesOn` `is_blocked_ones`,
`WaitChain` `is_wait_chain`, and `ExplainsOn`, on the tasks asked, `is_explains`. Each `Ops`
piece is its plan piece on every well-formed plan (`Ops.readyNow_iff` and the rest). -/

@[expose] public section

namespace AlgoDesign.Graphs.Workbench

open Digraph Relation

/-! ## The words, decided -/

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) : Decidable (Unfinished g done v) := by
  unfold Unfinished; infer_instance

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) : Decidable (Ready g done v) :=
  decidable_of_iff (Unfinished g done v ∧ ∀ e ∈ g.arrows, e.2 = v → e.1 ∈ done) (by
    unfold Ready Digraph.Arrow
    exact and_congr_right fun _ =>
      ⟨fun h a ha => h (a, v) ha rfl, fun h e he hev => h e.1 (hev ▸ he)⟩)

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) : Decidable (InKnot g done v) :=
  decidable_of_iff (Unfinished g done v ∧
      ∃ e ∈ (pending g done).arrows, e.2 = v ∧ (pending g done).Reaches v e.1) (by
    unfold InKnot Digraph.Arrow
    exact and_congr_right fun _ =>
      ⟨fun ⟨e, he, hev, hr⟩ => ⟨e.1, hev ▸ he, hr⟩, fun ⟨w, hw, hr⟩ => ⟨(w, v), hw, rfl, hr⟩⟩)

/-- A task that reaches `v` along arrows is `v` or the tail of one of them. -/
theorem mem_tails_of_reaches {h : Digraph} {k v : ℕ} (hr : h.Reaches k v) :
    k ∈ v :: h.arrows.map Prod.fst := by
  rcases ReflTransGen.cases_head hr with rfl | ⟨b, hb, -⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨(k, b), hb, rfl⟩)

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) : Decidable (Later g done v) :=
  decidable_of_iff (Unfinished g done v ∧ ¬ Ready g done v ∧
      ∀ k ∈ v :: (pending g done).arrows.map Prod.fst,
        (pending g done).Reaches k v → ¬ InKnot g done k) (by
    unfold Later
    exact and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun h k hr => h k (mem_tails_of_reaches hr) hr, fun h k _ hr => h k hr⟩)

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) : Decidable (Blocked g done v) :=
  decidable_of_iff (Unfinished g done v ∧ ¬ InKnot g done v ∧
      ∃ k < g.n, InKnot g done k ∧ (pending g done).Reaches k v) (by
    unfold Blocked
    exact and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun ⟨k, _, hk, hr⟩ => ⟨k, hk, hr⟩, fun ⟨k, hk, hr⟩ => ⟨k, hk.1.1, hk, hr⟩⟩)

instance (g : Digraph) (done : Finset ℕ) (v : ℕ) (p : List ℕ) : Decidable (WaitChain g done v p) :=
  decidable_of_iff ((p.head?.any fun k => decide (InKnot g done k)) = true ∧
      p.getLast? = some v ∧ p.IsChain (pending g done).Arrow) (by
    unfold WaitChain
    refine and_congr_left fun _ => ?_
    cases p.head? <;> simp)

/-! ## The pieces on one plan -/

/-- **Each once**, on one plan: the four lists together hold every unfinished task once, and
nothing else. -/
def EachOnceOn (g : Digraph) (done : Finset ℕ) (ready later knot blocked : List ℕ) : Prop :=
  (∀ v, Unfinished g done v → (ready ++ later ++ knot ++ blocked).count v = 1) ∧
    ∀ v ∈ ready ++ later ++ knot ++ blocked, Unfinished g done v

/-- **Ready now**, on one plan: the list holds exactly the tasks ready now. -/
def ReadyNowOn (g : Digraph) (done : Finset ℕ) (ready : List ℕ) : Prop :=
  ∀ v, v ∈ ready ↔ Ready g done v

/-- **Later**, on one plan: the list holds exactly the tasks that will be able to start later. -/
def LaterOnesOn (g : Digraph) (done : Finset ℕ) (later : List ℕ) : Prop :=
  ∀ v, v ∈ later ↔ Later g done v

/-- **In a knot**, on one plan: the list holds exactly the tasks in a knot. -/
def KnottedOn (g : Digraph) (done : Finset ℕ) (knot : List ℕ) : Prop :=
  ∀ v, v ∈ knot ↔ InKnot g done v

/-- **Blocked**, on one plan: the list holds exactly the blocked tasks. -/
def BlockedOnesOn (g : Digraph) (done : Finset ℕ) (blocked : List ℕ) : Prop :=
  ∀ v, v ∈ blocked ↔ Blocked g done v

/-- **Why**, on one plan and the tasks asked: each blocked task asked about got a chain of real
waits from a knot, and every other task asked about got nothing. -/
def ExplainsOn (g : Digraph) (done : Finset ℕ) (answers : List (ℕ × Option (List ℕ))) : Prop :=
  ∀ a ∈ answers, (Blocked g done a.1 → ∃ p, a.2 = some p ∧ WaitChain g done a.1 p) ∧
    (¬ Blocked g done a.1 → a.2 = none)

/-- A list holds exactly the tasks of a property only tasks have, decided below `n`. -/
theorem mem_iff_bounded {n : ℕ} {P : ℕ → Prop} (hP : ∀ v, P v → v < n) (l : List ℕ) :
    (∀ v, v ∈ l ↔ P v) ↔ (∀ v ∈ l, P v) ∧ ∀ v < n, P v → v ∈ l :=
  ⟨fun h => ⟨fun v hv => (h v).1 hv, fun v _ hv => (h v).2 hv⟩,
    fun ⟨h1, h2⟩ v => ⟨h1 v, fun hv => h2 v (hP v hv) hv⟩⟩

instance (g : Digraph) (done : Finset ℕ) (ready later knot blocked : List ℕ) :
    Decidable (EachOnceOn g done ready later knot blocked) :=
  decidable_of_iff ((∀ v < g.n, Unfinished g done v →
      (ready ++ later ++ knot ++ blocked).count v = 1) ∧
      ∀ v ∈ ready ++ later ++ knot ++ blocked, Unfinished g done v) (by
    unfold EachOnceOn
    exact and_congr_left fun _ => ⟨fun h v hv => h v hv.1 hv, fun h v _ hv => h v hv⟩)

instance (g : Digraph) (done : Finset ℕ) (ready : List ℕ) : Decidable (ReadyNowOn g done ready) :=
  decidable_of_iff _ (mem_iff_bounded (fun _ h => h.1.1) ready).symm

instance (g : Digraph) (done : Finset ℕ) (later : List ℕ) : Decidable (LaterOnesOn g done later) :=
  decidable_of_iff _ (mem_iff_bounded (fun _ h => h.1.1) later).symm

instance (g : Digraph) (done : Finset ℕ) (knot : List ℕ) : Decidable (KnottedOn g done knot) :=
  decidable_of_iff _ (mem_iff_bounded (fun _ h => h.1.1) knot).symm

instance (g : Digraph) (done : Finset ℕ) (blocked : List ℕ) :
    Decidable (BlockedOnesOn g done blocked) :=
  decidable_of_iff _ (mem_iff_bounded (fun _ h => h.1.1) blocked).symm

instance (g : Digraph) (done : Finset ℕ) (answers : List (ℕ × Option (List ℕ))) :
    Decidable (ExplainsOn g done answers) :=
  decidable_of_iff (∀ a ∈ answers, (Blocked g done a.1 →
      (a.2.any fun p => decide (WaitChain g done a.1 p)) = true) ∧
      (¬ Blocked g done a.1 → a.2 = none)) (by
    unfold ExplainsOn
    refine forall₂_congr fun a _ => and_congr_left fun _ => imp_congr_right fun _ => ?_
    cases a.2 <;> simp)

/-! ## Each `Ops` piece is its plan piece on every plan -/

variable {S : Type} (o : Ops S)

theorem Ops.eachOnce_iff : o.EachOnce ↔ ∀ g done, g.WellFormed →
    EachOnceOn g done (o.ready (o.build g done)) (o.later (o.build g done))
      (o.knot (o.build g done)) (o.blocked (o.build g done)) := Iff.rfl

theorem Ops.readyNow_iff : o.ReadyNow ↔ ∀ g done, g.WellFormed →
    ReadyNowOn g done (o.ready (o.build g done)) := Iff.rfl

theorem Ops.laterOnes_iff : o.LaterOnes ↔ ∀ g done, g.WellFormed →
    LaterOnesOn g done (o.later (o.build g done)) := Iff.rfl

theorem Ops.knotted_iff : o.Knotted ↔ ∀ g done, g.WellFormed →
    KnottedOn g done (o.knot (o.build g done)) := Iff.rfl

theorem Ops.blockedOnes_iff : o.BlockedOnes ↔ ∀ g done, g.WellFormed →
    BlockedOnesOn g done (o.blocked (o.build g done)) := Iff.rfl

/-- `Ops.Explains` is `ExplainsOn` with every task asked. -/
theorem Ops.explains_iff : o.Explains ↔ ∀ g done, g.WellFormed → ∀ v,
    ExplainsOn g done [(v, o.why (o.build g done) v)] := by
  unfold Ops.Explains ExplainsOn
  simp

end AlgoDesign.Graphs.Workbench
