import AlgoDesign
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Run from `lean/` after `lake build`:

    lake env lean CheckAxioms.lean

Every declaration defined in an `AlgoDesign` module uses only Lean's standard logical axioms
(`propext`, `Classical.choice`, `Quot.sound`), transitive proof dependencies included. This
rejects admissions (`sorry` and `admit` elaborate to the axiom `sorryAx`), custom axioms and
native evaluation (`Lean.ofReduceBool`). -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless (`AlgoDesign).isPrefixOf mod do continue
    count := count + 1
    let axioms ← liftCoreM (Lean.collectAxioms name)
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "{name} (in {mod}) depends on forbidden axiom {axiomName}"
  if count == 0 then
    throwError "No AlgoDesign declarations found; check the umbrella import"
  logInfo m!"Checked {count} AlgoDesign declarations: standard axioms only"
