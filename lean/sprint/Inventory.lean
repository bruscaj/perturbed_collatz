import Lean
import All

open Lean Elab Command

-- These are the named public source theorems; the separate Audit.lean also
-- checks every theorem constant in the project namespaces transitively.
run_cmd do
  let selected : List Name := [
    ``SevenStepSprint.predecessor_positive,
    ``SevenStepSprint.predecessor_replays,
    ``SevenStepSprint.predecessor_bound,
    ``SevenStepSprint.inverse_word_bound,
    ``SevenStepSprint.packet_guard_and_image]
  for name in selected do
    let info ← getConstInfo name
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
        throwError "{name} depends on an unexpected axiom: {axiomName}"
    let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
    let row := Json.mkObj [("declaration", toJson name.toString),
      ("statement", toJson statement), ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println ("RELEASE_THEOREM " ++ row.compress)
  if selected.isEmpty then throwError "No theorem declarations inventoried"

  -- Module identity includes private and generated theorem declarations.
  -- Checking theorem closures avoids compiler-only auxiliary implementation
  -- constants while rejecting any such axiom if a theorem depends on it.
  let env ← getEnv
  let modules : List Name := [`RootInverseHeight, `RootPacket]
  let mut theorems := 0
  for modName in modules do
    let mut inModule := 0
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if getOriginalConstKind? env name == some .thm then
            for axiomName in (← collectAxioms name) do
              unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
                throwError "{name} depends on an unexpected axiom {axiomName}"
            inModule := inModule + 1
    if inModule == 0 then throwError "No theorem declarations were audited in module {modName}"
    theorems := theorems + inModule
  let summary := Json.mkObj [
    ("theorem_constants_including_private_and_generated", toJson theorems),
    ("modules", toJson (modules.map Name.toString))]
  liftIO <| IO.println ("RELEASE_AUDIT " ++ summary.compress)
