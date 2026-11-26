import Lean
import All

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let spaces := [`SevenStepSprint]
  let mut checked := 0
  for space in spaces do
    let mut inSpace := 0
    for (name, _) in env.constants.toList do
      if space.isPrefixOf name && getOriginalConstKind? env name == some .thm then
        for axiomName in (← collectAxioms name) do
          unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
            throwError "{name} depends on an unexpected axiom {axiomName}"
        inSpace := inSpace + 1
    if inSpace == 0 then throwError "No exported theorems in {space}"
    checked := checked + inSpace
  logInfo m!"Axiom audit passed for {checked} exported theorems."
