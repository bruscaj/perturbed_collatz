import Lean
import Collatz

open Lean Elab Command

-- Check all public theorems in the project namespace, including transitive dependencies.
run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if `Collatz |>.isPrefixOf name then
      if getOriginalConstKind? env name == some .thm then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
            throwError "{name} depends on an unexpected axiom: {axiomName}"
        checked := checked + 1
  if checked == 0 then throwError "No project theorems were checked"
  logInfo m!"Axiom audit passed for {checked} project theorems."
