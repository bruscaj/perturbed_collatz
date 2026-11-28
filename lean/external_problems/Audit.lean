import Lean
import Solution

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let selected : Array Name := #[
    ``ExternalPrefixChallenge.floorDepthEquivalence,
    ``ExternalPrefixChallenge.depthInvolution,
    ``ExternalPrefixChallenge.closingFloorEquivalence,
    ``ExternalPrefixChallenge.floorRaiseSoundness,
    ``ExternalPrefixChallenge.endpointInverses]
  let mut selectedCount : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == `Solution then
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for axiomName in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
              throwError "{name} has forbidden axiom {axiomName}"
          if selected.contains name then
            let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
            let row := Json.mkObj [
              ("declaration", toJson name.toString),
              ("statement", toJson statement),
              ("raw_type", toJson (repr info.type).pretty),
              ("axioms", toJson (axioms.map Name.toString))]
            liftIO <| IO.println ("EXTERNAL_THEOREM " ++ row.compress)
            selectedCount := selectedCount + 1
          else
            let row := Json.mkObj [
              ("declaration", toJson name.toString),
              ("axioms", toJson (axioms.map Name.toString))]
            liftIO <| IO.println ("EXTERNAL_HELPER " ++ row.compress)
          checked := checked + 1
  unless selectedCount == 5 do throwError "Missing selected supporting theorem"
  logInfo m!"All {checked} module theorem closures checked, including helpers; no headline theorem audited."
