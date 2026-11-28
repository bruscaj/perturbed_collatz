import GeneralSolution
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  if env.header.moduleNames.contains `GeneralChallenge then
    throwError "Designated challenge holes must never enter implementation imports"
  let targets : Array (Name × Name) := #[
    (`ExternalO3GeneralChallenge.blocksWellDefined, `ExternalO3GeneralDraft.BlocksWellDefined),
    (`ExternalO3GeneralChallenge.windowValidity, `ExternalO3GeneralDraft.WindowValidity),
    (`ExternalO3GeneralChallenge.windowTransport, `ExternalO3GeneralDraft.WindowTransport),
    (`ExternalO3GeneralChallenge.correctionRestriction, `ExternalO3GeneralDraft.CorrectionRestriction),
    (`ExternalO3GeneralChallenge.fixedPointAndZero, `ExternalO3GeneralDraft.FixedPointAndZero),
    (`ExternalO3GeneralChallenge.refinedCylinderClasses, `ExternalO3GeneralDraft.RefinedCylinderClasses),
    (`ExternalO3GeneralChallenge.refinedCylinderDensities, `ExternalO3GeneralDraft.RefinedCylinderDensities),
    (`ExternalO3GeneralChallenge.refinedLabelCell, `ExternalO3GeneralDraft.RefinedLabelCell),
    (`ExternalO3GeneralChallenge.refinedWeightLaw, `ExternalO3GeneralDraft.RefinedWeightLaw),
    (`ExternalO3GeneralChallenge.refinementProjectionLaw, `ExternalO3GeneralDraft.RefinementProjectionLaw),
    (`ExternalO3GeneralChallenge.coarseMarginalLaw, `ExternalO3GeneralDraft.CoarseMarginalLaw),
    (`ExternalO3GeneralChallenge.weightLaw, `ExternalO3GeneralDraft.WeightLaw),
    (`ExternalO3GeneralChallenge.coordinateLaw, `ExternalO3GeneralDraft.CoordinateLaw),
    (`ExternalO3GeneralChallenge.labelRealizable, `ExternalO3GeneralDraft.LabelRealizable),
    (`ExternalO3GeneralChallenge.literalGainIdentity, `ExternalO3GeneralDraft.LiteralGainIdentity),
    (`ExternalO3GeneralChallenge.cellStabilization, `ExternalO3GeneralDraft.CellStabilization),
    (`ExternalO3GeneralChallenge.selectedMassSummable, `ExternalO3GeneralDraft.SelectedMassSummable),
    (`ExternalO3GeneralChallenge.densityExists, `ExternalO3GeneralDraft.DensityExists),
    (`ExternalO3GeneralChallenge.densityEqualsSymbolic, `ExternalO3GeneralDraft.DensityEqualsSymbolic),
    (`ExternalO3GeneralChallenge.densityUnique, `ExternalO3GeneralDraft.DensityUnique),
    (`ExternalO3GeneralChallenge.sourceDensityEquivalence, `ExternalO3GeneralDraft.SourceDensityEquivalence),
    (`ExternalO3GeneralChallenge.depthOneCompatibility, `ExternalO3GeneralDraft.DepthOneCompatibility)]
  for (proof, expected) in targets do
    let info ← getConstInfo proof
    let equal ← liftTermElabM do Meta.isDefEq info.type (mkConst expected)
    unless equal do throwError "Type mismatch for frozen target {expected}: {proof}"
    let expectedBody := match (← getConstInfo expected) with
      | .defnInfo d => (repr d.value).pretty
      | _ => "NOT A PROPOSITION DEFINITION"
    liftIO <| IO.println ("GENERAL_TARGET " ++ (Json.mkObj [
      ("declaration", toJson proof.toString), ("expected", toJson expected.toString),
      ("raw_type", toJson (repr info.type).pretty),
      ("raw_expected_proposition", toJson expectedBody)]).compress)
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if #[`Definitions, `ExpectedTypes, `Arithmetic, `PopulationWeights, `Progressions,
          `Cylinders, `ExitCylinders, `Gains, `CountablePartition, `PartitionGeneral,
          `DensityBounds, `SourceDensity, `GeneralDefinitions, `GeneralExpectedTypes,
          `GeneralArithmetic, `GeneralCompatibility, `GeneralPreimage, `GeneralStrideWords,
          `GeneralBlockWords, `GeneralCylinderDensity, `GeneralRefinementLabels,
          `GeneralWeights, `GeneralMarginal, `GeneralProjection, `GeneralGains,
          `GeneralSourceDensity, `GeneralDensity, `GeneralSolution].contains modName then
        if let .axiomInfo _ := info then
          throwError "Own module {modName} contains an unproved axiom {name}"
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for a in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains a do
              throwError "Forbidden axiom {a} in {name}"
          let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
          liftIO <| IO.println ("GENERAL_SUPPORT " ++ (Json.mkObj [
            ("declaration", toJson name.toString), ("module", toJson modName.toString),
            ("statement", toJson statement), ("raw_type", toJson (repr info.type).pretty),
            ("axioms", toJson (axioms.map Name.toString))]).compress)
          total := total + 1
  if total == 0 then throwError "Empty general-depth closure audit"
  logInfo m!"Audited {total} own and reused theorem closures. All22 frozen density/model targets; no rate theorem."
