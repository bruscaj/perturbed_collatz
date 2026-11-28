import GeneralSolution
import RateSolution
import Lean

/-! Public adapter: exhaustive own theorem closure inventory plus exact frozen target types. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for forbidden in #[`RateChallenge, `RateOptionalChallenge, `GeneralChallenge] do
    if env.header.moduleNames.contains forbidden then
      throwError "Designated challenge holes must never enter implementation imports: {forbidden}"
  let targets : Array (Name × Name) := #[
    (`ExternalO3RateChallenge.infimumWellPosed, `ExternalO3RateDraft.InfimumWellPosed),
    (`ExternalO3RateChallenge.markerSelectorLaw, `ExternalO3RateDraft.MarkerSelectorLaw),
    (`ExternalO3RateChallenge.markerUpperBound, `ExternalO3RateDraft.MarkerUpperBound),
    (`ExternalO3RateChallenge.historyWeightLaw, `ExternalO3RateDraft.HistoryWeightLaw),
    (`ExternalO3RateChallenge.cyclicNormalization, `ExternalO3RateDraft.CyclicNormalization),
    (`ExternalO3RateChallenge.cyclicTelescoping, `ExternalO3RateDraft.CyclicTelescoping),
    (`ExternalO3RateChallenge.cyclicForcing, `ExternalO3RateDraft.CyclicForcing),
    (`ExternalO3RateChallenge.cyclicDensityLowerBound, `ExternalO3RateDraft.CyclicDensityLowerBound),
    (`ExternalO3RateChallenge.positiveCycleMassLowerBound, `ExternalO3RateDraft.PositiveCycleMassLowerBound),
    (`ExternalO3RateChallenge.explicitInverseDepthRate, `ExternalO3RateDraft.ExplicitInverseDepthRate),
    (`ExternalO3RateChallenge.infimumTendsToZero, `ExternalO3RateDraft.InfimumTendsToZero)]
  for (proof, expected) in targets do
    let info ← getConstInfo proof
    let equal ← liftTermElabM do Meta.isDefEq info.type (mkConst expected)
    unless equal do throwError "Type mismatch for frozen target {expected}: {proof}"
    let expectedBody := match (← getConstInfo expected) with
      | .defnInfo d => (repr d.value).pretty
      | _ => "NOT A PROPOSITION DEFINITION"
    liftIO <| IO.println ("RATE_TARGET " ++ (Json.mkObj [
      ("declaration", toJson proof.toString), ("expected", toJson expected.toString),
      ("raw_type", toJson (repr info.type).pretty),
      ("raw_expected_proposition", toJson expectedBody)]).compress)
  let owned : Array Name := #[`Definitions, `ExpectedTypes, `Arithmetic, `PopulationWeights, `Progressions, `Cylinders, `ExitCylinders, `Gains, `CountablePartition, `PartitionGeneral, `DensityBounds, `SourceDensity, `GeneralDefinitions, `GeneralExpectedTypes, `GeneralArithmetic, `GeneralCompatibility, `GeneralPreimage, `GeneralStrideWords, `GeneralBlockWords, `GeneralCylinderDensity, `GeneralRefinementLabels, `GeneralWeights, `GeneralMarginal, `GeneralProjection, `GeneralGains, `GeneralSourceDensity, `GeneralDensity, `GeneralSolution, `RateDefinitions, `RateExpectedTypes, `RateInfimum, `RateMoments, `RateProductMoments, `RateSymmetry, `RateCycles, `RateNormalization, `RateLower, `RateMarker, `RateMarkerUpper, `RateCantelli, `RateBounds, `RateMaxMass, `RateMarkerEvents, `RateMain, `RateSolution]
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if owned.contains modName then
        if let .axiomInfo _ := info then
          throwError "Own module {modName} contains an unproved axiom {name}"
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for a in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains a do
              throwError "Forbidden axiom {a} in {name}"
          let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
          liftIO <| IO.println ("RATE_SUPPORT " ++ (Json.mkObj [
            ("declaration", toJson name.toString), ("module", toJson modName.toString),
            ("statement", toJson statement), ("raw_type", toJson (repr info.type).pretty),
            ("axioms", toJson (axioms.map Name.toString))]).compress)
          total := total + 1
  if total == 0 then throwError "Empty required-rate closure audit"
  logInfo m!"Audited {total} own and reused theorem closures; all11 required rate targets; optional liminf excluded."
