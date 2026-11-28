import GeneralSolution
import OptimizationSolution
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if #[`Challenge, `BridgeChallenge, `GeneralChallenge, `RateChallenge,
        `RateOptionalChallenge, `OptimizationChallenge, `OptimizationOptionalChallenge].contains modName then
      throwError "Designated challenge holes must never enter implementation imports"
  let targets : Array (Name × Name) := #[
    (`ExternalO3OptimizationChallenge.genericStrictCycleCriterion, `ExternalO3OptimizationDraft.GenericStrictCycleCriterion),
    (`ExternalO3OptimizationChallenge.vertexEncodingAndExtension, `ExternalO3OptimizationDraft.VertexEncodingAndExtension),
    (`ExternalO3OptimizationChallenge.edgeEncodingAndWeights, `ExternalO3OptimizationDraft.EdgeEncodingAndWeights),
    (`ExternalO3OptimizationChallenge.naturalCycleSigns, `ExternalO3OptimizationDraft.NaturalCycleSigns),
    (`ExternalO3OptimizationChallenge.commonDyadicDenominator, `ExternalO3OptimizationDraft.CommonDyadicDenominator),
    (`ExternalO3OptimizationChallenge.numeratorMinimumWellPosed, `ExternalO3OptimizationDraft.NumeratorMinimumWellPosed),
    (`ExternalO3OptimizationChallenge.genericElementaryReduction, `ExternalO3OptimizationDraft.GenericElementaryReduction),
    (`ExternalO3OptimizationChallenge.genericDeletionOptimum, `ExternalO3OptimizationDraft.GenericDeletionOptimum),
    (`ExternalO3OptimizationChallenge.finiteOptimizationExact, `ExternalO3OptimizationDraft.FiniteOptimizationExact),
    (`ExternalO3OptimizationChallenge.truncationMassIdentity, `ExternalO3OptimizationDraft.TruncationMassIdentity),
    (`ExternalO3OptimizationChallenge.discardedMassBound, `ExternalO3OptimizationDraft.DiscardedMassBound),
    (`ExternalO3OptimizationChallenge.literalInfimumSandwich, `ExternalO3OptimizationDraft.LiteralInfimumSandwich),
    (`ExternalO3OptimizationChallenge.diagonalConvergence, `ExternalO3OptimizationDraft.DiagonalConvergence),
    (`ExternalO3OptimizationChallenge.computableExactOptimizer, `ExternalO3OptimizationDraft.ComputableExactOptimizer),
    (`ExternalO3OptimizationChallenge.computableDyadicApproximation, `ExternalO3OptimizationDraft.ComputableDyadicApproximation)]
  for (proof, expected) in targets do
    let info ← getConstInfo proof
    let equal ← liftTermElabM do Meta.isDefEq info.type (mkConst expected)
    unless equal do throwError "Type mismatch for frozen target {expected}: {proof}"
    let expectedBody := match (← getConstInfo expected) with
      | .defnInfo d => (repr d.value).pretty
      | _ => "NOT A PROPOSITION DEFINITION"
    liftIO <| IO.println ("OPTIMIZATION_TARGET " ++ (Json.mkObj [
      ("declaration", toJson proof.toString), ("expected", toJson expected.toString),
      ("raw_type", toJson (repr info.type).pretty),
      ("raw_expected_proposition", toJson expectedBody)]).compress)
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if #[`Definitions, `ExpectedTypes, `Arithmetic, `PopulationWeights, `Progressions, `Cylinders, `ExitCylinders, `Gains, `CountablePartition, `PartitionGeneral, `DensityBounds, `SourceDensity, `GeneralDefinitions, `GeneralExpectedTypes, `GeneralArithmetic, `GeneralCompatibility, `GeneralPreimage, `GeneralStrideWords, `GeneralBlockWords, `GeneralCylinderDensity, `GeneralRefinementLabels, `GeneralWeights, `GeneralMarginal, `GeneralProjection, `GeneralGains, `GeneralSourceDensity, `GeneralDensity, `GeneralSolution, `RateDefinitions, `RateExpectedTypes, `RateInfimum, `OptimizationDefinitions, `OptimizationExpectedTypes, `OptimizationCycles, `OptimizationEncoding, `OptimizationArithmetic, `OptimizationPaths, `OptimizationDeletion, `OptimizationMass, `OptimizationDensity, `OptimizationAlgorithmTypes, `OptimizationCode, `OptimizationAlgorithm, `OptimizationVertexCode, `OptimizationEdgeCode, `OptimizationCycleCode, `OptimizationAccuracy, `OptimizationJoin, `OptimizationSolution].contains modName then
        if let .axiomInfo _ := info then
          throwError "Own custom axiom {name} is forbidden"
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for a in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains a do
              throwError "Forbidden axiom {a} in {name}"
          let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
          liftIO <| IO.println ("OPTIMIZATION_SUPPORT " ++ (Json.mkObj [
            ("declaration", toJson name.toString), ("module", toJson modName.toString),
            ("statement", toJson statement), ("raw_type", toJson (repr info.type).pretty),
            ("axioms", toJson (axioms.map Name.toString))]).compress)
          total := total + 1
  if total == 0 then throwError "Empty optimization closure audit"
  logInfo m!"Audited {total} own and reused theorem closures. All15 frozen optimization targets; independent assurance gates pending."
