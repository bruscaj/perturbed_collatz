import BridgeSolution
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for modName in env.header.moduleNames do
    if #[`Challenge, `BridgeChallenge, `GeneralChallenge, `RateChallenge,
        `RateOptionalChallenge].contains modName then
      throwError "Designated challenge holes must never enter implementation imports"
  let targets : Array (Name × Name) := #[
    (`ExternalFiniteBridgeChallenge.finiteWordPrefixEncoding, `ExternalFiniteBridgeDraft.FiniteWordPrefixEncoding),
    (`ExternalFiniteBridgeChallenge.abstractPrefixCompatibility, `ExternalFiniteBridgeDraft.AbstractPrefixCompatibility),
    (`ExternalFiniteBridgeChallenge.defectBounds, `ExternalFiniteBridgeDraft.DefectBounds),
    (`ExternalFiniteBridgeChallenge.nonintegralEndpoint, `ExternalFiniteBridgeDraft.NonintegralEndpoint),
    (`ExternalFiniteBridgeChallenge.strictRungCaps, `ExternalFiniteBridgeDraft.StrictRungCaps),
    (`ExternalFiniteBridgeChallenge.unitFloorIncrements, `ExternalFiniteBridgeDraft.UnitFloorIncrements),
    (`ExternalFiniteBridgeChallenge.floorIncrementAlphabet, `ExternalFiniteBridgeDraft.FloorIncrementAlphabet),
    (`ExternalFiniteBridgeChallenge.sourceSlopeFacts, `ExternalFiniteBridgeDraft.SourceSlopeFacts),
    (`ExternalFiniteBridgeChallenge.sourceSlopeNonintegral, `ExternalFiniteBridgeDraft.SourceSlopeNonintegral),
    (`ExternalFiniteBridgeChallenge.sourceRungsUnbounded, `ExternalFiniteBridgeDraft.SourceRungsUnbounded),
    (`ExternalFiniteBridgeChallenge.literalClosingDepth, `ExternalFiniteBridgeDraft.LiteralClosingDepth),
    (`ExternalFiniteBridgeChallenge.rewardEndpointInvariant, `ExternalFiniteBridgeDraft.RewardEndpointInvariant),
    (`ExternalFiniteBridgeChallenge.rewardRealPower, `ExternalFiniteBridgeDraft.RewardRealPower),
    (`ExternalFiniteBridgeChallenge.sourceDepthReward, `ExternalFiniteBridgeDraft.SourceDepthReward),
    (`ExternalFiniteBridgeChallenge.referenceAtRungs, `ExternalFiniteBridgeDraft.ReferenceAtRungs),
    (`ExternalFiniteBridgeChallenge.sourceLastLetterLowerable, `ExternalFiniteBridgeDraft.SourceLastLetterLowerable),
    (`ExternalFiniteBridgeChallenge.lowerRaiseTransport, `ExternalFiniteBridgeDraft.LowerRaiseTransport),
    (`ExternalFiniteBridgeChallenge.sourceFloorBijection, `ExternalFiniteBridgeDraft.SourceFloorBijection),
    (`ExternalFiniteBridgeChallenge.finitePopulations, `ExternalFiniteBridgeDraft.FinitePopulations),
    (`ExternalFiniteBridgeChallenge.sourceDepthBijection, `ExternalFiniteBridgeDraft.SourceDepthBijection),
    (`ExternalFiniteBridgeChallenge.thresholdCountPreservation, `ExternalFiniteBridgeDraft.ThresholdCountPreservation),
    (`ExternalFiniteBridgeChallenge.phaseZeroExtremizer, `ExternalFiniteBridgeDraft.PhaseZeroExtremizer),
    (`ExternalFiniteBridgeChallenge.uniqueExtremizer, `ExternalFiniteBridgeDraft.UniqueExtremizer),
    (`ExternalFiniteBridgeChallenge.zeroLengthConvention, `ExternalFiniteBridgeDraft.ZeroLengthConvention),
    (`ExternalFiniteBridgeChallenge.lengthOneBoundary, `ExternalFiniteBridgeDraft.LengthOneBoundary)]
  for (proof, expected) in targets do
    let info ← getConstInfo proof
    let equal ← liftTermElabM do Meta.isDefEq info.type (mkConst expected)
    unless equal do throwError "Type mismatch for frozen target {expected}: {proof}"
    let expectedBody := match (← getConstInfo expected) with
      | .defnInfo d => (repr d.value).pretty
      | _ => "NOT A PROPOSITION DEFINITION"
    liftIO <| IO.println ("BRIDGE_TARGET " ++ (Json.mkObj [
      ("declaration", toJson proof.toString), ("expected", toJson expected.toString),
      ("raw_type", toJson (repr info.type).pretty),
      ("raw_expected_proposition", toJson expectedBody)]).compress)
  let mut total : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if #[`Definitions, `ExpectedTypes, `Arithmetic, `PopulationWeights, `DepthOneSeries, `LogRatioIrrational, `PositiveCeilReturns, `PrefixDefinitions, `RungDefinitions, `RungTransfer, `SyracuseSlope, `BridgeDefinitions, `BridgeExpectedTypes, `BridgeArithmetic, `BridgeEncoding, `BridgeRungs, `BridgeRewards, `BridgeTransport, `BridgeFinite, `BridgeExtremal, `BridgeBoundary, `BridgeSolution].contains modName then
        if let .axiomInfo _ := info then
          throwError "Own custom axiom {name} is forbidden"
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for a in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains a do
              throwError "Forbidden axiom {a} in {name}"
          let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
          liftIO <| IO.println ("BRIDGE_SUPPORT " ++ (Json.mkObj [
            ("declaration", toJson name.toString), ("module", toJson modName.toString),
            ("statement", toJson statement), ("raw_type", toJson (repr info.type).pretty),
            ("axioms", toJson (axioms.map Name.toString))]).compress)
          total := total + 1
  if total == 0 then throwError "Empty finite bridge closure audit"
  logInfo m!"Audited {total} own and reused theorem closures. All25 frozen finite bridge targets; independent gates pending."
