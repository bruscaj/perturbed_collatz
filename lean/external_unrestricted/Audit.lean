import BridgeSolution
import UnrestrictedSolution
import Lean

/-! Public audit adapter. Trusted target and owned-module lists are explicit;
this is not a copy of a private audit accepted as mathematical evidence. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if m.toString.endsWith "Challenge" then throwError "Challenge module imported: {m}"
  let targets : Array (Name × Name) := #[
    (`ExternalM4UnrestrictedChallenge.slopeBounds, `ExternalM4UnrestrictedDraft.SlopeBounds),
    (`ExternalM4UnrestrictedChallenge.tripleRotationHighLow, `ExternalM4UnrestrictedDraft.TripleRotationHighLow),
    (`ExternalM4UnrestrictedChallenge.highPhaseCountLower, `ExternalM4UnrestrictedDraft.HighPhaseCountLower),
    (`ExternalM4UnrestrictedChallenge.largeDefectsUnbounded, `ExternalM4UnrestrictedDraft.LargeDefectsUnbounded),
    (`ExternalM4UnrestrictedChallenge.canonicalPrefixLaw, `ExternalM4UnrestrictedDraft.CanonicalPrefixLaw),
    (`ExternalM4UnrestrictedChallenge.canonicalAllLengthWord, `ExternalM4UnrestrictedDraft.CanonicalAllLengthWord),
    (`ExternalM4UnrestrictedChallenge.canonicalAlphabetAndSites, `ExternalM4UnrestrictedDraft.CanonicalAlphabetAndSites),
    (`ExternalM4UnrestrictedChallenge.manyDisjointCanonicalSites, `ExternalM4UnrestrictedDraft.ManyDisjointCanonicalSites),
    (`ExternalM4UnrestrictedChallenge.swapPrefixLaw, `ExternalM4UnrestrictedDraft.SwapPrefixLaw),
    (`ExternalM4UnrestrictedChallenge.swapPreservesSource, `ExternalM4UnrestrictedDraft.SwapPreservesSource),
    (`ExternalM4UnrestrictedChallenge.swapFamilyInjective, `ExternalM4UnrestrictedDraft.SwapFamilyInjective),
    (`ExternalM4UnrestrictedChallenge.swapCubeCard, `ExternalM4UnrestrictedDraft.SwapCubeCard),
    (`ExternalM4UnrestrictedChallenge.swapRewardIdentity, `ExternalM4UnrestrictedDraft.SwapRewardIdentity),
    (`ExternalM4UnrestrictedChallenge.canonicalRewardBudget, `ExternalM4UnrestrictedDraft.CanonicalRewardBudget),
    (`ExternalM4UnrestrictedChallenge.canonicalSwapLossBound, `ExternalM4UnrestrictedDraft.CanonicalSwapLossBound),
    (`ExternalM4UnrestrictedChallenge.largeDefectWitnessInjection, `ExternalM4UnrestrictedDraft.LargeDefectWitnessInjection),
    (`ExternalM4UnrestrictedChallenge.exponentialCountLower, `ExternalM4UnrestrictedDraft.ExponentialCountLower),
    (`ExternalM4UnrestrictedChallenge.rungCountOne, `ExternalM4UnrestrictedDraft.RungCountOne),
    (`ExternalM4UnrestrictedChallenge.allLengthCountBounds, `ExternalM4UnrestrictedDraft.AllLengthCountBounds),
    (`ExternalM4UnrestrictedChallenge.normalizedLogBounds, `ExternalM4UnrestrictedDraft.NormalizedLogBounds),
    (`ExternalM4UnrestrictedChallenge.normalizedLogLiminf, `ExternalM4UnrestrictedDraft.NormalizedLogLiminf),
    (`ExternalM4UnrestrictedChallenge.normalizedLogLimsup, `ExternalM4UnrestrictedDraft.NormalizedLogLimsup),
    (`ExternalM4UnrestrictedChallenge.noAllLengthLimit, `ExternalM4UnrestrictedDraft.NoAllLengthLimit)]
  for (proof, expected) in targets do
    let info ← getConstInfo proof
    let equal ← liftTermElabM do Meta.isDefEq info.type (mkConst expected)
    unless equal do throwError "Frozen type mismatch: {proof}"
    let raw := match (← getConstInfo expected) with
      | .defnInfo d => (repr d.value).pretty
      | _ => "NOT A DEFINITION"
    liftIO <| IO.println ("UNRESTRICTED_TARGET " ++ (Json.mkObj [
      ("declaration",toJson proof.toString), ("expected",toJson expected.toString),
      ("raw_type",toJson (repr info.type).pretty), ("raw_expected_proposition",toJson raw)]).compress)
  let models : Array Name := #[
    `ExternalM4UnrestrictedDraft.beta,
    `ExternalM4UnrestrictedDraft.canonicalPrefix,
    `ExternalM4UnrestrictedDraft.canonicalWord,
    `ExternalM4UnrestrictedDraft.count,
    `ExternalM4UnrestrictedDraft.highPhaseCount,
    `ExternalM4UnrestrictedDraft.TwentyOneSite,
    `ExternalM4UnrestrictedDraft.DisjointSites,
    `ExternalM4UnrestrictedDraft.AdmissibleSites,
    `ExternalM4UnrestrictedDraft.applySwaps,
    `ExternalM4UnrestrictedDraft.SwapCube,
    `ExternalM4UnrestrictedDraft.swapFamily,
    `ExternalM4UnrestrictedDraft.swapLoss,
    `ExternalM4UnrestrictedDraft.normalizedLogCount]
  for name in models do
    let info ← getConstInfo name
    let raw := match info with | .defnInfo d => (repr d.value).pretty | _ => "NOT A DEFINITION"
    liftIO <| IO.println ("UNRESTRICTED_MODEL " ++ (Json.mkObj [
      ("declaration",toJson name.toString), ("raw_type",toJson (repr info.type).pretty),
      ("raw_body",toJson raw)]).compress)
  let owned : Array Name := #[
    `Definitions,
    `ExpectedTypes,
    `Arithmetic,
    `PopulationWeights,
    `DepthOneSeries,
    `LogRatioIrrational,
    `PositiveCeilReturns,
    `PrefixDefinitions,
    `RungDefinitions,
    `RungTransfer,
    `SyracuseSlope,
    `BridgeDefinitions,
    `BridgeExpectedTypes,
    `BridgeArithmetic,
    `BridgeEncoding,
    `BridgeRungs,
    `BridgeRewards,
    `BridgeTransport,
    `BridgeFinite,
    `BridgeExtremal,
    `BridgeBoundary,
    `BridgeSolution,
    `UnrestrictedDefinitions,
    `UnrestrictedExpectedTypes,
    `UnrestrictedCounts,
    `UnrestrictedCountBound,
    `UnrestrictedRotation,
    `UnrestrictedSwaps,
    `UnrestrictedCanonical,
    `UnrestrictedInjection,
    `UnrestrictedLimits,
    `UnrestrictedSolution]
  for name in owned do
    unless env.header.moduleNames.contains name do throwError "Owned module omitted: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if owned.contains moduleName then
        if let .axiomInfo _ := info then throwError "Custom owned axiom: {name}"
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for ax in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
              throwError "Forbidden axiom {ax} in {name}"
          liftIO <| IO.println ("UNRESTRICTED_SUPPORT " ++ (Json.mkObj [
            ("declaration",toJson name.toString), ("module",toJson moduleName.toString),
            ("raw_type",toJson (repr info.type).pretty),
            ("axioms",toJson (axioms.map Name.toString))]).compress)
          count := count+1
  if count == 0 then throwError "Empty own theorem audit"
  logInfo m!"Audited all {count} own/reused closures,23 target types and13 model bodies."
