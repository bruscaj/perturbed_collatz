import PressureSolution
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if m.toString.endsWith "Challenge" then throwError "Challenge module imported: {m}"
  let targets : Array (String × String) := #[    ("ExternalBridgePressureSupportChallenge.word_zeroVolumeConvention", "ExternalBridgePressureWordDraft.ZeroVolumeConvention"),
    ("ExternalBridgePressureSupportChallenge.word_auxiliaryEndpointWitness", "ExternalBridgePressureWordDraft.AuxiliaryEndpointWitness"),
    ("ExternalBridgePressureSupportChallenge.word_capIncrementBounds", "ExternalBridgePressureWordDraft.CapIncrementBounds"),
    ("ExternalBridgePressureSupportChallenge.word_canonicalWordLaw", "ExternalBridgePressureWordDraft.CanonicalWordLaw"),
    ("ExternalBridgePressureSupportChallenge.word_finiteWordPopulation", "ExternalBridgePressureWordDraft.FiniteWordPopulation"),
    ("ExternalBridgePressureSupportChallenge.word_boundedWordEnumeration", "ExternalBridgePressureWordDraft.BoundedWordEnumeration"),
    ("ExternalBridgePressureSupportChallenge.word_normalizedRewardLaw", "ExternalBridgePressureWordDraft.NormalizedRewardLaw"),
    ("ExternalBridgePressureSupportChallenge.word_auxPartitionFiniteSum", "ExternalBridgePressureWordDraft.AuxPartitionFiniteSum"),
    ("ExternalBridgePressureSupportChallenge.word_finitePartitionBounds", "ExternalBridgePressureWordDraft.FinitePartitionBounds"),
    ("ExternalBridgePressureSupportChallenge.word_capDifferenceGeometry", "ExternalBridgePressureWordDraft.CapDifferenceGeometry"),
    ("ExternalBridgePressureSupportChallenge.word_phaseUpTransport", "ExternalBridgePressureWordDraft.PhaseUpTransport"),
    ("ExternalBridgePressureSupportChallenge.word_phaseUpInjectionReward", "ExternalBridgePressureWordDraft.PhaseUpInjectionReward"),
    ("ExternalBridgePressureSupportChallenge.word_clampWordTransport", "ExternalBridgePressureWordDraft.ClampWordTransport"),
    ("ExternalBridgePressureSupportChallenge.word_clampFiberEncoding", "ExternalBridgePressureWordDraft.ClampFiberEncoding"),
    ("ExternalBridgePressureSupportChallenge.word_clampFiberCount", "ExternalBridgePressureWordDraft.ClampFiberCount"),
    ("ExternalBridgePressureSupportChallenge.word_clampRewardBound", "ExternalBridgePressureWordDraft.ClampRewardBound"),
    ("ExternalBridgePressureSupportChallenge.word_phaseLogComparison", "ExternalBridgePressureWordDraft.PhaseLogComparison"),
    ("ExternalBridgePressureSupportChallenge.word_completionTransport", "ExternalBridgePressureWordDraft.CompletionTransport"),
    ("ExternalBridgePressureSupportChallenge.word_truncationTransport", "ExternalBridgePressureWordDraft.TruncationTransport"),
    ("ExternalBridgePressureSupportChallenge.word_truncationFiberEncoding", "ExternalBridgePressureWordDraft.TruncationFiberEncoding"),
    ("ExternalBridgePressureSupportChallenge.word_truncationFiberCount", "ExternalBridgePressureWordDraft.TruncationFiberCount"),
    ("ExternalBridgePressureSupportChallenge.word_fixedShiftComparison", "ExternalBridgePressureWordDraft.FixedShiftComparison"),
    ("ExternalBridgePressureSupportChallenge.word_naturalDepthCompleteness", "ExternalBridgePressureWordDraft.NaturalDepthCompleteness"),
    ("ExternalBridgePressureSupportChallenge.word_wordDepthDictionary", "ExternalBridgePressureWordDraft.WordDepthDictionary"),
    ("ExternalBridgePressureSupportChallenge.word_wordPathPartitionEquality", "ExternalBridgePressureWordDraft.WordPathPartitionEquality"),
    ("ExternalBridgePressureSupportChallenge.word_concatenationTransport", "ExternalBridgePressureWordDraft.ConcatenationTransport"),
    ("ExternalBridgePressureSupportChallenge.word_partitionCocycle", "ExternalBridgePressureWordDraft.PartitionCocycle"),
    ("ExternalBridgePressureSupportChallenge.word_finiteTiltLipschitz", "ExternalBridgePressureWordDraft.FiniteTiltLipschitz"),
    ("ExternalBridgePressureSupportChallenge.word_closingPhaseTransport", "ExternalBridgePressureWordDraft.ClosingPhaseTransport"),
    ("ExternalBridgePressureSupportChallenge.word_rungWordTransport", "ExternalBridgePressureWordDraft.RungWordTransport"),
    ("ExternalBridgePressureSupportChallenge.analytic_uniformIntervalDiscrepancy", "ExternalBridgePressureAnalyticDraft.UniformIntervalDiscrepancy"),
    ("ExternalBridgePressureSupportChallenge.analytic_uniformShiftedIntervalDiscrepancy", "ExternalBridgePressureAnalyticDraft.UniformShiftedIntervalDiscrepancy"),
    ("ExternalBridgePressureSupportChallenge.analytic_capDifferenceDiscrepancy", "ExternalBridgePressureAnalyticDraft.CapDifferenceDiscrepancy"),
    ("ExternalBridgePressureSupportChallenge.analytic_auxiliaryOscillationEstimate", "ExternalBridgePressureAnalyticDraft.AuxiliaryOscillationEstimate"),
    ("ExternalBridgePressureSupportChallenge.analytic_auxiliaryBoundednessAndEquicontinuity", "ExternalBridgePressureAnalyticDraft.AuxiliaryBoundednessAndEquicontinuity"),
    ("ExternalBridgePressureSupportChallenge.analytic_gridMeshCover", "ExternalBridgePressureAnalyticDraft.GridMeshCover"),
    ("ExternalBridgePressureSupportChallenge.analytic_denseGridSubsequence", "ExternalBridgePressureAnalyticDraft.DenseGridSubsequence"),
    ("ExternalBridgePressureSupportChallenge.analytic_gridToUniformCauchy", "ExternalBridgePressureAnalyticDraft.GridToUniformCauchy"),
    ("ExternalBridgePressureSupportChallenge.analytic_uniformCauchyContinuousLimit", "ExternalBridgePressureAnalyticDraft.UniformCauchyContinuousLimit"),
    ("ExternalBridgePressureSupportChallenge.analytic_discontinuousSequenceCompactness", "ExternalBridgePressureAnalyticDraft.DiscontinuousSequenceCompactness"),
    ("ExternalBridgePressureSupportChallenge.analytic_auxiliarySubsequenceCompactness", "ExternalBridgePressureAnalyticDraft.AuxiliarySubsequenceCompactness"),
    ("ExternalBridgePressureSupportChallenge.analytic_fixedShiftNormalizedCompletion", "ExternalBridgePressureAnalyticDraft.FixedShiftNormalizedCompletion"),
    ("ExternalBridgePressureSupportChallenge.analytic_subsequenceRotationDomination", "ExternalBridgePressureAnalyticDraft.SubsequenceRotationDomination"),
    ("ExternalBridgePressureSupportChallenge.analytic_positiveRotationOrbitDense", "ExternalBridgePressureAnalyticDraft.PositiveRotationOrbitDense"),
    ("ExternalBridgePressureSupportChallenge.analytic_rotationDominationImpliesConstant", "ExternalBridgePressureAnalyticDraft.RotationDominationImpliesConstant"),
    ("ExternalBridgePressureSupportChallenge.analytic_auxiliarySubsequenceConstant", "ExternalBridgePressureAnalyticDraft.AuxiliarySubsequenceConstant"),
    ("ExternalBridgePressureSupportChallenge.analytic_phaseInfimumWellPosed", "ExternalBridgePressureAnalyticDraft.PhaseInfimumWellPosed"),
    ("ExternalBridgePressureSupportChallenge.analytic_phaseInfimumSuperadditivity", "ExternalBridgePressureAnalyticDraft.PhaseInfimumSuperadditivity"),
    ("ExternalBridgePressureSupportChallenge.analytic_candidatePressureWellPosed", "ExternalBridgePressureAnalyticDraft.CandidatePressureWellPosed"),
    ("ExternalBridgePressureSupportChallenge.analytic_feketeCandidateLimit", "ExternalBridgePressureAnalyticDraft.FeketeCandidateLimit"),
    ("ExternalBridgePressureSupportChallenge.analytic_subsequenceConstantIdentification", "ExternalBridgePressureAnalyticDraft.SubsequenceConstantIdentification"),
    ("ExternalBridgePressureSupportChallenge.analytic_fullAuxiliaryUniformPressure", "ExternalBridgePressureAnalyticDraft.FullAuxiliaryUniformPressure"),
    ("ExternalBridgePressureSupportChallenge.analytic_candidateTiltLipschitz", "ExternalBridgePressureAnalyticDraft.CandidateTiltLipschitz"),
    ("ExternalBridgePressureSupportChallenge.analytic_compactAuxiliaryTiltPressure", "ExternalBridgePressureAnalyticDraft.CompactAuxiliaryTiltPressure"),
    ("ExternalBridgePressureSupportChallenge.analytic_physicalRewardPressureComposition", "ExternalBridgePressureAnalyticDraft.PhysicalRewardPressureComposition"),
    ("ExternalBridgePressureSupportChallenge.analytic_uniformReferenceComposition", "ExternalBridgePressureAnalyticDraft.UniformReferenceComposition"),
    ("ExternalBridgePressureSupportChallenge.analytic_costPressureComposition", "ExternalBridgePressureAnalyticDraft.CostPressureComposition"),
    ("ExternalBridgePressureSupportChallenge.analytic_sourceRungPressureComposition", "ExternalBridgePressureAnalyticDraft.SourceRungPressureComposition"),
    ("ExternalBridgePressureSupportChallenge.analytic_variableTiltSourceAsymptotic", "ExternalBridgePressureAnalyticDraft.VariableTiltSourceAsymptotic"),
    ("ExternalBridgePressureSupportChallenge.analytic_candidateQualitativePressure", "ExternalBridgePressureAnalyticDraft.CandidateQualitativePressure"),
    ("ExternalBridgePressureSupportChallenge.analytic_candidateCorePressureComponents", "ExternalBridgePressureAnalyticDraft.CandidateCorePressureComponents"),
    ("ExternalBridgePressureSupportChallenge.analytic_finitePhaseLogIntegrability", "ExternalBridgePressureAnalyticDraft.FinitePhaseLogIntegrability"),
    ("ExternalBridgePressureSupportChallenge.analytic_integratedLowerBracketValidity", "ExternalBridgePressureAnalyticDraft.IntegratedLowerBracketValidity"),
    ("ExternalBridgePressureSupportChallenge.analytic_integratedLowerBracketCofinality", "ExternalBridgePressureAnalyticDraft.IntegratedLowerBracketCofinality")]
  for (proofString, expectedString) in targets do
    let proof := proofString.toName
    let expected := expectedString.toName
    let info ← getConstInfo proof
    unless info.type == mkConst expected do throwError "Frozen type mismatch: {proof}"
    let some raw := (← getConstInfo expected).value? | throwError "Missing expected body"
    liftIO <| IO.println ("PRESSURE_TARGET " ++ (Json.mkObj [
      ("declaration",toJson proof.toString),("expected",toJson expected.toString),
      ("raw_type",toJson (repr info.type).pretty),
      ("raw_expected_proposition",toJson (repr raw).pretty)]).compress)
  let models : Array String := #[    "ExternalBridgePressureWordDraft.ActualPhase",
    "ExternalBridgePressureWordDraft.AuxWord",
    "ExternalBridgePressureWordDraft.AuxWords",
    "ExternalBridgePressureWordDraft.BoundedWord",
    "ExternalBridgePressureWordDraft.CapDifference",
    "ExternalBridgePressureWordDraft.ClosedPhase",
    "ExternalBridgePressureWordDraft.Dcount",
    "ExternalBridgePressureWordDraft.OrderedPhases",
    "ExternalBridgePressureWordDraft.auxCap",
    "ExternalBridgePressureWordDraft.auxDepth",
    "ExternalBridgePressureWordDraft.auxFinitePartition",
    "ExternalBridgePressureWordDraft.auxLogPartition",
    "ExternalBridgePressureWordDraft.auxLogPressure",
    "ExternalBridgePressureWordDraft.auxPartition",
    "ExternalBridgePressureWordDraft.auxReward",
    "ExternalBridgePressureWordDraft.auxTerm",
    "ExternalBridgePressureWordDraft.auxTerm._proof_1",
    "ExternalBridgePressureWordDraft.auxTerm._proof_2",
    "ExternalBridgePressureWordDraft.boundedTailRecord",
    "ExternalBridgePressureWordDraft.boundedTailRecord._proof_1",
    "ExternalBridgePressureWordDraft.boundedTailRecord._proof_2",
    "ExternalBridgePressureWordDraft.canonicalProfile",
    "ExternalBridgePressureWordDraft.canonicalWord",
    "ExternalBridgePressureWordDraft.clampBits",
    "ExternalBridgePressureWordDraft.clampCode",
    "ExternalBridgePressureWordDraft.clampProfile",
    "ExternalBridgePressureWordDraft.clampWord",
    "ExternalBridgePressureWordDraft.completeProfile",
    "ExternalBridgePressureWordDraft.completeProfile._proof_1",
    "ExternalBridgePressureWordDraft.completeProfile._proof_2",
    "ExternalBridgePressureWordDraft.completeWord",
    "ExternalBridgePressureWordDraft.concatenate",
    "ExternalBridgePressureWordDraft.concatenate._proof_1",
    "ExternalBridgePressureWordDraft.concatenate._proof_2",
    "ExternalBridgePressureWordDraft.decodeBoundedWord",
    "ExternalBridgePressureWordDraft.firstIndex",
    "ExternalBridgePressureWordDraft.firstIndex._proof_1",
    "ExternalBridgePressureWordDraft.firstIndex._proof_2",
    "ExternalBridgePressureWordDraft.instDecidable_pressureWordDefinitions",
    "ExternalBridgePressureWordDraft.letterAt",
    "ExternalBridgePressureWordDraft.pathToWord",
    "ExternalBridgePressureWordDraft.phaseUp",
    "ExternalBridgePressureWordDraft.recoverClampProfile",
    "ExternalBridgePressureWordDraft.recoverClampWord",
    "ExternalBridgePressureWordDraft.recoverLongWord",
    "ExternalBridgePressureWordDraft.recoverLongWord._proof_1",
    "ExternalBridgePressureWordDraft.recoverLongWord._proof_2",
    "ExternalBridgePressureWordDraft.recoverLongWord._proof_3",
    "ExternalBridgePressureWordDraft.recoverLongWord._proof_4",
    "ExternalBridgePressureWordDraft.tailRecord",
    "ExternalBridgePressureWordDraft.truncateProfile",
    "ExternalBridgePressureWordDraft.truncateProfile._proof_1",
    "ExternalBridgePressureWordDraft.truncateProfile._proof_2",
    "ExternalBridgePressureWordDraft.truncateWord",
    "ExternalBridgePressureWordDraft.truncationCode",
    "ExternalBridgePressureWordDraft.wordToPath",
    "ExternalBridgePressureWordDraft.wordToPath._proof_1",
    "ExternalBridgePressureAnalyticDraft.CompactTiltActualConvergence",
    "ExternalBridgePressureAnalyticDraft.CompactTiltClosedConvergence",
    "ExternalBridgePressureAnalyticDraft.EventuallyEquicontinuousClosed",
    "ExternalBridgePressureAnalyticDraft.FunctionSequence",
    "ExternalBridgePressureAnalyticDraft.UniformAlong",
    "ExternalBridgePressureAnalyticDraft.UniformCauchyClosed",
    "ExternalBridgePressureAnalyticDraft.UniformClosedConvergence",
    "ExternalBridgePressureAnalyticDraft.UniformlyBoundedClosed",
    "ExternalBridgePressureAnalyticDraft.auxFamily",
    "ExternalBridgePressureAnalyticDraft.candidateCostPressure",
    "ExternalBridgePressureAnalyticDraft.candidatePressure",
    "ExternalBridgePressureAnalyticDraft.gridPoint",
    "ExternalBridgePressureAnalyticDraft.instDecidable_pressureAnalyticDefinitions",
    "ExternalBridgePressureAnalyticDraft.intervalCount",
    "ExternalBridgePressureAnalyticDraft.phaseInfimum",
    "ExternalBridgePressureAnalyticDraft.phaseValues",
    "ExternalBridgePressureAnalyticDraft.physicalCostFamily",
    "ExternalBridgePressureAnalyticDraft.physicalRewardFamily",
    "ExternalBridgePressureAnalyticDraft.pressureValues",
    "ExternalBridgePressureAnalyticDraft.shiftedIntervalCount"]
  for model in models do
    let [(name, info)] := env.constants.toList.filter (fun (name,_) => name.toString == model)
      | throwError "Missing or ambiguous model {model}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing model origin"
    let axs ← collectAxioms name
    liftIO <| IO.println ("PRESSURE_MODEL " ++ (Json.mkObj [
      ("declaration",toJson name.toString),("module",toJson env.header.moduleNames[idx.toNat]!.toString),
      ("raw_type",toJson (repr info.type).pretty),("raw_value",toJson (info.value?.map fun raw => (repr raw).pretty)),
      ("axioms",toJson ((axs.map Name.toString).qsort (· < ·)))]).compress)
  let owned : Array String := #["Definitions", "ExpectedTypes", "Arithmetic", "PopulationWeights", "DepthOneSeries", "LogRatioIrrational", "PositiveCeilReturns", "PrefixDefinitions", "RungDefinitions", "RungTransfer", "SyracuseSlope", "BridgeDefinitions", "BridgeExpectedTypes", "BridgeEncoding", "BridgeArithmetic", "BridgeRewards", "BridgeTransport", "PressureDefinitions", "PressureExpectedTypes", "PressureWordDefinitions", "PressureWordExpectedTypes", "PhaseCocycle", "PhasePaths", "WordArithmetic", "WordReward", "WordPopulation", "WordPhysical", "WordPartitions", "WordRung", "WordPhaseUp", "WordClamp", "WordClampCount", "WordCompletion", "WordTruncation", "WordTruncationFiber", "WordFiniteComparison", "WordPartitionTransport", "WordEndpoint", "WordConcatenation", "CompletePressureDefinitions", "CompletePressureExpectedTypes", "PressureAnalyticDefinitions", "PressureAnalyticExpectedTypes", "AnalyticFekete", "AnalyticPhaseInfimum", "AnalyticRotation", "AnalyticConstant", "AnalyticSubsequence", "AnalyticCompactness", "AnalyticCompactnessCompletion", "AnalyticRotationGrid", "AnalyticCircleGrid", "AnalyticAveraging", "AnalyticDiscrepancy", "AnalyticCapDiscrepancy", "AnalyticOscillation", "BridgeRungs", "AnalyticUniformPressure", "AnalyticReference", "AnalyticCost", "AnalyticQualitative", "AnalyticCore", "AnalyticIntegrals", "PressureSolution"]
  for name in owned do
    unless env.header.moduleNames.any (fun m => m.toString == name) do throwError "Owned module omitted: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if owned.contains moduleName.toString then
        if let .axiomInfo _ := info then throwError "Custom owned axiom: {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
            throwError "Forbidden axiom {ax} in {name}"
        liftIO <| IO.println ("PRESSURE_SUPPORT " ++ (Json.mkObj [
          ("declaration",toJson name.toString),("module",toJson moduleName.toString),
          ("raw_type",toJson (repr info.type).pretty),
          ("is_theorem",toJson (getOriginalConstKind? env name == some .thm)),
          ("axioms",toJson (axioms.map Name.toString))]).compress)
        count := count+1
  if count == 0 then throwError "Empty owned declaration audit"
  logInfo m!"Audited all {count} owned declaration closures,64 target types and77 model-origin entries (including opaque null bodies)."
