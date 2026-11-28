"""Clean public pressure-space supporting build; full mode requires every replay/comparator/checker gate.

Fetch public dependencies before running this verifier. This program never runs
lake update or the cache downloader. Build mode is explicitly lower assurance.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import sys

HERE = Path(__file__).resolve().parent
MATHLIB_COMMIT = "56a005855ea17e0b0958f73ec801ae140b0a1679"
OWNED_MODULES = ('Definitions', 'ExpectedTypes', 'Arithmetic', 'PopulationWeights', 'DepthOneSeries', 'LogRatioIrrational', 'PositiveCeilReturns', 'PrefixDefinitions', 'RungDefinitions', 'RungTransfer', 'SyracuseSlope', 'BridgeDefinitions', 'BridgeExpectedTypes', 'BridgeEncoding', 'BridgeArithmetic', 'BridgeRewards', 'BridgeTransport', 'PressureDefinitions', 'PressureExpectedTypes', 'PressureWordDefinitions', 'PressureWordExpectedTypes', 'PhaseCocycle', 'PhasePaths', 'WordArithmetic', 'WordReward', 'WordPopulation', 'WordPhysical', 'WordPartitions', 'WordRung', 'WordPhaseUp', 'WordClamp', 'WordClampCount', 'WordCompletion', 'WordTruncation', 'WordTruncationFiber', 'WordFiniteComparison', 'WordPartitionTransport', 'WordEndpoint', 'WordConcatenation', 'CompletePressureDefinitions', 'CompletePressureExpectedTypes', 'PressureAnalyticDefinitions', 'PressureAnalyticExpectedTypes', 'AnalyticFekete', 'AnalyticPhaseInfimum', 'AnalyticRotation', 'AnalyticConstant', 'AnalyticSubsequence', 'AnalyticCompactness', 'AnalyticCompactnessCompletion', 'AnalyticRotationGrid', 'AnalyticCircleGrid', 'AnalyticAveraging', 'AnalyticDiscrepancy', 'AnalyticCapDiscrepancy', 'AnalyticOscillation', 'BridgeRungs', 'AnalyticUniformPressure', 'AnalyticReference', 'AnalyticCost', 'AnalyticQualitative', 'AnalyticCore', 'AnalyticIntegrals', 'PressureSolution')
TARGETS = ('ExternalBridgePressureSupportChallenge.word_zeroVolumeConvention', 'ExternalBridgePressureSupportChallenge.word_auxiliaryEndpointWitness', 'ExternalBridgePressureSupportChallenge.word_capIncrementBounds', 'ExternalBridgePressureSupportChallenge.word_canonicalWordLaw', 'ExternalBridgePressureSupportChallenge.word_finiteWordPopulation', 'ExternalBridgePressureSupportChallenge.word_boundedWordEnumeration', 'ExternalBridgePressureSupportChallenge.word_normalizedRewardLaw', 'ExternalBridgePressureSupportChallenge.word_auxPartitionFiniteSum', 'ExternalBridgePressureSupportChallenge.word_finitePartitionBounds', 'ExternalBridgePressureSupportChallenge.word_capDifferenceGeometry', 'ExternalBridgePressureSupportChallenge.word_phaseUpTransport', 'ExternalBridgePressureSupportChallenge.word_phaseUpInjectionReward', 'ExternalBridgePressureSupportChallenge.word_clampWordTransport', 'ExternalBridgePressureSupportChallenge.word_clampFiberEncoding', 'ExternalBridgePressureSupportChallenge.word_clampFiberCount', 'ExternalBridgePressureSupportChallenge.word_clampRewardBound', 'ExternalBridgePressureSupportChallenge.word_phaseLogComparison', 'ExternalBridgePressureSupportChallenge.word_completionTransport', 'ExternalBridgePressureSupportChallenge.word_truncationTransport', 'ExternalBridgePressureSupportChallenge.word_truncationFiberEncoding', 'ExternalBridgePressureSupportChallenge.word_truncationFiberCount', 'ExternalBridgePressureSupportChallenge.word_fixedShiftComparison', 'ExternalBridgePressureSupportChallenge.word_naturalDepthCompleteness', 'ExternalBridgePressureSupportChallenge.word_wordDepthDictionary', 'ExternalBridgePressureSupportChallenge.word_wordPathPartitionEquality', 'ExternalBridgePressureSupportChallenge.word_concatenationTransport', 'ExternalBridgePressureSupportChallenge.word_partitionCocycle', 'ExternalBridgePressureSupportChallenge.word_finiteTiltLipschitz', 'ExternalBridgePressureSupportChallenge.word_closingPhaseTransport', 'ExternalBridgePressureSupportChallenge.word_rungWordTransport', 'ExternalBridgePressureSupportChallenge.analytic_uniformIntervalDiscrepancy', 'ExternalBridgePressureSupportChallenge.analytic_uniformShiftedIntervalDiscrepancy', 'ExternalBridgePressureSupportChallenge.analytic_capDifferenceDiscrepancy', 'ExternalBridgePressureSupportChallenge.analytic_auxiliaryOscillationEstimate', 'ExternalBridgePressureSupportChallenge.analytic_auxiliaryBoundednessAndEquicontinuity', 'ExternalBridgePressureSupportChallenge.analytic_gridMeshCover', 'ExternalBridgePressureSupportChallenge.analytic_denseGridSubsequence', 'ExternalBridgePressureSupportChallenge.analytic_gridToUniformCauchy', 'ExternalBridgePressureSupportChallenge.analytic_uniformCauchyContinuousLimit', 'ExternalBridgePressureSupportChallenge.analytic_discontinuousSequenceCompactness', 'ExternalBridgePressureSupportChallenge.analytic_auxiliarySubsequenceCompactness', 'ExternalBridgePressureSupportChallenge.analytic_fixedShiftNormalizedCompletion', 'ExternalBridgePressureSupportChallenge.analytic_subsequenceRotationDomination', 'ExternalBridgePressureSupportChallenge.analytic_positiveRotationOrbitDense', 'ExternalBridgePressureSupportChallenge.analytic_rotationDominationImpliesConstant', 'ExternalBridgePressureSupportChallenge.analytic_auxiliarySubsequenceConstant', 'ExternalBridgePressureSupportChallenge.analytic_phaseInfimumWellPosed', 'ExternalBridgePressureSupportChallenge.analytic_phaseInfimumSuperadditivity', 'ExternalBridgePressureSupportChallenge.analytic_candidatePressureWellPosed', 'ExternalBridgePressureSupportChallenge.analytic_feketeCandidateLimit', 'ExternalBridgePressureSupportChallenge.analytic_subsequenceConstantIdentification', 'ExternalBridgePressureSupportChallenge.analytic_fullAuxiliaryUniformPressure', 'ExternalBridgePressureSupportChallenge.analytic_candidateTiltLipschitz', 'ExternalBridgePressureSupportChallenge.analytic_compactAuxiliaryTiltPressure', 'ExternalBridgePressureSupportChallenge.analytic_physicalRewardPressureComposition', 'ExternalBridgePressureSupportChallenge.analytic_uniformReferenceComposition', 'ExternalBridgePressureSupportChallenge.analytic_costPressureComposition', 'ExternalBridgePressureSupportChallenge.analytic_sourceRungPressureComposition', 'ExternalBridgePressureSupportChallenge.analytic_variableTiltSourceAsymptotic', 'ExternalBridgePressureSupportChallenge.analytic_candidateQualitativePressure', 'ExternalBridgePressureSupportChallenge.analytic_candidateCorePressureComponents', 'ExternalBridgePressureSupportChallenge.analytic_finitePhaseLogIntegrability', 'ExternalBridgePressureSupportChallenge.analytic_integratedLowerBracketValidity', 'ExternalBridgePressureSupportChallenge.analytic_integratedLowerBracketCofinality')
FROZEN_SOURCES = {'Definitions.lean': 'cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc', 'ExpectedTypes.lean': '5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968', 'Arithmetic.lean': '8ad07971f3dd9b211aa99c36f6ed9c645e9dbb158b7ba33e81b72d5ca2c6f76e', 'PopulationWeights.lean': '8affb6d578e9891f306df4b54cc621c33d110227eaec7912d8dcf826f9697190', 'DepthOneSeries.lean': 'b0852b07d1f7105c61464d1642c998ece3563cb81e658cfe4a995f0e6b7e2562', 'LogRatioIrrational.lean': '2a2950ef39be685654ab7c3d3c4c734cf6103a74fa622d450ee0675e0240a89e', 'PositiveCeilReturns.lean': '98e1852aaa8baa5ecabcc70424b24d8871f7178fb7768b31c8278a579f0e8a37', 'PrefixDefinitions.lean': 'd7b5cd8b624dae007e3c3dc7f3620260dbfcf2169d0211b0859e18ed58180069', 'RungDefinitions.lean': '8c1996d5e2a11f726324f8f0fd282c061ed1b3819ccb734ecbccf49a8ccb17b5', 'RungTransfer.lean': 'e61650b3d2f90f3431c2bd861c57448aa86d54be769d554ab437808d7d612dde', 'SyracuseSlope.lean': '7909ad410f4b2e1ac7cf13d6f476679aa1d608c92f95ca2c3514a696a3cd5395', 'BridgeDefinitions.lean': '7a36ebc1e9ff89fcec7ad1fdae1c2d5ae9ee011b06ae110fd4f34999e7df19a7', 'BridgeExpectedTypes.lean': '850dcdd0d75479edaeab1c8d6d336b9099f56511e0b6f5a5125bedfca05838aa', 'BridgeEncoding.lean': 'f7f6f59daca369a1347219540cfbc15312af9592b65f123c041418939c480816', 'BridgeArithmetic.lean': '645d446755a140470ee402fdd0596e9fd8c55496d1de6515ff1e756538546f57', 'BridgeRewards.lean': '53da32ac28f519ad0e63bfad402139c91f6856e43d13134bcfa6430807c3e673', 'BridgeTransport.lean': '35a0565a222c677fd59249de39599d526d982dc97453c60ed1a1261b321612cb', 'PressureDefinitions.lean': '07d60f44e7aaa3107518678bb1780b4867a37f07c3db9b49e89f9402c8b45cd4', 'PressureExpectedTypes.lean': '9aa83c42cf2ccb23490ce84da1b21b9d6de0fb26dbf435d21b4d27bcc215f015', 'PressureWordDefinitions.lean': '3dd0db7a7ac1bf2adf2a048c51080cef65f6dd769a5ca95f58ae443a8110fe03', 'PressureWordExpectedTypes.lean': '010c0e9dd204fd5d6ec2173bbe39eb270d67f971bb59093c1a24804dd8d0f5f4', 'PhaseCocycle.lean': '432d64a737ba454eeff5b1d7f24d73b45e68d44bb34d88c238ce751aafb8cafe', 'PhasePaths.lean': '0bf85081aab115ce706cb9989b0c88728ec065f15cb501090fa1fd1da43bf55e', 'WordArithmetic.lean': 'a2e2f919a1b103ca36e0b431d217d03c176019963f4bea046ed193e7af82912c', 'WordReward.lean': '79b6024c8a59a24a0c941efc6eeebb4178844743fdfaa6a480e244666d8ad473', 'WordPopulation.lean': 'a5dd789e89af123be788e229679b0364a9575befa5b68b10d49864753bbc77d3', 'WordPhysical.lean': '54dd2303e109040a6d7937e99329047c8c630483c9b595fb4c85f8a10ac5eead', 'WordPartitions.lean': 'de397966da98ec7c93d8a57b757552ebcf6a415c186d10e3ea2e5be35fb4cb32', 'WordRung.lean': 'fad8ddd5cda899e869fd09a9d62c862692bb52ac1efd175fc0a2c9d759f00a25', 'WordPhaseUp.lean': 'f3802b8951b522c37c145117e737278c787c8265ba73856f4bf11b3cdc966d3b', 'WordClamp.lean': '5840853632287a4852d4be06347e7280b5bbb7362dcb464cdd2f9c9189a53b6a', 'WordClampCount.lean': '882432a4d8cd42ca1ca011a9228d9a7a22332558f5ebf2d4c333a952d1207544', 'WordCompletion.lean': 'c0fad3648101fca2cbec3e067531ee264e44b2e55f82b904bc39080941c91866', 'WordTruncation.lean': '5d101961cce6b0619295fe261f9f125b5e91256fc8678dbc275216dc249e4525', 'WordTruncationFiber.lean': '38da641eb858ac38abfaaa4e1fed3bccf954cd7957a9fbb7db188e2cdf5ffa4b', 'WordFiniteComparison.lean': 'b68eb074c13d0012b4ce76ad83d12d1be3a66dbb17f78e9807487feed2e8e6b9', 'WordPartitionTransport.lean': '1627f9610121b60178da707f4f34f38d0cd7cc0496271476702b3f8bb1a20990', 'WordEndpoint.lean': '8dac2b32a0f4871fd7ddac286dcbab732176667d68fb1d43d61dcd5de8e7e688', 'WordConcatenation.lean': '005db4a8714832d582018aecd890db29dd7ae83ff250bb3874c92d0235a6d88a', 'CompletePressureDefinitions.lean': 'fbc125a7aeb568b2e47f314956bed9038e12d0044111a9f7a10c4f8df0eba91e', 'CompletePressureExpectedTypes.lean': 'e21ef1fec4dfab47a945590d9b8179002d4c6505f669355710e450e09163412d', 'PressureAnalyticDefinitions.lean': '948dae752ed3f7209f7a1e067e44e35bc6f8ac0875b54d830858d2ea19c748fd', 'PressureAnalyticExpectedTypes.lean': 'a6264a5beef9e5a5ffa936f9c20ff9a54310bfc7b8fd3cc20b2c1942615854d0', 'AnalyticFekete.lean': '8228a52855902ad33f8303683fdf250716f856be3656886b216d7bf7ffa317e2', 'AnalyticPhaseInfimum.lean': '02486b99ca63ebce5d7d86ee3b0d8366e0ef042eba0583326124fee94930d6bc', 'AnalyticRotation.lean': '36bf12f658ce3bd4ef5a8ae2453b2f2224509cc5281fb42eb102dbd5bcf3fe8d', 'AnalyticConstant.lean': 'cc443171ede66bc0e3c40dc917d789d469f0be51152d771cbb9ddda7c0098d6f', 'AnalyticSubsequence.lean': '533e7033700746f6db52ba0a356f93c7dddf4a7ee9b9ec11a49f5f67fcf06692', 'AnalyticCompactness.lean': 'd40de57dfce793c90ba2633194235641c9f8389806c90d6f60ec6e64c70a4260', 'AnalyticCompactnessCompletion.lean': 'bc9717e9fcc8cc993d1db552a5b7b49353d071f4081ee0c33e677bc270a9248d', 'AnalyticRotationGrid.lean': '6ba5ad348624333185b247d3bdff26428a6d8e2f43f3d5e7b5db3c858cef55e3', 'AnalyticCircleGrid.lean': '1d5f8906978c65406f8ae315699764455a79389eb06ccb6b07b3a40341d4f437', 'AnalyticAveraging.lean': 'a6801aa66171973b6c53e25929ca6a53af771b4bce7804e1df31a06521dff003', 'AnalyticDiscrepancy.lean': '9aebb930ce32ad27ffdc90238b5c044e682b4f7edf4889dfca31be1461859175', 'AnalyticCapDiscrepancy.lean': '230af917dd7520e56eecdcbc7bb15726942ac748feb3f75c5d4bb4a532603a64', 'AnalyticOscillation.lean': '023478a47bf7ab07376d0ad032c2e94addb08a0981fcff6334d292e84cbbd8d8', 'BridgeRungs.lean': 'df4d32953097dd24a6479aae99fbd93a5dd9ece47eb98d59347055db2209872d', 'AnalyticUniformPressure.lean': 'b81ce58e21ffdca9fb2f787cacb53d621de8a0ffc08c120f6b0dabe3d98faf8c', 'AnalyticReference.lean': '0be327f137039c838342136072a834e06042c61c504356dc00dd78647771b132', 'AnalyticCost.lean': '0504d749813424d806c5e124f2a0c8b957c85d24e127e94f20bfb7e836dd33d8', 'AnalyticQualitative.lean': '7f9b0c811ebc8789167c9c112d1760b5b5f2987230a906e8e7e85c9f09049031', 'AnalyticCore.lean': '78e0c61963d0be8f20d4134f16ef1dd5d1dafb70946cc3894360d01ea6d23609', 'AnalyticIntegrals.lean': 'e4d2a8aa56fba92c749ee0dc68bbbd9a6cbb30339803ca0527cd1f9165b2d5f4', 'PressureChallenge.lean': '05470364b4d2daec53364e2b897aeef30f0385dad723a9ff6c9414ba7a2e37bc', 'target_map.json': '1d89085fc125dd39d29acd66a9c475e6938fe1da2e5d7425507b354c227f1ea5', 'word_legacy_model_metadata.json': '80bb462b37eae3d1a286d965d9abad844b72f777359c9c839d52e29693cf5fbc'}
AXIOMS = ("propext", "Quot.sound", "Classical.choice")
CHECKERS = ("Lean default", "Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


EXPECTED_HELPER_COUNT = 1293
MODEL_NAMES = ('ExternalBridgePressureAnalyticDraft.CompactTiltActualConvergence', 'ExternalBridgePressureAnalyticDraft.CompactTiltClosedConvergence', 'ExternalBridgePressureAnalyticDraft.EventuallyEquicontinuousClosed', 'ExternalBridgePressureAnalyticDraft.FunctionSequence', 'ExternalBridgePressureAnalyticDraft.UniformAlong', 'ExternalBridgePressureAnalyticDraft.UniformCauchyClosed', 'ExternalBridgePressureAnalyticDraft.UniformClosedConvergence', 'ExternalBridgePressureAnalyticDraft.UniformlyBoundedClosed', 'ExternalBridgePressureAnalyticDraft.auxFamily', 'ExternalBridgePressureAnalyticDraft.candidateCostPressure', 'ExternalBridgePressureAnalyticDraft.candidatePressure', 'ExternalBridgePressureAnalyticDraft.gridPoint', 'ExternalBridgePressureAnalyticDraft.instDecidable_pressureAnalyticDefinitions', 'ExternalBridgePressureAnalyticDraft.intervalCount', 'ExternalBridgePressureAnalyticDraft.phaseInfimum', 'ExternalBridgePressureAnalyticDraft.phaseValues', 'ExternalBridgePressureAnalyticDraft.physicalCostFamily', 'ExternalBridgePressureAnalyticDraft.physicalRewardFamily', 'ExternalBridgePressureAnalyticDraft.pressureValues', 'ExternalBridgePressureAnalyticDraft.shiftedIntervalCount', 'ExternalBridgePressureWordDraft.ActualPhase', 'ExternalBridgePressureWordDraft.AuxWord', 'ExternalBridgePressureWordDraft.AuxWords', 'ExternalBridgePressureWordDraft.BoundedWord', 'ExternalBridgePressureWordDraft.CapDifference', 'ExternalBridgePressureWordDraft.ClosedPhase', 'ExternalBridgePressureWordDraft.Dcount', 'ExternalBridgePressureWordDraft.OrderedPhases', 'ExternalBridgePressureWordDraft.auxCap', 'ExternalBridgePressureWordDraft.auxDepth', 'ExternalBridgePressureWordDraft.auxFinitePartition', 'ExternalBridgePressureWordDraft.auxLogPartition', 'ExternalBridgePressureWordDraft.auxLogPressure', 'ExternalBridgePressureWordDraft.auxPartition', 'ExternalBridgePressureWordDraft.auxReward', 'ExternalBridgePressureWordDraft.auxTerm', 'ExternalBridgePressureWordDraft.auxTerm._proof_1', 'ExternalBridgePressureWordDraft.auxTerm._proof_2', 'ExternalBridgePressureWordDraft.boundedTailRecord', 'ExternalBridgePressureWordDraft.boundedTailRecord._proof_1', 'ExternalBridgePressureWordDraft.boundedTailRecord._proof_2', 'ExternalBridgePressureWordDraft.canonicalProfile', 'ExternalBridgePressureWordDraft.canonicalWord', 'ExternalBridgePressureWordDraft.clampBits', 'ExternalBridgePressureWordDraft.clampCode', 'ExternalBridgePressureWordDraft.clampProfile', 'ExternalBridgePressureWordDraft.clampWord', 'ExternalBridgePressureWordDraft.completeProfile', 'ExternalBridgePressureWordDraft.completeProfile._proof_1', 'ExternalBridgePressureWordDraft.completeProfile._proof_2', 'ExternalBridgePressureWordDraft.completeWord', 'ExternalBridgePressureWordDraft.concatenate', 'ExternalBridgePressureWordDraft.concatenate._proof_1', 'ExternalBridgePressureWordDraft.concatenate._proof_2', 'ExternalBridgePressureWordDraft.decodeBoundedWord', 'ExternalBridgePressureWordDraft.firstIndex', 'ExternalBridgePressureWordDraft.firstIndex._proof_1', 'ExternalBridgePressureWordDraft.firstIndex._proof_2', 'ExternalBridgePressureWordDraft.instDecidable_pressureWordDefinitions', 'ExternalBridgePressureWordDraft.letterAt', 'ExternalBridgePressureWordDraft.pathToWord', 'ExternalBridgePressureWordDraft.phaseUp', 'ExternalBridgePressureWordDraft.recoverClampProfile', 'ExternalBridgePressureWordDraft.recoverClampWord', 'ExternalBridgePressureWordDraft.recoverLongWord', 'ExternalBridgePressureWordDraft.recoverLongWord._proof_1', 'ExternalBridgePressureWordDraft.recoverLongWord._proof_2', 'ExternalBridgePressureWordDraft.recoverLongWord._proof_3', 'ExternalBridgePressureWordDraft.recoverLongWord._proof_4', 'ExternalBridgePressureWordDraft.tailRecord', 'ExternalBridgePressureWordDraft.truncateProfile', 'ExternalBridgePressureWordDraft.truncateProfile._proof_1', 'ExternalBridgePressureWordDraft.truncateProfile._proof_2', 'ExternalBridgePressureWordDraft.truncateWord', 'ExternalBridgePressureWordDraft.truncationCode', 'ExternalBridgePressureWordDraft.wordToPath', 'ExternalBridgePressureWordDraft.wordToPath._proof_1')
FROZEN_PROPOSITIONS_SHA256 = '0f10513a5beb18a0b50ff65d1c26a048617d800283ed22c9c55abc29ea036cdb'
FROZEN_MODELS_SHA256 = '669605092d4da153af55d9e366abaf0f5a99558dc44384f34fec11b7d26f0e44'


def source_gate(root, inventory=None):
    """Fail closed on exact meanings and complete owned/target/helper/model coverage."""
    root = Path(root)
    inventory = inventory or json.loads((root/"inventory.json").read_text())
    expected = {m+".lean" for m in OWNED_MODULES} | {"PressureChallenge.lean", "Audit.lean"}
    require(inventory.get("owned_modules") == list(OWNED_MODULES), "inventory owned module coverage mismatch")
    require(len(inventory["targets"]) == 64 and sorted(x["declaration"] for x in inventory["targets"]) == sorted(TARGETS), "inventory target coverage mismatch")
    helpers = [x["declaration"] for x in inventory["helpers"]]
    require(len(helpers) == EXPECTED_HELPER_COUNT and len(set(helpers)) == EXPECTED_HELPER_COUNT and not set(helpers)&set(TARGETS), "inventory helper coverage mismatch")
    require(all(x["module"] in OWNED_MODULES for x in inventory["targets"]+inventory["helpers"]), "inventory declaration module mismatch")
    require(len(inventory["models"]) == 77 and sorted(x["declaration"] for x in inventory["models"]) == sorted(MODEL_NAMES), "inventory model coverage mismatch")
    required = expected | set(FROZEN_SOURCES) | {"verify.py", "README.md", "ARGUMENT.md", "comparator.json", "owned_modules.json", "specification.json", "frozen_propositions.json", "frozen_models.json", "lake-manifest.json", "lakefile.toml", "lean-toolchain", "cache-imports.txt", "test_mutations.py", "provenance.json"}
    require(required <= set(inventory["sources_sha256"]), "source inventory coverage mismatch")
    actual = {p.name for p in root.glob("*.lean")}
    require(actual == expected, f"owned Lean module coverage mismatch: {sorted(actual ^ expected)}")
    for name, pin in FROZEN_SOURCES.items():
        require(digest(root/name) == pin, f"frozen source digest mismatch: {name}")
    require(json.loads((root/"owned_modules.json").read_text()) == list(OWNED_MODULES), "owned module register mismatch")
    config = json.loads((root/"comparator.json").read_text())
    require(config["theorem_names"] == list(TARGETS), "frozen target register mismatch")
    require(config["challenge_module"] == "PressureChallenge" and config["solution_module"] == "PressureSolution", "comparator module mismatch")
    require(config["permitted_axioms"] == list(AXIOMS), "axiom policy mismatch")
    require(config.get("external_kernels") == {"nanoda": ["nanoda_bin"]}, "independent checker configuration mismatch")
    require(config.get("definition_names") == [], "unexpected definition holes")
    specification = json.loads((root/"specification.json").read_text())
    require(specification["frozen_propositions_sha256"] == FROZEN_PROPOSITIONS_SHA256 and digest(root/"frozen_propositions.json") == FROZEN_PROPOSITIONS_SHA256, "frozen raw proposition register mismatch")
    require(specification["frozen_model_definitions_sha256"] == FROZEN_MODELS_SHA256 and digest(root/"frozen_models.json") == FROZEN_MODELS_SHA256, "frozen raw model register mismatch")
    require(inventory["models"] == sorted(json.loads((root/"frozen_models.json").read_text()), key=lambda r: r["declaration"]), "exact frozen model inventory mismatch")
    require(set(specification["files"]) == set(FROZEN_SOURCES) and all(specification["files"][n]["sha256"] == pin for n,pin in FROZEN_SOURCES.items()), "original frozen specification pin mismatch")
    for name, pin in inventory["sources_sha256"].items():
        path = Path(name)
        require(not path.is_absolute() and ".." not in path.parts, "unsafe source inventory path")
        require((root/path).is_file() and not (root/path).is_symlink(), f"missing source: {name}")
        require(digest(root/path) == pin, f"source inventory mismatch: {name}")


def prepare_dependencies(root, *, dependency_cache=None, mathlib_cache=None):
    """Materialize public Git-pinned cached dependencies; never fetch or mutate the cache.

    dependency_cache is a normal prepared project's .lake/packages directory.
    mathlib_cache is a pinned mathlib checkout with its normal dependency cache.
    Omitting both uses this public project's existing .lake/packages directory.
    This helper intentionally does not accept/rewrite any own proof source.
    """
    root = Path(root)
    require(not (dependency_cache and mathlib_cache), "choose one dependency cache layout")
    manifest = json.loads((HERE/"lake-manifest.json").read_text())
    require(manifest["packagesDir"] == ".lake/packages", "unexpected package layout")
    packages = manifest["packages"]
    names = [p["name"] for p in packages]
    require(len(names) == len(set(names)) and "mathlib" in names, "invalid package inventory")
    destination = root/".lake/packages"
    destination.mkdir(parents=True, exist_ok=True)
    records = []
    for package in packages:
        name = package["name"]
        require(re.fullmatch(r"[A-Za-z0-9_-]+", name), "unsafe package name")
        require(package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"]),
                f"dependency lacks an exact Git pin: {name}")
        require(package["url"].startswith("https://github.com/") and "@" not in package["url"],
                f"non-public dependency URL: {name}")
        if name == "mathlib":
            require(package["rev"] == MATHLIB_COMMIT, "mathlib revision mismatch")
        if mathlib_cache:
            source = Path(mathlib_cache) if name == "mathlib" else Path(mathlib_cache)/".lake/packages"/name
        else:
            source = Path(dependency_cache or HERE/".lake/packages")/name
        source = source.resolve()
        require(source.is_dir(), f"missing pinned public dependency cache: {name}; fetch dependencies first")
        revision = subprocess.run(["git", "-C", str(source), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=True).stdout.strip()
        require(revision == package["rev"], f"dependency source pin mismatch: {name}")
        subprocess.run(["git", "-C", str(source), "diff", "--exit-code", "HEAD", "--"],
                       capture_output=True, text=True, check=True)
        target = destination/name
        require(not target.exists(), f"dependency destination already exists: {name}")

        def ignore(directory, children):
            ignored = {"__pycache__", ".DS_Store"} & set(children)
            if Path(directory) == source/".lake":
                ignored |= {"packages"} & set(children)
            return ignored

        # Preserve Git-tracked relative links (e.g. batteries docs/README.md)
        # rather than changing their file type. No link may escape its package.
        for directory, dirs, files in os.walk(source, followlinks=False):
            if Path(directory) == source/".lake" and "packages" in dirs:
                dirs.remove("packages")
            for entry in dirs+files:
                path = Path(directory)/entry
                if path.is_symlink():
                    require(path.resolve().is_relative_to(source),
                            f"dependency cache link escapes package: {name}")
        shutil.copytree(source, target, symlinks=True, ignore=ignore)
        subprocess.run(["git", "-C", str(target), "diff", "--exit-code", "HEAD", "--"],
                       capture_output=True, text=True, check=True)
        records.append({"name": name, "url": package["url"], "revision": revision})
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("build", "full"), default="full")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--mathlib-cache", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "all64 compact pressure-space supporting targets; no full pressure law",
              "mode": args.mode, "status": "running", "steps": []}
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(key, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin")+os.pathsep+env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    lake = shutil.which("lake", path=env.get("PATH"))
    log_directory = Path(tempfile.mkdtemp(prefix="pressure-verifier-logs-")) if args.report is None else None

    def save():
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2)+"\n")

    try:
        source_gate(HERE)
        if args.mode == "full":
            require(sys.platform.startswith("linux"), "full assurance requires Linux sandbox support; no full gate passed")
        require(lake is not None, "lake unavailable; install pinned Lean or pass --toolchain")
        inventory = json.loads((HERE/"inventory.json").read_text())
        with tempfile.TemporaryDirectory(prefix="collatz-public-pressure-") as temporary:
            root = Path(temporary)/"project"
            root.mkdir()
            # Explicit own source/config inventory; never copy ambient build caches.
            for name in inventory["sources_sha256"]:
                shutil.copyfile(HERE/name, root/name)
            shutil.copyfile(HERE/"inventory.json", root/"inventory.json")
            report["dependencies"] = prepare_dependencies(root,
                dependency_cache=args.dependency_cache, mathlib_cache=args.mathlib_cache)
            save()

            def run(label, command):
                row = {"label": label, "command": [str(x) for x in command], "status": "running"}
                report["steps"].append(row)
                save()
                print(f"RUN {label}", flush=True)
                started = time.monotonic()
                result = subprocess.run([str(x) for x in command], cwd=root, env=env,
                                        capture_output=True, text=True)
                row.update({"exit_code": result.returncode, "seconds": round(time.monotonic()-started, 3),
                            "status": "passed" if result.returncode == 0 else "failed"})
                evidence_dir = (args.report.parent/(args.report.stem+".logs")) if args.report else log_directory
                evidence_dir.mkdir(parents=True, exist_ok=True)
                for stream_name, value in (("stdout", result.stdout), ("stderr", result.stderr)):
                    data = value.encode()
                    row[stream_name+"_sha256"] = hashlib.sha256(data).hexdigest()
                    row[stream_name+"_bytes"] = len(data)
                    row[stream_name] = value[:4000]
                    if data:
                        name = f"{len(report['steps'])-1:02d}-" + re.sub(r"[^a-z0-9]+", "-", label.lower()).strip("-") + "."+stream_name+".txt.gz"
                        evidence = evidence_dir/name
                        evidence.write_bytes(gzip.compress(data, mtime=0))
                        row[stream_name+"_gzip"] = str(evidence)
                        row[stream_name+"_gzip_sha256"] = digest(evidence)
                save()
                require(result.returncode == 0, f"required gate failed: {label}")
                print(f"PASS {label} ({row['seconds']}s)", flush=True)
                return result.stdout

            version = run("pinned toolchain", [lake, "env", "lean", "--version"])
            require("version 4.35.0," in version, "wrong pressure toolchain")
            build = run("all own source clean build", [lake, "build"])
            require("warning:" not in build + report["steps"][-1]["stderr"], "own build emitted a warning")
            missing = [m for m in OWNED_MODULES if not (root/f".lake/build/lib/lean/{m}.olean").is_file()]
            require(not missing, f"own modules omitted from build: {missing}")
            source_gate(root, inventory)
            audit = run("all own theorem closures and raw frozen target types",
                        [lake, "env", "lean", "-DwarningAsError=true", "-R", str(root), "-o", str(root/".lake/build/lib/lean/Audit.olean"), "Audit.lean"])
            meta = [json.loads(x.removeprefix("PRESSURE_TARGET ")) for x in audit.splitlines()
                    if x.startswith("PRESSURE_TARGET ")]
            closures = [json.loads(x.removeprefix("PRESSURE_SUPPORT ")) for x in audit.splitlines()
                        if x.startswith("PRESSURE_SUPPORT ")]
            model_rows = [json.loads(x.removeprefix("PRESSURE_MODEL ")) for x in audit.splitlines() if x.startswith("PRESSURE_MODEL ")]
            frozen_models = json.loads((root/"frozen_models.json").read_text())
            require(len(model_rows) == 77 and sorted(model_rows,key=lambda x:x["declaration"]) == sorted(frozen_models,key=lambda x:x["declaration"]), "canonical frozen model body/type mismatch")
            require(sorted(model_rows,key=lambda x:x["declaration"]) == inventory["models"], "model body inventory mismatch")
            by_name = {x["declaration"]: x for x in closures}
            targets = [by_name[x["declaration"]] | x for x in meta]
            helpers = [x for x in closures if x["declaration"] not in TARGETS]
            frozen = {row["declaration"]: row for row in json.loads((root/"frozen_propositions.json").read_text())}
            require(all(row["raw_expected_proposition"] == frozen[row["expected"]]["raw_proposition"] for row in targets),
                    "canonical frozen proposition body mismatch")
            targets.sort(key=lambda x:x["declaration"])
            helpers.sort(key=lambda x:x["declaration"])
            require([x["declaration"] for x in targets] == sorted(TARGETS), "missing frozen target implementation")
            require(targets == inventory["targets"], "elaborated frozen target inventory mismatch")
            require(helpers == inventory["helpers"], "own generated-helper inventory mismatch")
            report.update({"targets": targets, "helpers": helpers, "models": model_rows, "own_module_count": len(OWNED_MODULES),
                           "own_declaration_count": len(targets)+len(helpers)})
            if args.mode == "full":
                roots = sorted({x["declaration"] for x in targets+helpers})
                export = root/".lake/pressure-complete-proof-closure.ndjson"
                command = [lake, "env", "leanexport", "Audit", "--", *roots]
                started = time.monotonic()
                with export.open("wb") as stream:
                    result = subprocess.run(command, cwd=root, env=env, stdout=stream,
                                            stderr=subprocess.PIPE, text=True)
                row = {"label": "fresh complete own proof-closure export", "command": command,
                    "exit_code": result.returncode, "seconds": round(time.monotonic()-started, 3),
                    "stderr": result.stderr, "roots": roots, "bytes": export.stat().st_size,
                    "sha256": digest(export), "source_sha256": inventory["sources_sha256"]}
                report["steps"].append(row)
                save()
                require(result.returncode == 0 and export.stat().st_size > 0, "fresh complete proof export failed")
                replay = run("fresh complete proof-closure replay and all bundled checkers",
                    [lake, "check", "--from-export", export, "--paranoid"])
                comparison = run("all64 frozen statements and independent checker",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"])
                coverage = {}
                for label, output in (("complete proof closure", replay), ("frozen statement comparison", comparison)):
                    accepted = [name for name in CHECKERS if f"{name} kernel accepts the solution" in output]
                    require(accepted == list(CHECKERS), f"missing required six-checker coverage: {label}")
                    coverage[label] = accepted
                report["checker_coverage"] = coverage
                report["status"] = "passed pressure full assurance gates"
            else:
                report["status"] = "partial: clean pressure build and axiom audit only"
                report["missing_gates"] = ["fresh imported-proof replay", "trusted statement comparator",
                                           "independently implemented checker"]
    except Exception as error:
        report.update({"status": "failed", "error": str(error)})
        raise
    finally:
        save()
    print(report["status"])


if __name__ == "__main__":
    main()
