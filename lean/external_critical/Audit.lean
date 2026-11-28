import CriticalSolution
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    if m.toString.endsWith "Challenge" then throwError "Challenge module imported: {m}"
  let targets : Array (Name × Name) := #[    (`ExternalCriticalSupportChallenge.space_topology, `ExternalCriticalSpaceDraft.SpaceTopology),
    (`ExternalCriticalSupportChallenge.phase_representative_law, `ExternalCriticalSpaceDraft.PhaseRepresentativeLaw),
    (`ExternalCriticalSupportChallenge.shift_group_and_continuity, `ExternalCriticalSpaceDraft.ShiftGroupAndContinuity),
    (`ExternalCriticalSupportChallenge.reward_roof_and_regularity, `ExternalCriticalSpaceDraft.RewardRoofAndRegularity),
    (`ExternalCriticalSupportChallenge.weak_reward_passage, `ExternalCriticalSpaceDraft.WeakRewardPassage),
    (`ExternalCriticalSupportChallenge.rooted_normalization, `ExternalCriticalSpaceDraft.RootedNormalization),
    (`ExternalCriticalSupportChallenge.root_shift_error, `ExternalCriticalSpaceDraft.RootShiftError),
    (`ExternalCriticalSupportChallenge.rooted_stationary_subsequence, `ExternalCriticalSpaceDraft.RootedStationarySubsequence),
    (`ExternalCriticalSupportChallenge.finite_infinity_exclusion, `ExternalCriticalSpaceDraft.FiniteInfinityExclusion),
    (`ExternalCriticalSupportChallenge.gap_packing, `ExternalCriticalSpaceDraft.GapPacking),
    (`ExternalCriticalSupportChallenge.excursion_first_moment, `ExternalCriticalSpaceDraft.ExcursionFirstMoment),
    (`ExternalCriticalSupportChallenge.polynomial_excursion_contradiction, `ExternalCriticalSpaceDraft.PolynomialExcursionContradiction)]
  for (proof, expected) in targets do
    let info ← getConstInfo proof
    unless info.type == mkConst expected do throwError "Frozen type mismatch: {proof}"
    let some raw := (← getConstInfo expected).value? | throwError "Missing expected body"
    liftIO <| IO.println ("CRITICAL_TARGET " ++ (Json.mkObj [
      ("declaration",toJson proof.toString),("expected",toJson expected.toString),
      ("raw_type",toJson (repr info.type).pretty),
      ("raw_expected_proposition",toJson (repr raw).pretty)]).compress)
  let models : Array Name := #[    `ExternalCriticalSpaceDraft.Config,
    `ExternalCriticalSpaceDraft.HasUniformPhase,
    `ExternalCriticalSpaceDraft.Height,
    `ExternalCriticalSpaceDraft.IsStationary,
    `ExternalCriticalSpaceDraft.Phase,
    `ExternalCriticalSpaceDraft.allFinite,
    `ExternalCriticalSpaceDraft.allInfinite,
    `ExternalCriticalSpaceDraft.configBorelSpace,
    `ExternalCriticalSpaceDraft.configMeasurableSpace,
    `ExternalCriticalSpaceDraft.finiteHeightSet,
    `ExternalCriticalSpaceDraft.forbiddenUpwardCylinder,
    `ExternalCriticalSpaceDraft.heightBorelSpace,
    `ExternalCriticalSpaceDraft.heightMeasurableSpace,
    `ExternalCriticalSpaceDraft.heightWeight,
    `ExternalCriticalSpaceDraft.heightWeight._proof_1,
    `ExternalCriticalSpaceDraft.instDecidable_criticalSpaceDefinitions,
    `ExternalCriticalSpaceDraft.localReward,
    `ExternalCriticalSpaceDraft.longExcursion,
    `ExternalCriticalSpaceDraft.lowEvent,
    `ExternalCriticalSpaceDraft.phaseRepresentative,
    `ExternalCriticalSpaceDraft.phaseRepresentative._proof_1,
    `ExternalCriticalSpaceDraft.phaseRotation,
    `ExternalCriticalSpaceDraft.rootedConfig,
    `ExternalCriticalSpaceDraft.rootedConfig._proof_1,
    `ExternalCriticalSpaceDraft.rootedConfig._proof_2,
    `ExternalCriticalSpaceDraft.rootedMeasure,
    `ExternalCriticalSpaceDraft.rootedMeasure._proof_1,
    `ExternalCriticalSpaceDraft.shiftedGap,
    `ExternalCriticalSpaceDraft.successiveGap,
    `ExternalCriticalSpaceDraft.timeShift,
    `ExternalCriticalSpaceDraft.uniformPhase,
    `ExternalCriticalSpaceDraft.uniformPhase._proof_1]
  for name in models do
    let info ← getConstInfo name
    let some idx := env.getModuleIdxFor? name | throwError "Missing model origin"
    let axs ← collectAxioms name
    liftIO <| IO.println ("CRITICAL_MODEL " ++ (Json.mkObj [
      ("declaration",toJson name.toString),("module",toJson env.header.moduleNames[idx.toNat]!.toString),
      ("raw_type",toJson (repr info.type).pretty),("raw_value",toJson (info.value?.map fun raw => (repr raw).pretty)),
      ("axioms",toJson ((axs.map Name.toString).qsort (· < ·)))]).compress)
  let owned : Array Name := #[`PrefixDefinitions, `BridgeDefinitions, `BridgeExpectedTypes, `PressureDefinitions, `PressureExpectedTypes, `CriticalSpaceDefinitions, `CriticalSpaceExpectedTypes, `SpaceTopology, `SpaceArithmetic, `SpaceReward, `PhaseCocycle, `RootedLaw, `WeakReward, `RootedShift, `RootedStationary, `StationaryEvents, `FiniteInfinity, `GapPacking, `ExcursionMoment, `PolynomialContradiction, `CriticalSolution]
  for name in owned do
    unless env.header.moduleNames.contains name do throwError "Owned module omitted: {name}"
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if owned.contains moduleName then
        if let .axiomInfo _ := info then throwError "Custom owned axiom: {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
            throwError "Forbidden axiom {ax} in {name}"
        liftIO <| IO.println ("CRITICAL_SUPPORT " ++ (Json.mkObj [
          ("declaration",toJson name.toString),("module",toJson moduleName.toString),
          ("raw_type",toJson (repr info.type).pretty),
          ("is_theorem",toJson (getOriginalConstKind? env name == some .thm)),
          ("axioms",toJson (axioms.map Name.toString))]).compress)
        count := count+1
  if count == 0 then throwError "Empty owned declaration audit"
  logInfo m!"Audited all {count} owned declaration closures,12 target types and32 model-origin entries (including opaque null bodies)."
