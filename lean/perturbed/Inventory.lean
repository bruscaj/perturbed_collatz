import Lean
import All

open Lean Elab Command

-- These are the named public source theorems; the separate Audit.lean also
-- checks every theorem constant in the project namespaces transitively.
run_cmd do
  let selected : List Name := [
    ``PeriodSevenBasin.child_returns,
    ``PeriodSevenBasin.child_distinct,
    ``PeriodSevenBasin.many_preimages,
    ``PeriodSevenBasin.cycle_targets,
    ``PeriodSevenBasin.many_escaping,
    ``PeriodSevenBasin.not_least_of_meeting,
    ``PeriodSevenBasin.rising_class_reduction,
    ``PerturbedCollatz.step_lift,
    ``PerturbedCollatz.orbit_seed_lift,
    ``PerturbedCollatz.orbit_shift,
    ``PerturbedCollatz.shrinking_stretch_blocks_bounded_returns,
    ``PerturbedCollatz.adaptive_growth,
    ``PerturbedCollatz.reductionSeed_increases,
    ``PerturbedCollatz.reduction_cycle,
    ``PerturbedCollatz.reduction_return,
    ``PerturbedCollatz.unbounded_iff_escape,
    ``PerturbedCollatz.nonperiodic_parity_escapes,
    ``InverseBranch.even_nonneg,
    ``InverseBranch.even_spec,
    ``InverseBranch.odd_spec,
    ``InverseBranch.gate_of_odd_replay,
    ``InverseBranch.gate_or_increase,
    ``InverseBranch.three_laps_gate,
    ``InverseBranch.evenChain_nonneg,
    ``InverseBranch.replay_even,
    ``InverseBranch.padded_preimages,
    ``InverseBranch.three_laps_preimages,
    ``ProgressionSteering.drop_branches,
    ``ProgressionSteering.evenPrefix_affine,
    ``ProgressionSteering.lap_replay,
    ``ProgressionSteering.invariant_all,
    ``ProgressionSteering.exact_choices,
    ``ProgressionSteering.affine_permutation,
    ``ProgressionSteering.crt_lift,
    ``ProgressionSteering.lap_permutations,
    ``ProgressionSteering.lap_projects,
    ``ProgressionSteering.coprime_steering,
    ``ProgressionSteering.target_le_seed,
    ``ProgressionSteering.ternary_word_lift,
    ``ProgressionSteering.admits_sound,
    ``ProgressionSteering.progression_steering,
    ``ResidueTrack.even_forward,
    ``ResidueTrack.odd_forward_iff,
    ``ResidueTrack.odd_spec,
    ``ResidueTrack.odd_preimage_iff_gate,
    ``ResidueTrack.plus_one_pin,
    ``ResidueTrack.Track.start_clear,
    ``ResidueTrack.Track.end_clear,
    ``ResidueTrack.Track.follow,
    ``ResidueTrack.track_of_scan,
    ``ResidueTrack.replay_chain,
    ``ResidueTrack.unique_of_miss,
    ``ResidueTrack.gate_iff_other_preimage,
    ``ResidueTrack.pinned_finish,
    ``ResidueTrack.circular_cons_one,
    ``ResidueTrack.laps_length,
    ``ResidueTrack.Track.append,
    ``ResidueTrack.Track.reverse,
    ``ResidueTrack.circular_reverse,
    ``ResidueTrack.Track.repeat_laps,
    ``ResidueTrack.Track.forever,
    ``ResidueTrack.Track.unique_preimage,
    ``ResidueTrack.hits_append,
    ``ResidueTrack.Track.unique_prefix,
    ``ResidueTrack.chain_mod_iff,
    ``ResidueTrack.miss_three_iff_track,
    ``ResidueTrack.avoid_iff_track,
    ``ResidueTrack.circular_iff_forever,
    ``ResidueTrack.no_track_iff_three,
    ``ResidueTrack.balanced_has_one,
    ``ResidueTrack.balanced_obstruction,
    ``ResidueTrack.three_laps_sharp,
    ``ResidueTrack.balanced_track_example,
    ``ResidueTrack.adjacent_one_odd,
    ``ResidueTrack.adjacent_one_odd_at,
    ``ResidueTrack.displacement_forward,
    ``ResidueTrack.odd_step_threshold,
    ``ResidueTrack.chain_difference,
    ``ResidueTrack.chain_bias_commutation,
    ``TernaryPump.geomSum_add,
    ``TernaryPump.geomSum_triple,
    ``TernaryPump.geomSum_pow_three,
    ``TernaryPump.geomSum_add_pow_three,
    ``TernaryPump.geomSum_step_mod,
    ``TernaryPump.geomSum_lift,
    ``TernaryPump.exists_ge_geomSum_mod]
  for name in selected do
    let info ← getConstInfo name
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
        throwError "{name} depends on an unexpected axiom: {axiomName}"
    let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
    let row := Json.mkObj [("declaration", toJson name.toString),
      ("statement", toJson statement), ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println ("RELEASE_THEOREM " ++ row.compress)
  if selected.isEmpty then throwError "No theorem declarations inventoried"

  -- Module identity includes private and generated theorem declarations.
  -- Checking theorem closures avoids compiler-only auxiliary implementation
  -- constants while rejecting any such axiom if a theorem depends on it.
  let env ← getEnv
  let modules : List Name := [`Collatz, `BasinGrowth, `InverseBranch, `ResidueTrack, `TernaryPump, `ProgressionSteering]
  let mut theorems := 0
  for modName in modules do
    let mut inModule := 0
    for (name, info) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if info.isTheorem then
            for axiomName in (← collectAxioms name) do
              unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
                throwError "{name} depends on an unexpected axiom {axiomName}"
            inModule := inModule + 1
    if inModule == 0 then throwError "No theorem declarations were audited in module {modName}"
    theorems := theorems + inModule
  let summary := Json.mkObj [
    ("theorem_constants_including_private_and_generated", toJson theorems),
    ("modules", toJson (modules.map Name.toString))]
  liftIO <| IO.println ("RELEASE_AUDIT " ++ summary.compress)
