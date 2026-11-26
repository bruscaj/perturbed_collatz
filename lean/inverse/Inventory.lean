import Lean
import Collatz
import Collatz.ReleaseBridge

open Lean Elab Command

-- These are the named public source theorems; the separate Audit.lean also
-- checks every theorem constant in the project namespaces transitively.
run_cmd do
  let selected : List Name := [
    ``Collatz.Physical.safe_tail,
    ``Collatz.Physical.floor_invariant,
    ``Collatz.Physical.admissible_of_floor,
    ``Collatz.Physical.leastSafe_binary,
    ``Collatz.Physical.leastSafe_le,
    ``Collatz.Physical.leastSafe_floor,
    ``Collatz.Physical.admissible_iff_floor,
    ``Collatz.Physical.gradient_conservative,
    ``Collatz.Physical.floor_gradient,
    ``Collatz.Physical.admissible_conservative_iff_binary_height,
    ``Collatz.Physical.gradient_unit_alphabet,
    ``Collatz.Physical.height_across_zeros,
    ``Collatz.Physical.gradient_alternates,
    ``Collatz.Physical.alternating_admissible,
    ``Collatz.Physical.conservative_admissible_iff_alternating,
    ``Collatz.Physical.coordinate_conjugacy,
    ``Collatz.Physical.safe_iff_above_least,
    ``Collatz.Physical.height_unique,
    ``Collatz.Physical.safe_iff_height,
    ``Collatz.Physical.coordinate_orbit,
    ``Collatz.Physical.coordinate_injective,
    ``Collatz.Physical.cycle_correspondence,
    ``Collatz.Physical.rotation_step,
    ``Collatz.Physical.rotation_orbit,
    ``Collatz.Physical.rotation_onto,
    ``Collatz.Physical.rotation_admissible,
    ``Collatz.Physical.shortcut_lift,
    ``Collatz.Physical.signed_parity_lift,
    ``Collatz.BinaryZoom.even_lap_steps,
    ``Collatz.BinaryZoom.inverse_lap,
    ``Collatz.BinaryZoom.laps_lift,
    ``Collatz.BinaryZoom.lift_affine,
    ``Collatz.BinaryZoom.residue_lt,
    ``Collatz.BinaryZoom.lift_residue,
    ``Collatz.BinaryZoom.run_laps,
    ``Collatz.BinaryZoom.residue_return,
    ``Collatz.conservative,
    ``Collatz.T_pos,
    ``Collatz.positive_safe,
    ``Collatz.step_safe,
    ``Collatz.step_faithful,
    ``Collatz.run_safe,
    ``Collatz.admissible,
    ``Collatz.three_steps,
    ``Collatz.six_steps,
    ``Collatz.root_orbits,
    ``Collatz.A_parent,
    ``Collatz.good_residues,
    ``Collatz.B_parent,
    ``Collatz.A_good,
    ``Collatz.A_grow,
    ``Collatz.A_bound,
    ``Collatz.B_good,
    ``Collatz.B_grow,
    ``Collatz.B_lt_A,
    ``Collatz.B_bound,
    ``Collatz.Coverage.stem_at_least_two,
    ``Collatz.Coverage.stem_spec,
    ``Collatz.Coverage.run_add,
    ``Collatz.Coverage.run_blocks,
    ``Collatz.Coverage.all_phase_preimages,
    ``Collatz.Physical.doubled_coordinate,
    ``Collatz.Physical.gain_succ,
    ``Collatz.Physical.segment_multiplier_bound,
    ``Collatz.Physical.cycle_multiplier_lt_one,
    ``Collatz.Physical.run_add,
    ``Collatz.Physical.reaches_prepend,
    ``Collatz.Physical.target_invariant,
    ``Collatz.Physical.reaches_tail,
    ``Collatz.Physical.coalescence,
    ``Collatz.Physical.reduce_by_rank,
    ``Collatz.ReleaseBridge.global_capture_iff_three,
    ``Collatz.SevenStep.section_entry,
    ``Collatz.SevenStep.smallHit_sound,
    ``Collatz.SevenStep.launch_val,
    ``Collatz.SevenStep.lower_sound,
    ``Collatz.SevenStep.residual_mod,
    ``Collatz.SevenStep.large_descent,
    ``Collatz.SevenStep.section_capture,
    ``Collatz.SevenStep.global_capture_of_three,
    ``Collatz.SevenStep.checked_rows,
    ``Collatz.SevenStep.orbit_phase,
    ``Collatz.SevenStep.Row.sound,
    ``Collatz.SevenStep.partition,
    ``Collatz.SevenStep.parameter_of_applies,
    ``Collatz.SevenStep.increasing_rows,
    ``Collatz.SevenStep.rank_classification,
    ``Collatz.SevenStep.rank_change,
    ``Collatz.SevenStep.finite_captures,
    ``Collatz.SevenStep.sharp_entry,
    ``Collatz.SevenStep.root_cycle,
    ``Collatz.SevenStep.binary_height,
    ``Collatz.SevenStep.height_difference,
    ``Collatz.SevenStep.zero_sum,
    ``Collatz.SevenStep.impulse_primitive,
    ``Collatz.SevenStep.physical_conjugacy,
    ``Collatz.SevenStep.safe_invariant,
    ``Collatz.SevenStep.admissible_word,
    ``Collatz.SevenStep.marked_site,
    ``Collatz.SevenStep.advance_sound,
    ``Collatz.SevenStep.affine_z,
    ``Collatz.SevenStep.affine_mod3,
    ``Collatz.SevenStep.checkHit_sound,
    ``Collatz.Tree.endpoint_good,
    ``Collatz.Tree.endpoint_injective,
    ``Collatz.Tree.endpoint_returns,
    ``Collatz.Tree.endpoint_bound,
    ``Collatz.Tree.endpoint_weighted_bound,
    ``Collatz.Tree.bits_length,
    ``Collatz.Tree.fixed_depth_lower_bound]
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
  let modules : List Name := [`Collatz.Admissibility, `Collatz.BinaryZoom, `Collatz.Branches, `Collatz.Coverage, `Collatz.CycleMultiplier, `Collatz.Physical, `Collatz.ReleaseBridge, `Collatz.SevenFrontier, `Collatz.SevenRows, `Collatz.SevenStep, `Collatz.Tree]
  let mut theorems := 0
  for modName in modules do
    let mut inModule := 0
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if getOriginalConstKind? env name == some .thm then
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
