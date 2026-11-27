import Lean
import Collatz.SevenStepCertificate
import Collatz.SevenStepCertificate.B1Primitives
import Collatz.SevenStepCertificate.B1Recursive
import Collatz.SevenStepCertificate.B1AllGuards
import Collatz.SevenStepCertificate.RefinedFrontier
import Collatz.SevenStepCertificate.B1FinalObligation
import Collatz.SevenStepCertificate.B1ComplementWitness

#print axioms Collatz.SevenStepCertificate.update_faithful
#print axioms Collatz.SevenStepCertificate.run_faithful
#print axioms Collatz.SevenStepCertificate.phase_six_merger
#print axioms Collatz.SevenStepCertificate.phase_six_signed_merger
#print axioms Collatz.SevenStepCertificate.merger_rank_gap
#print axioms Collatz.SevenStepCertificate.complete_classifier
#print axioms Collatz.SevenStepCertificate.entry_phase_zero
#print axioms Collatz.SevenStepCertificate.section_entry
#print axioms Collatz.SevenStepCertificate.section_capture_of_three
#print axioms Collatz.SevenStepCertificate.global_capture_of_three
#print axioms Collatz.SevenStepCertificate.global_capture_iff_three
#print axioms Collatz.SevenStepCertificate.global_safe_physical_capture_of_three
#print axioms Collatz.SevenStepCertificate.global_physical_capture_of_three

#print axioms Collatz.SevenStepCertificate.even_pump_phase_two
#print axioms Collatz.SevenStepCertificate.ratio_three_TU_merger
#print axioms Collatz.SevenStepCertificate.ratio_three_UU_merger
#print axioms Collatz.SevenStepCertificate.b1_capture_of_ratio_three_meeting

#print axioms Collatz.SevenStepCertificate.iterated_even_pump_phase_two
#print axioms Collatz.SevenStepCertificate.b1_recursive_merger
#print axioms Collatz.SevenStepCertificate.b1_recursive_signed_merger
#print axioms Collatz.SevenStepCertificate.b1_recursive_rank_reduction
#print axioms Collatz.SevenStepCertificate.b1_recursive_capture_transfer

#print axioms Collatz.SevenStepCertificate.b1_all_guards_merger
#print axioms Collatz.SevenStepCertificate.b1_all_guards_signed_merger
#print axioms Collatz.SevenStepCertificate.b1_all_guards_rank_reduction
#print axioms Collatz.SevenStepCertificate.b1_all_guards_capture_transfer
#print axioms Collatz.SevenStepCertificate.b1_guarded_binary_run_merger
#print axioms Collatz.SevenStepCertificate.b1_guarded_binary_run_rank_reduction
#print axioms Collatz.SevenStepCertificate.b1_guarded_binary_run_capture_transfer

#print axioms Collatz.SevenStepCertificate.a3_even_ratio_merger
#print axioms Collatz.SevenStepCertificate.a3_difference_merger
#print axioms Collatz.SevenStepCertificate.a3_two_stage_merger
#print axioms Collatz.SevenStepCertificate.n03_difference_merger
#print axioms Collatz.SevenStepCertificate.n03_two_stage_merger
#print axioms Collatz.SevenStepCertificate.global_capture_iff_refined_frontier
#print axioms Collatz.SevenStepCertificate.b1_ancestor_phase_one
#print axioms Collatz.SevenStepCertificate.global_capture_iff_b1_alone
#print axioms Collatz.SevenStepCertificate.b1_tripling_bridge
#print axioms Collatz.SevenStepCertificate.b1_growth_history
#print axioms Collatz.SevenStepCertificate.b1_shadow_history
#print axioms Collatz.SevenStepCertificate.b1_repayment_strict_parameter_drop
#print axioms Collatz.SevenStepCertificate.b1_repayment_merger
#print axioms Collatz.SevenStepCertificate.b1_repayment_self_progress
#print axioms Collatz.SevenStepCertificate.b1_complement_witness_19
#print axioms Collatz.SevenStepCertificate.global_capture_iff_final_obligation
#print axioms Collatz.SevenStepCertificate.global_safe_physical_capture_of_final_obligation

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if `Collatz.SevenStepCertificate |>.isPrefixOf name then
      if getOriginalConstKind? env name == some .thm then
        let axioms ← collectAxioms name
        for axiomName in axioms do
          unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
            throwError "{name} depends on an unexpected axiom: {axiomName}"
        checked := checked + 1
  if checked == 0 then throwError "No seven-step theorems were checked"
  logInfo m!"Seven-step axiom audit passed for {checked} theorems."
