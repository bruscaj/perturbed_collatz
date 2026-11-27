import All

/-! Small boundary fixtures for the new certificates and their exact interfaces.
These are kernel checks; they are not finite-seed evidence for global capture. -/
open Collatz.SevenStepCertificate

example : run (.p1,6*12) 5 = run (.p1,6*4) 5 := by decide
example : run (.p1,6*960) 12 = run (.p1,6*320) 12 := by decide
example : run (.p1,6*2) 4 ≠ run (.p1,6*(2/3)) 4 := by decide
example : run (.p1,6*3008) 12 ≠ run (.p1,6*(3008/3)) 12 := by decide
example : run (.p2,74) 3 ≠ run (.p2,72) 3 := by decide
example : run (.p3,5586) 5 ≠ run (.p3,5589) 5 := by decide
example : run (.p3,3*(4*116+3)) 9 = run (.p5,3*(3*116+2)) 7 := by decide
example : run (.p3,3*(4*54084+3)) 19 = run (.p5,3*(3*54084+2)) 17 := by decide
example : run (.p3,3*(4*54084+3)) 19 ≠ run (.p5,3*(3*54084+2)) 18 := by decide
example : run (.p5,3*(8*1681+2)) 17 = run (.p1,3*(3*1681+1)) 14 := by decide
example : run (.p1,18) 7 = (.p1,2) := by decide
example : run (.p1,6*11) 7 = (.p1,6) := by decide
example : ¬ B1DirectGuard 17 := by unfold B1DirectGuard; decide
example : ¬ B1ElementaryGuard 0 1 := by unfold B1ElementaryGuard; decide
example : ¬ B1ElementaryGuard 6 3 := by unfold B1ElementaryGuard; decide
example : (3008 : Nat) % 3 ≠ 0 := by decide

example : run (.p1,6*1531812753) 32 = run (.p1,6*613416961) 18 := by decide
example : run (.p1,6*1531812753) 31 ≠ run (.p1,6*613416961) 18 := by decide
example : B1RepaymentGuard 1531812753 := by
  exact ⟨1,7192339568,520,by decide,by decide,by decide,by decide⟩
example : ¬ B1RepaymentGuard 19 := by
  intro guard
  have wrong := b1_repayment_source_residue 19 guard
  omega

example (remaining : B1FinalObligation) (p : Phase) (z : Nat) (hz : 0 < z) :
    Captured (p,z) := global_capture_of_final_obligation remaining p z hz

example (hB1 : B1Obligation) (p : Phase) (z : Nat) (hz : 0 < z) :
    Captured (p,z) := global_capture_of_b1_alone hB1 p z hz

example (hB1 : B1ComplementObligation) (hA3 : A3ComplementObligation)
    (hN03 : N03ComplementObligation) (p : Phase) (z : Nat) (hz : 0 < z) :
    Captured (p,z) := global_capture_of_refined_frontier hB1 hA3 hN03 p z hz

#print axioms Collatz.SevenStepCertificate.global_capture_iff_final_obligation
#print axioms Collatz.SevenStepCertificate.a3_two_stage_merger
#print axioms Collatz.SevenStepCertificate.n03_two_stage_merger
