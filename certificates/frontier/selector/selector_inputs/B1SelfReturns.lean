import Collatz.SevenStepCertificate.B1Entry

/-! Whole affine one-period B1 self-descents. Generated from the
separately checked 28-row physical certificate. -/

namespace Collatz.SevenStepCertificate

def B1SelfProgress (t : Nat) : Prop :=
  Captured (.p1,6*t) ∨
  ∃ s a b, 0 < s ∧ s < t ∧ run (.p1,6*t) a = run (.p1,6*s) b

def B1DirectGuard (t : Nat) : Prop :=
  t % 128 = 9 ∨ t % 128 = 11 ∨ t % 128 = 12 ∨ t % 128 = 13 ∨ t % 128 = 25 ∨ t % 128 = 27 ∨ t % 128 = 28 ∨ t % 128 = 31 ∨ t % 128 = 36 ∨ t % 128 = 45 ∨ t % 128 = 47 ∨ t % 128 = 51 ∨ t % 128 = 52 ∨ t % 128 = 55 ∨ t % 128 = 61 ∨ t % 128 = 66 ∨ t % 128 = 69 ∨ t % 128 = 71 ∨ t % 128 = 82 ∨ t % 128 = 83 ∨ t % 128 = 85 ∨ t % 128 = 99 ∨ t % 128 = 104 ∨ t % 128 = 107 ∨ t % 128 = 108 ∨ t % 128 = 120 ∨ t % 128 = 123 ∨ t % 128 = 127

theorem b1_direct_return_9 (t : Nat) :
    run (.p1, 6*(128*t+9)) 7 = (.p1, 6*(81*t+6)) := by
  have h0 : next (.p1, 6*(128*t+9)) = (.p2, 1152*t+81) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+81) = (.p3, 576*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+41) = (.p4, 864*t+62) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+62) = (.p5, 1296*t+93) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+93) = (.p6, 648*t+47) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+47) = (.p0, 972*t+71) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 972*t+71) = (.p1, 6*(81*t+6)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_9 (t : Nat) : B1SelfProgress (128*t+9) := by
  right
  refine ⟨81*t+6,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_9 t

theorem b1_direct_return_11 (t : Nat) :
    run (.p1, 6*(128*t+11)) 7 = (.p1, 6*(9*t+1)) := by
  have h0 : next (.p1, 6*(128*t+11)) = (.p2, 1152*t+99) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+99) = (.p3, 576*t+50) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+50) = (.p4, 288*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+25) = (.p5, 144*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+13) = (.p6, 72*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 72*t+7) = (.p0, 108*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 108*t+11) = (.p1, 6*(9*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_11 (t : Nat) : B1SelfProgress (128*t+11) := by
  right
  refine ⟨9*t+1,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_11 t

theorem b1_direct_return_12 (t : Nat) :
    run (.p1, 6*(128*t+12)) 7 = (.p1, 6*(81*t+8)) := by
  have h0 : next (.p1, 6*(128*t+12)) = (.p2, 1152*t+108) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+108) = (.p3, 1728*t+162) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+162) = (.p4, 864*t+81) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+81) = (.p5, 432*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+41) = (.p6, 216*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+21) = (.p0, 324*t+32) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+32) = (.p1, 6*(81*t+8)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_12 (t : Nat) : B1SelfProgress (128*t+12) := by
  right
  refine ⟨81*t+8,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_12 t

theorem b1_direct_return_13 (t : Nat) :
    run (.p1, 6*(128*t+13)) 7 = (.p1, 6*(27*t+3)) := by
  have h0 : next (.p1, 6*(128*t+13)) = (.p2, 1152*t+117) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+117) = (.p3, 576*t+59) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+59) = (.p4, 864*t+89) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+89) = (.p5, 432*t+45) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+45) = (.p6, 216*t+23) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+23) = (.p0, 324*t+35) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+35) = (.p1, 6*(27*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_13 (t : Nat) : B1SelfProgress (128*t+13) := by
  right
  refine ⟨27*t+3,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_13 t

theorem b1_direct_return_25 (t : Nat) :
    run (.p1, 6*(128*t+25)) 7 = (.p1, 6*(81*t+16)) := by
  have h0 : next (.p1, 6*(128*t+25)) = (.p2, 1152*t+225) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+225) = (.p3, 576*t+113) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+113) = (.p4, 864*t+170) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+170) = (.p5, 1296*t+255) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+255) = (.p6, 648*t+128) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+128) = (.p0, 324*t+64) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+64) = (.p1, 6*(81*t+16)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_25 (t : Nat) : B1SelfProgress (128*t+25) := by
  right
  refine ⟨81*t+16,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_25 t

theorem b1_direct_return_27 (t : Nat) :
    run (.p1, 6*(128*t+27)) 7 = (.p1, 6*(9*t+2)) := by
  have h0 : next (.p1, 6*(128*t+27)) = (.p2, 1152*t+243) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+243) = (.p3, 576*t+122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+122) = (.p4, 288*t+61) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+61) = (.p5, 144*t+31) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+31) = (.p6, 72*t+16) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 72*t+16) = (.p0, 36*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 36*t+8) = (.p1, 6*(9*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_27 (t : Nat) : B1SelfProgress (128*t+27) := by
  right
  refine ⟨9*t+2,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_27 t

theorem b1_direct_return_28 (t : Nat) :
    run (.p1, 6*(128*t+28)) 7 = (.p1, 6*(27*t+6)) := by
  have h0 : next (.p1, 6*(128*t+28)) = (.p2, 1152*t+252) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+252) = (.p3, 1728*t+378) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+378) = (.p4, 864*t+189) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+189) = (.p5, 432*t+95) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+95) = (.p6, 216*t+48) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+48) = (.p0, 108*t+24) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 108*t+24) = (.p1, 6*(27*t+6)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_28 (t : Nat) : B1SelfProgress (128*t+28) := by
  right
  refine ⟨27*t+6,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_28 t

theorem b1_direct_return_31 (t : Nat) :
    run (.p1, 6*(128*t+31)) 7 = (.p1, 6*(81*t+20)) := by
  have h0 : next (.p1, 6*(128*t+31)) = (.p2, 1152*t+279) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+279) = (.p3, 576*t+140) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+140) = (.p4, 288*t+70) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+70) = (.p5, 432*t+105) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+105) = (.p6, 216*t+53) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+53) = (.p0, 324*t+80) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+80) = (.p1, 6*(81*t+20)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_31 (t : Nat) : B1SelfProgress (128*t+31) := by
  right
  refine ⟨81*t+20,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_31 t

theorem b1_direct_return_36 (t : Nat) :
    run (.p1, 6*(128*t+36)) 7 = (.p1, 6*(81*t+23)) := by
  have h0 : next (.p1, 6*(128*t+36)) = (.p2, 1152*t+324) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+324) = (.p3, 1728*t+486) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+486) = (.p4, 864*t+243) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+243) = (.p5, 432*t+122) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+122) = (.p6, 648*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+183) = (.p0, 972*t+275) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 972*t+275) = (.p1, 6*(81*t+23)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_36 (t : Nat) : B1SelfProgress (128*t+36) := by
  right
  refine ⟨81*t+23,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_36 t

theorem b1_direct_return_45 (t : Nat) :
    run (.p1, 6*(128*t+45)) 7 = (.p1, 6*(81*t+29)) := by
  have h0 : next (.p1, 6*(128*t+45)) = (.p2, 1152*t+405) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+405) = (.p3, 576*t+203) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+203) = (.p4, 864*t+305) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+305) = (.p5, 432*t+153) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+153) = (.p6, 216*t+77) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+77) = (.p0, 324*t+116) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+116) = (.p1, 6*(81*t+29)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_45 (t : Nat) : B1SelfProgress (128*t+45) := by
  right
  refine ⟨81*t+29,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_45 t

theorem b1_direct_return_47 (t : Nat) :
    run (.p1, 6*(128*t+47)) 7 = (.p1, 6*(27*t+10)) := by
  have h0 : next (.p1, 6*(128*t+47)) = (.p2, 1152*t+423) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+423) = (.p3, 576*t+212) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+212) = (.p4, 288*t+106) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+106) = (.p5, 432*t+159) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+159) = (.p6, 216*t+80) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+80) = (.p0, 108*t+40) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 108*t+40) = (.p1, 6*(27*t+10)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_47 (t : Nat) : B1SelfProgress (128*t+47) := by
  right
  refine ⟨27*t+10,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_47 t

theorem b1_direct_return_51 (t : Nat) :
    run (.p1, 6*(128*t+51)) 7 = (.p1, 6*(27*t+11)) := by
  have h0 : next (.p1, 6*(128*t+51)) = (.p2, 1152*t+459) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+459) = (.p3, 576*t+230) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+230) = (.p4, 288*t+115) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+115) = (.p5, 144*t+58) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+58) = (.p6, 216*t+87) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+87) = (.p0, 324*t+131) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+131) = (.p1, 6*(27*t+11)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_51 (t : Nat) : B1SelfProgress (128*t+51) := by
  right
  refine ⟨27*t+11,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_51 t

theorem b1_direct_return_52 (t : Nat) :
    run (.p1, 6*(128*t+52)) 7 = (.p1, 6*(81*t+33)) := by
  have h0 : next (.p1, 6*(128*t+52)) = (.p2, 1152*t+468) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+468) = (.p3, 1728*t+702) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+702) = (.p4, 864*t+351) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+351) = (.p5, 432*t+176) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+176) = (.p6, 648*t+264) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+264) = (.p0, 324*t+132) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+132) = (.p1, 6*(81*t+33)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_52 (t : Nat) : B1SelfProgress (128*t+52) := by
  right
  refine ⟨81*t+33,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_52 t

theorem b1_direct_return_55 (t : Nat) :
    run (.p1, 6*(128*t+55)) 7 = (.p1, 6*(81*t+35)) := by
  have h0 : next (.p1, 6*(128*t+55)) = (.p2, 1152*t+495) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+495) = (.p3, 576*t+248) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+248) = (.p4, 288*t+124) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+124) = (.p5, 432*t+186) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+186) = (.p6, 648*t+279) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+279) = (.p0, 972*t+419) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 972*t+419) = (.p1, 6*(81*t+35)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_55 (t : Nat) : B1SelfProgress (128*t+55) := by
  right
  refine ⟨81*t+35,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_55 t

theorem b1_direct_return_61 (t : Nat) :
    run (.p1, 6*(128*t+61)) 7 = (.p1, 6*(27*t+13)) := by
  have h0 : next (.p1, 6*(128*t+61)) = (.p2, 1152*t+549) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+549) = (.p3, 576*t+275) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+275) = (.p4, 864*t+413) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+413) = (.p5, 432*t+207) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+207) = (.p6, 216*t+104) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+104) = (.p0, 108*t+52) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 108*t+52) = (.p1, 6*(27*t+13)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_61 (t : Nat) : B1SelfProgress (128*t+61) := by
  right
  refine ⟨27*t+13,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_61 t

theorem b1_direct_return_66 (t : Nat) :
    run (.p1, 6*(128*t+66)) 7 = (.p1, 6*(81*t+42)) := by
  have h0 : next (.p1, 6*(128*t+66)) = (.p2, 1152*t+594) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+594) = (.p3, 1728*t+891) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+891) = (.p4, 2592*t+1337) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 2592*t+1337) = (.p5, 1296*t+669) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+669) = (.p6, 648*t+335) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+335) = (.p0, 972*t+503) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 972*t+503) = (.p1, 6*(81*t+42)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_66 (t : Nat) : B1SelfProgress (128*t+66) := by
  right
  refine ⟨81*t+42,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_66 t

theorem b1_direct_return_69 (t : Nat) :
    run (.p1, 6*(128*t+69)) 7 = (.p1, 6*(81*t+44)) := by
  have h0 : next (.p1, 6*(128*t+69)) = (.p2, 1152*t+621) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+621) = (.p3, 576*t+311) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+311) = (.p4, 864*t+467) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+467) = (.p5, 432*t+234) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+234) = (.p6, 648*t+351) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+351) = (.p0, 972*t+527) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 972*t+527) = (.p1, 6*(81*t+44)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_69 (t : Nat) : B1SelfProgress (128*t+69) := by
  right
  refine ⟨81*t+44,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_69 t

theorem b1_direct_return_71 (t : Nat) :
    run (.p1, 6*(128*t+71)) 7 = (.p1, 6*(81*t+45)) := by
  have h0 : next (.p1, 6*(128*t+71)) = (.p2, 1152*t+639) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+639) = (.p3, 576*t+320) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+320) = (.p4, 288*t+160) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+160) = (.p5, 432*t+240) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+240) = (.p6, 648*t+360) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+360) = (.p0, 324*t+180) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+180) = (.p1, 6*(81*t+45)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_71 (t : Nat) : B1SelfProgress (128*t+71) := by
  right
  refine ⟨81*t+45,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_71 t

theorem b1_direct_return_82 (t : Nat) :
    run (.p1, 6*(128*t+82)) 7 = (.p1, 6*(81*t+52)) := by
  have h0 : next (.p1, 6*(128*t+82)) = (.p2, 1152*t+738) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+738) = (.p3, 1728*t+1107) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+1107) = (.p4, 2592*t+1661) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 2592*t+1661) = (.p5, 1296*t+831) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+831) = (.p6, 648*t+416) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+416) = (.p0, 324*t+208) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+208) = (.p1, 6*(81*t+52)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_82 (t : Nat) : B1SelfProgress (128*t+82) := by
  right
  refine ⟨81*t+52,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_82 t

theorem b1_direct_return_83 (t : Nat) :
    run (.p1, 6*(128*t+83)) 7 = (.p1, 6*(81*t+53)) := by
  have h0 : next (.p1, 6*(128*t+83)) = (.p2, 1152*t+747) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+747) = (.p3, 576*t+374) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+374) = (.p4, 288*t+187) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+187) = (.p5, 144*t+94) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+94) = (.p6, 216*t+141) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+141) = (.p0, 324*t+212) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+212) = (.p1, 6*(81*t+53)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_83 (t : Nat) : B1SelfProgress (128*t+83) := by
  right
  refine ⟨81*t+53,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_83 t

theorem b1_direct_return_85 (t : Nat) :
    run (.p1, 6*(128*t+85)) 7 = (.p1, 6*(81*t+54)) := by
  have h0 : next (.p1, 6*(128*t+85)) = (.p2, 1152*t+765) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+765) = (.p3, 576*t+383) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+383) = (.p4, 864*t+575) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+575) = (.p5, 432*t+288) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+288) = (.p6, 648*t+432) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+432) = (.p0, 324*t+216) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+216) = (.p1, 6*(81*t+54)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_85 (t : Nat) : B1SelfProgress (128*t+85) := by
  right
  refine ⟨81*t+54,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_85 t

theorem b1_direct_return_99 (t : Nat) :
    run (.p1, 6*(128*t+99)) 7 = (.p1, 6*(27*t+21)) := by
  have h0 : next (.p1, 6*(128*t+99)) = (.p2, 1152*t+891) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+891) = (.p3, 576*t+446) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+446) = (.p4, 288*t+223) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+223) = (.p5, 144*t+112) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+112) = (.p6, 216*t+168) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+168) = (.p0, 108*t+84) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 108*t+84) = (.p1, 6*(27*t+21)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_99 (t : Nat) : B1SelfProgress (128*t+99) := by
  right
  refine ⟨27*t+21,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_99 t

theorem b1_direct_return_104 (t : Nat) :
    run (.p1, 6*(128*t+104)) 7 = (.p1, 6*(81*t+66)) := by
  have h0 : next (.p1, 6*(128*t+104)) = (.p2, 1152*t+936) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+936) = (.p3, 1728*t+1404) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+1404) = (.p4, 864*t+702) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+702) = (.p5, 1296*t+1053) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+1053) = (.p6, 648*t+527) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+527) = (.p0, 972*t+791) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 972*t+791) = (.p1, 6*(81*t+66)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_104 (t : Nat) : B1SelfProgress (128*t+104) := by
  right
  refine ⟨81*t+66,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_104 t

theorem b1_direct_return_107 (t : Nat) :
    run (.p1, 6*(128*t+107)) 7 = (.p1, 6*(27*t+23)) := by
  have h0 : next (.p1, 6*(128*t+107)) = (.p2, 1152*t+963) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+963) = (.p3, 576*t+482) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+482) = (.p4, 288*t+241) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+241) = (.p5, 144*t+121) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+121) = (.p6, 72*t+61) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 72*t+61) = (.p0, 108*t+92) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 108*t+92) = (.p1, 6*(27*t+23)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_107 (t : Nat) : B1SelfProgress (128*t+107) := by
  right
  refine ⟨27*t+23,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_107 t

theorem b1_direct_return_108 (t : Nat) :
    run (.p1, 6*(128*t+108)) 7 = (.p1, 6*(27*t+23)) := by
  have h0 : next (.p1, 6*(128*t+108)) = (.p2, 1152*t+972) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+972) = (.p3, 1728*t+1458) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+1458) = (.p4, 864*t+729) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+729) = (.p5, 432*t+365) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+365) = (.p6, 216*t+183) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+183) = (.p0, 324*t+275) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+275) = (.p1, 6*(27*t+23)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_108 (t : Nat) : B1SelfProgress (128*t+108) := by
  right
  refine ⟨27*t+23,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_108 t

theorem b1_direct_return_120 (t : Nat) :
    run (.p1, 6*(128*t+120)) 7 = (.p1, 6*(81*t+76)) := by
  have h0 : next (.p1, 6*(128*t+120)) = (.p2, 1152*t+1080) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+1080) = (.p3, 1728*t+1620) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 1728*t+1620) = (.p4, 864*t+810) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+810) = (.p5, 1296*t+1215) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+1215) = (.p6, 648*t+608) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 648*t+608) = (.p0, 324*t+304) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+304) = (.p1, 6*(81*t+76)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_120 (t : Nat) : B1SelfProgress (128*t+120) := by
  right
  refine ⟨81*t+76,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_120 t

theorem b1_direct_return_123 (t : Nat) :
    run (.p1, 6*(128*t+123)) 7 = (.p1, 6*(3*t+3)) := by
  have h0 : next (.p1, 6*(128*t+123)) = (.p2, 1152*t+1107) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+1107) = (.p3, 576*t+554) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+554) = (.p4, 288*t+277) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+277) = (.p5, 144*t+139) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 144*t+139) = (.p6, 72*t+70) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 72*t+70) = (.p0, 36*t+35) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 36*t+35) = (.p1, 6*(3*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_123 (t : Nat) : B1SelfProgress (128*t+123) := by
  right
  refine ⟨3*t+3,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_123 t

theorem b1_direct_return_127 (t : Nat) :
    run (.p1, 6*(128*t+127)) 7 = (.p1, 6*(27*t+27)) := by
  have h0 : next (.p1, 6*(128*t+127)) = (.p2, 1152*t+1143) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+1143) = (.p3, 576*t+572) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+572) = (.p4, 288*t+286) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 288*t+286) = (.p5, 432*t+429) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 432*t+429) = (.p6, 216*t+215) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 216*t+215) = (.p0, 324*t+323) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 324*t+323) = (.p1, 6*(27*t+27)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem b1_direct_progress_127 (t : Nat) : B1SelfProgress (128*t+127) := by
  right
  refine ⟨27*t+27,7,0,by omega,by omega,?_⟩
  exact b1_direct_return_127 t

theorem b1_direct_self_progress (t : Nat) (guard : B1DirectGuard t) :
    B1SelfProgress t := by
  rcases guard with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h

  · have eq : t = 128*(t/128)+9 := by omega
    rw [eq]
    exact b1_direct_progress_9 (t/128)

  · have eq : t = 128*(t/128)+11 := by omega
    rw [eq]
    exact b1_direct_progress_11 (t/128)

  · have eq : t = 128*(t/128)+12 := by omega
    rw [eq]
    exact b1_direct_progress_12 (t/128)

  · have eq : t = 128*(t/128)+13 := by omega
    rw [eq]
    exact b1_direct_progress_13 (t/128)

  · have eq : t = 128*(t/128)+25 := by omega
    rw [eq]
    exact b1_direct_progress_25 (t/128)

  · have eq : t = 128*(t/128)+27 := by omega
    rw [eq]
    exact b1_direct_progress_27 (t/128)

  · have eq : t = 128*(t/128)+28 := by omega
    rw [eq]
    exact b1_direct_progress_28 (t/128)

  · have eq : t = 128*(t/128)+31 := by omega
    rw [eq]
    exact b1_direct_progress_31 (t/128)

  · have eq : t = 128*(t/128)+36 := by omega
    rw [eq]
    exact b1_direct_progress_36 (t/128)

  · have eq : t = 128*(t/128)+45 := by omega
    rw [eq]
    exact b1_direct_progress_45 (t/128)

  · have eq : t = 128*(t/128)+47 := by omega
    rw [eq]
    exact b1_direct_progress_47 (t/128)

  · have eq : t = 128*(t/128)+51 := by omega
    rw [eq]
    exact b1_direct_progress_51 (t/128)

  · have eq : t = 128*(t/128)+52 := by omega
    rw [eq]
    exact b1_direct_progress_52 (t/128)

  · have eq : t = 128*(t/128)+55 := by omega
    rw [eq]
    exact b1_direct_progress_55 (t/128)

  · have eq : t = 128*(t/128)+61 := by omega
    rw [eq]
    exact b1_direct_progress_61 (t/128)

  · have eq : t = 128*(t/128)+66 := by omega
    rw [eq]
    exact b1_direct_progress_66 (t/128)

  · have eq : t = 128*(t/128)+69 := by omega
    rw [eq]
    exact b1_direct_progress_69 (t/128)

  · have eq : t = 128*(t/128)+71 := by omega
    rw [eq]
    exact b1_direct_progress_71 (t/128)

  · have eq : t = 128*(t/128)+82 := by omega
    rw [eq]
    exact b1_direct_progress_82 (t/128)

  · have eq : t = 128*(t/128)+83 := by omega
    rw [eq]
    exact b1_direct_progress_83 (t/128)

  · have eq : t = 128*(t/128)+85 := by omega
    rw [eq]
    exact b1_direct_progress_85 (t/128)

  · have eq : t = 128*(t/128)+99 := by omega
    rw [eq]
    exact b1_direct_progress_99 (t/128)

  · have eq : t = 128*(t/128)+104 := by omega
    rw [eq]
    exact b1_direct_progress_104 (t/128)

  · have eq : t = 128*(t/128)+107 := by omega
    rw [eq]
    exact b1_direct_progress_107 (t/128)

  · have eq : t = 128*(t/128)+108 := by omega
    rw [eq]
    exact b1_direct_progress_108 (t/128)

  · have eq : t = 128*(t/128)+120 := by omega
    rw [eq]
    exact b1_direct_progress_120 (t/128)

  · have eq : t = 128*(t/128)+123 := by omega
    rw [eq]
    exact b1_direct_progress_123 (t/128)

  · have eq : t = 128*(t/128)+127 := by omega
    rw [eq]
    exact b1_direct_progress_127 (t/128)

end Collatz.SevenStepCertificate
