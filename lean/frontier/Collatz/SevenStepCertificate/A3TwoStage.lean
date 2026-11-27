import Collatz.SevenStepCertificate.A3Recursive

/-! One-way difference-two to ratio-three switching inside even A3.
Two separate unbounded counters are handled by nested induction. -/
namespace Collatz.SevenStepCertificate

theorem a3_difference_history (h u q : Nat) (eq : 115*u+36 = 128^h*q) :
    ∃ v, 115*v+36 = 243^h*q ∧
      run (.p2,243*u+74) (7*h) = (.p2,243*v+74) ∧
      run (.p2,243*u+72) (7*h) = (.p2,243*v+72) := by
  induction h generalizing u q with
  | zero =>
    refine ⟨u,?_,rfl,rfl⟩
    simpa only [Nat.pow_zero,Nat.one_mul] using eq
  | succ h ih =>
    have eq' : 115*u+36 = 128*(128^h*q) := by
      rw [Nat.pow_succ] at eq
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using eq
    have residue : u % 128 = 52 := by omega
    have expand : u = 128*(u/128)+52 := by omega
    let v := u/128
    let nextU := 243*v+99
    have lower : 128^h*q = 115*v+47 := by dsimp [v]; omega
    have next_eq : 115*nextU+36 = 128^h*(243*q) := by
      have rearrange : 128^h*(243*q) = 243*(128^h*q) := by ac_rfl
      rw [rearrange,lower]
      dsimp [nextU]
      omega
    have small : run (.p2,243*u+72) 7 = (.p2,243*nextU+72) := by
      rw [expand]
      exact a3_difference_pump_small v
    have large : run (.p2,243*u+74) 7 = (.p2,243*nextU+74) := by
      rw [expand]
      exact a3_difference_pump_large v
    obtain ⟨v',hv',large',small'⟩ := ih nextU (243*q) next_eq
    refine ⟨v',?_,?_,?_⟩
    · simpa only [Nat.pow_succ,Nat.mul_assoc] using hv'
    · rw [show 7*(h+1) = 7+7*h by omega,run_add,large]
      exact large'
    · rw [show 7*(h+1) = 7+7*h by omega,run_add,small]
      exact small'

theorem iterated_even_pump_phase_five (h a : Nat) :
    run (.p5,16384^h*a) (14*h) = (.p5,59049^h*a) := by
  induction h generalizing a with
  | zero => simp only [Nat.pow_zero,Nat.one_mul,run]
  | succ h ih =>
    have time : 14*(h+1) = 14+14*h := by omega
    have initial : 16384^(h+1)*a = 16384*(16384^h*a) := by rw [Nat.pow_succ]; ac_rfl
    have middle : 59049*(16384^h*a) = 16384^h*(59049*a) := by ac_rfl
    have final : 59049^h*(59049*a) = 59049^(h+1)*a := by rw [Nat.pow_succ]; ac_rfl
    rw [time,initial,run_add,even_pump_phase_five,middle,ih,final]

theorem ratio_three_phase_five_terminal (q : Nat) (hq : q % 4 = 3) :
    run (.p5,6*q) 3 = run (.p5,2*q) 3 := by
  have small : next (.p5,2*q) = (.p6,3*q) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have large : next (.p5,6*q) = (.p6,9*q) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have lower : 3*q = 4*((3*q)/4)+1 := by omega
  have upper : 9*q = 3*(4*((3*q)/4)+1) := by omega
  change run (next (.p5,6*q)) 2 = run (next (.p5,2*q)) 2
  rw [small,large]
  have terminal := (ratio_three_TU_merger .p6 ((3*q)/4) (Or.inr rfl)).symm
  rw [← upper,← lower] at terminal
  exact terminal

theorem ratio_three_phase_five_pumped (j w : Nat) :
    run (.p5,6*(16384^j*(4*w+3))) (14*j+3) =
      run (.p5,2*(16384^j*(4*w+3))) (14*j+3) := by
  let tail := 59049^j*(4*w+3)
  have large : 6*(16384^j*(4*w+3)) = 16384^j*(6*(4*w+3)) := by ac_rfl
  have small : 2*(16384^j*(4*w+3)) = 16384^j*(2*(4*w+3)) := by ac_rfl
  have large_end : 59049^j*(6*(4*w+3)) = 6*tail := by dsimp [tail]; ac_rfl
  have small_end : 59049^j*(2*(4*w+3)) = 2*tail := by dsimp [tail]; ac_rfl
  have residue : tail % 4 = 3 := by
    dsimp [tail]
    rw [Nat.mul_mod,pump_multiplier_mod_four]
    omega
  rw [large,small,
      run_add (.p5,16384^j*(6*(4*w+3))) (14*j) 3,
      run_add (.p5,16384^j*(2*(4*w+3))) (14*j) 3,
      iterated_even_pump_phase_five,iterated_even_pump_phase_five,large_end,small_end]
  exact ratio_three_phase_five_terminal tail residue

theorem a3_two_stage_pair (h u q r j w : Nat)
    (entry : 115*u+36 = 128^h*q)
    (exit : 243^h*q = 115*(8*r+1)+36)
    (second : 243*r+40 = 2*(16384^j*(4*w+3))) :
    run (.p2,243*u+74) (7*h+14*j+6) =
      run (.p2,243*u+72) (7*h+14*j+6) := by
  obtain ⟨v,hv,large,small⟩ := a3_difference_history h u q entry
  have endpoint : v = 8*r+1 := by omega
  rw [endpoint] at small large
  rw [show 7*h+14*j+6 = 7*h+(3+(14*j+3)) by omega,
      run_add (.p2,243*u+74) (7*h) (3+(14*j+3)),
      run_add (.p2,243*u+72) (7*h) (3+(14*j+3)),small,large,
      run_add (.p2,243*(8*r+1)+74) 3 (14*j+3),a3_difference_ratio_exit_large,
      run_add (.p2,243*(8*r+1)+72) 3 (14*j+3),a3_difference_ratio_exit_small,second]
  have shape : 3*(2*(16384^j*(4*w+3))) = 6*(16384^j*(4*w+3)) := by omega
  rw [shape]
  exact ratio_three_phase_five_pumped j w

def A3TwoStageGuard (u : Nat) : Prop :=
  ∃ h q r j w, 115*u+36 = 128^h*q ∧
    243^h*q = 115*(8*r+1)+36 ∧ 243*r+40 = 2*(16384^j*(4*w+3))

theorem a3_two_stage_merger (u h q r j w : Nat)
    (entry : 115*u+36 = 128^h*q)
    (exit : 243^h*q = 115*(8*r+1)+36)
    (second : 243*r+40 = 2*(16384^j*(4*w+3))) :
    run (.p3,3*(4*(16*u+4)+3)) (7*h+14*j+12) =
      run (.p5,3*(3*(16*u+4)+2)) (7*h+14*j+10) := by
  rw [show 7*h+14*j+12 = 6+(7*h+14*j+6) by omega,
      show 7*h+14*j+10 = 4+(7*h+14*j+6) by omega,
      run_add (.p3,3*(4*(16*u+4)+3)) 6 (7*h+14*j+6),a3_difference_source_initialization,
      run_add (.p5,3*(3*(16*u+4)+2)) 4 (7*h+14*j+6),a3_difference_alternate_initialization]
  exact a3_two_stage_pair h u q r j w entry exit second

theorem a3_two_stage_progress (u : Nat) (guard : A3TwoStageGuard u) :
    Progress .p3 (4*(16*u+4)+3) := by
  obtain ⟨h,q,r,j,w,entry,exit,second⟩ := guard
  right
  refine ⟨.p5,3*(16*u+4)+2,7*h+14*j+12,7*h+14*j+10,?_,?_,?_,
    a3_two_stage_merger u h q r j w entry exit second⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank,weight]; omega

end Collatz.SevenStepCertificate
