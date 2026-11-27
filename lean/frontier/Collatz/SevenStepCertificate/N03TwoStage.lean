import Collatz.SevenStepCertificate.N03Recursive
import Collatz.SevenStepCertificate.B1AllGuards

/-! One permitted switch from a difference-three pump to a ratio-three pump.
The first stage is never revisited; its counter can reset arbitrarily in the
second stage without invalidating the nested natural-number induction. -/
namespace Collatz.SevenStepCertificate

theorem n03_difference_history (h x q : Nat) (eq : 115*x+702 = 128^h*q) :
    ∃ y, 115*y+702 = 243^h*q ∧
      run (.p3,x) (7*h) = (.p3,y) ∧ run (.p3,x+3) (7*h) = (.p3,y+3) := by
  induction h generalizing x q with
  | zero =>
    refine ⟨x,?_,rfl,rfl⟩
    simpa only [Nat.pow_zero,Nat.one_mul] using eq
  | succ h ih =>
    have eq' : 115*x+702 = 128*(128^h*q) := by
      rw [Nat.pow_succ] at eq
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using eq
    have residue : x % 128 = 54 := by omega
    have expand : x = 128*(x/128)+54 := by omega
    have upper : x+3 = 128*(x/128)+57 := by omega
    let v := x/128
    let nextX := 243*v+108
    have lower : 128^h*q = 115*v+54 := by dsimp [v]; omega
    have next_eq : 115*nextX+702 = 128^h*(243*q) := by
      have rearrange : 128^h*(243*q) = 243*(128^h*q) := by ac_rfl
      rw [rearrange,lower]
      dsimp [nextX]
      omega
    have small : run (.p3,x) 7 = (.p3,nextX) := by
      rw [expand]
      exact n03_difference_pump_small v
    have large : run (.p3,x+3) 7 = (.p3,nextX+3) := by
      rw [upper]
      exact n03_difference_pump_large v
    obtain ⟨y,hy,sy,ly⟩ := ih nextX (243*q) next_eq
    refine ⟨y,?_,?_,?_⟩
    · simpa only [Nat.pow_succ,Nat.mul_assoc] using hy
    · rw [show 7*(h+1) = 7+7*h by omega,run_add,small]
      exact sy
    · rw [show 7*(h+1) = 7+7*h by omega,run_add,large]
      exact ly

theorem iterated_even_pump_phase_one (h a : Nat) :
    run (.p1,16384^h*a) (14*h) = (.p1,59049^h*a) := by
  induction h generalizing a with
  | zero => simp only [Nat.pow_zero,Nat.one_mul,run]
  | succ h ih =>
    have time : 14*(h+1) = 14+14*h := by omega
    have initial : 16384^(h+1)*a = 16384*(16384^h*a) := by rw [Nat.pow_succ]; ac_rfl
    have middle : 59049*(16384^h*a) = 16384^h*(59049*a) := by ac_rfl
    have final : 59049^h*(59049*a) = 59049^(h+1)*a := by rw [Nat.pow_succ]; ac_rfl
    rw [time,initial,run_add,even_pump_phase_one,middle,ih,final]

theorem ratio_three_phase_one_pumped (j w : Nat) :
    run (.p1,16384^j*(4*w+3)) (14*j+2) =
      run (.p1,3*(16384^j*(4*w+3))) (14*j+2) := by
  let tail := 59049^j*(4*w+3)
  have large : 3*(16384^j*(4*w+3)) = 16384^j*(3*(4*w+3)) := by ac_rfl
  have large_end : 59049^j*(3*(4*w+3)) = 3*tail := by dsimp [tail]; ac_rfl
  have small_end : 59049^j*(4*w+3) = tail := rfl
  have residue : tail % 4 = 3 := by
    dsimp [tail]
    rw [Nat.mul_mod,pump_multiplier_mod_four]
    omega
  have decomposition : tail = 4*(tail/4)+3 := by omega
  rw [large,run_add (.p1,16384^j*(4*w+3)) (14*j) 2,
      run_add (.p1,16384^j*(3*(4*w+3))) (14*j) 2,
      iterated_even_pump_phase_one,iterated_even_pump_phase_one,large_end,small_end,decomposition]
  exact ratio_three_UU_merger .p1 (tail/4) (Or.inr (Or.inl rfl))

theorem n03_two_stage_pair (h x q r j w : Nat)
    (entry : 115*x+702 = 128^h*q)
    (exit : 243^h*q = 115*(32*r+3)+702)
    (second : 3*r+1 = 16384^j*(4*w+3)) :
    run (.p3,x) (7*h+14*j+7) = run (.p3,x+3) (7*h+14*j+7) := by
  obtain ⟨y,hy,small,large⟩ := n03_difference_history h x q entry
  have endpoint : y = 32*r+3 := by omega
  rw [endpoint] at small large
  have upper : (32*r+3)+3 = 32*r+6 := by omega
  rw [show 7*h+14*j+7 = 7*h+(5+(14*j+2)) by omega,
      run_add (.p3,x) (7*h) (5+(14*j+2)),
      run_add (.p3,x+3) (7*h) (5+(14*j+2)),small,large,upper,
      run_add (.p3,32*r+3) 5 (14*j+2),n03_difference_ratio_exit_small,
      run_add (.p3,32*r+6) 5 (14*j+2),n03_difference_ratio_exit_large,second]
  exact ratio_three_phase_one_pumped j w

def N03TwoStageGuard (v : Nat) : Prop :=
  ∃ h q r j w, 115*(19683*v+5586)+702 = 128^h*q ∧
    243^h*q = 115*(32*r+3)+702 ∧ 3*r+1 = 16384^j*(4*w+3)

theorem n03_two_stage_merger (v h q r j w : Nat)
    (entry : 115*(19683*v+5586)+702 = 128^h*q)
    (exit : 243^h*q = 115*(32*r+3)+702)
    (second : 3*r+1 = 16384^j*(4*w+3)) :
    run (.p5,3*(8*(512*v+145)+2)) (7*h+14*j+19) =
      run (.p1,3*(3*(512*v+145)+1)) (7*h+14*j+16) := by
  rw [show 7*h+14*j+19 = 12+(7*h+14*j+7) by omega,
      show 7*h+14*j+16 = 9+(7*h+14*j+7) by omega,
      run_add (.p5,3*(8*(512*v+145)+2)) 12 (7*h+14*j+7),n03_difference_source_initialization,
      run_add (.p1,3*(3*(512*v+145)+1)) 9 (7*h+14*j+7),n03_difference_alternate_initialization]
  have upper : 19683*v+5589 = (19683*v+5586)+3 := by omega
  rw [upper]
  exact n03_two_stage_pair h (19683*v+5586) q r j w entry exit second

theorem n03_two_stage_progress (v : Nat) (guard : N03TwoStageGuard v) :
    Progress .p5 (8*(512*v+145)+2) := by
  obtain ⟨h,q,r,j,w,entry,exit,second⟩ := guard
  right
  refine ⟨.p1,3*(512*v+145)+1,7*h+14*j+19,7*h+14*j+16,?_,?_,?_,
    n03_two_stage_merger v h q r j w entry exit second⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank,weight]; omega

end Collatz.SevenStepCertificate
