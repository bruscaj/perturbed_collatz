import Collatz.SevenStepCertificate.FrontierIdentities
import Collatz.SevenStepCertificate.B1AllGuards

/-! Two unbounded merger rules inside the previously unresolved even A3 branch.
The recursion counters are binary valuations of explicit affine coordinates;
neither proof assumes decreasing trajectory height. -/
namespace Collatz.SevenStepCertificate

theorem ratio_nine_phase_two_terminal (q : Nat) (hq : q % 32 = 13 ∨ q % 32 = 15) :
    run (.p2,9*(64*q)) 11 = run (.p2,64*q) 11 := by
  rcases hq with hq | hq
  · have eq : q = 32*(q/32)+13 := by omega
    rw [eq]
    exact ratio_nine_p2_terminal_13 (q/32)
  · have eq : q = 32*(q/32)+15 := by omega
    rw [eq]
    exact ratio_nine_p2_terminal_15 (q/32)

theorem ratio_nine_phase_two_pumped (h q : Nat)
    (hq : (59049^h*q) % 32 = 13 ∨ (59049^h*q) % 32 = 15) :
    run (.p2,9*(2^(14*h+6)*q)) (14*h+11) =
      run (.p2,2^(14*h+6)*q) (14*h+11) := by
  have power : 2^(14*h+6) = 16384^h*64 := binary_pump_power_general h 6
  have small : 2^(14*h+6)*q = 16384^h*(64*q) := by rw [power]; ac_rfl
  have large : 9*(2^(14*h+6)*q) = 16384^h*(9*(64*q)) := by rw [power]; ac_rfl
  have small_end : 59049^h*(64*q) = 64*(59049^h*q) := by ac_rfl
  have large_end : 59049^h*(9*(64*q)) = 9*(64*(59049^h*q)) := by ac_rfl
  rw [large,small,
      run_add (.p2,16384^h*(9*(64*q))) (14*h) 11,
      run_add (.p2,16384^h*(64*q)) (14*h) 11,
      iterated_even_pump_phase_two,iterated_even_pump_phase_two,small_end,large_end]
  exact ratio_nine_phase_two_terminal (59049^h*q) hq

def A3EvenRatioGuard (u : Nat) : Prop :=
  ∃ h q, 81*u+65 = 2^(14*h+6)*q ∧
    ((59049^h*q) % 32 = 13 ∨ (59049^h*q) % 32 = 15)

theorem a3_even_ratio_merger (u h q : Nat)
    (eq : 81*u+65 = 2^(14*h+6)*q)
    (hq : (59049^h*q) % 32 = 13 ∨ (59049^h*q) % 32 = 15) :
    run (.p3,3*(4*(16*u+12)+3)) (14*h+17) =
      run (.p5,3*(3*(16*u+12)+2)) (14*h+15) := by
  rw [show 14*h+17 = 6+(14*h+11) by omega,
      show 14*h+15 = 4+(14*h+11) by omega,
      run_add (.p3,3*(4*(16*u+12)+3)) 6 (14*h+11), a3_even_source_initialization,
      run_add (.p5,3*(3*(16*u+12)+2)) 4 (14*h+11), a3_even_alternate_initialization, eq]
  exact ratio_nine_phase_two_pumped h q hq

theorem a3_even_ratio_progress (u : Nat) (guard : A3EvenRatioGuard u) :
    Progress .p3 (4*(16*u+12)+3) := by
  obtain ⟨h,q,eq,hq⟩ := guard
  right
  refine ⟨.p5,3*(16*u+12)+2,14*h+17,14*h+15,?_,?_,?_,a3_even_ratio_merger u h q eq hq⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank,weight]; omega

theorem a3_difference_terminal (u : Nat) (hu : u % 8 = 7) :
    run (.p2,243*u+74) 3 = run (.p2,243*u+72) 3 := by
  have eq : u = 8*(u/8)+7 := by omega
  rw [eq,a3_difference_terminal_large,a3_difference_terminal_small]

/-- A seven-step difference-two block consumes seven exact binary factors.
The affine progress coordinate is C=115*u+36, transformed to 243*C/128. -/
theorem a3_difference_repeated (h u q : Nat)
    (eq : 115*u+36 = 128^h*q) (terminal : (243^h*q) % 8 = 1) :
    run (.p2,243*u+74) (7*h+3) = run (.p2,243*u+72) (7*h+3) := by
  induction h generalizing u q with
  | zero =>
    simp only [Nat.pow_zero,Nat.one_mul] at eq terminal
    have hu : u % 8 = 7 := by omega
    exact a3_difference_terminal u hu
  | succ h ih =>
    have eq' : 115*u+36 = 128*(128^h*q) := by
      rw [Nat.pow_succ] at eq
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using eq
    have residue : u % 128 = 52 := by omega
    have expand : u = 128*(u/128)+52 := by omega
    let v := u/128
    let nextU := 243*v+99
    have lower : 128^h*q = 115*v+47 := by
      dsimp [v]
      omega
    have next_eq : 115*nextU+36 = 128^h*(243*q) := by
      have rearrange : 128^h*(243*q) = 243*(128^h*q) := by ac_rfl
      rw [rearrange,lower]
      dsimp [nextU]
      omega
    have next_terminal : (243^h*(243*q)) % 8 = 1 := by
      rw [Nat.pow_succ] at terminal
      simpa only [Nat.mul_assoc] using terminal
    have large : run (.p2,243*u+74) 7 = (.p2,243*nextU+74) := by
      rw [expand]
      exact a3_difference_pump_large v
    have small : run (.p2,243*u+72) 7 = (.p2,243*nextU+72) := by
      rw [expand]
      exact a3_difference_pump_small v
    rw [show 7*(h+1)+3 = 7+(7*h+3) by omega,
        run_add (.p2,243*u+74) 7 (7*h+3),
        run_add (.p2,243*u+72) 7 (7*h+3),large,small]
    exact ih nextU (243*q) next_eq next_terminal

def A3DifferenceGuard (u : Nat) : Prop :=
  ∃ h q, 115*u+36 = 128^h*q ∧ (243^h*q) % 8 = 1

theorem a3_difference_merger (u h q : Nat)
    (eq : 115*u+36 = 128^h*q) (terminal : (243^h*q) % 8 = 1) :
    run (.p3,3*(4*(16*u+4)+3)) (7*h+9) =
      run (.p5,3*(3*(16*u+4)+2)) (7*h+7) := by
  rw [show 7*h+9 = 6+(7*h+3) by omega,
      show 7*h+7 = 4+(7*h+3) by omega,
      run_add (.p3,3*(4*(16*u+4)+3)) 6 (7*h+3),a3_difference_source_initialization,
      run_add (.p5,3*(3*(16*u+4)+2)) 4 (7*h+3),a3_difference_alternate_initialization]
  exact a3_difference_repeated h u q eq terminal

theorem a3_difference_progress (u : Nat) (guard : A3DifferenceGuard u) :
    Progress .p3 (4*(16*u+4)+3) := by
  obtain ⟨h,q,eq,terminal⟩ := guard
  right
  refine ⟨.p5,3*(16*u+4)+2,7*h+9,7*h+7,?_,?_,?_,a3_difference_merger u h q eq terminal⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank,weight]; omega

end Collatz.SevenStepCertificate
