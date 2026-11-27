import Collatz.SevenStepCertificate.B1Primitives

/-! A complete unbounded B1 merger subfamily, proved by induction over the pump count.
The arbitrary natural h is not bounded by a search horizon. This theorem is a
strict reduction to an alternate launch, not an assertion of its capture. -/
namespace Collatz.SevenStepCertificate

/-- Iterate the even fourteen-update pump an arbitrary number of times. -/
theorem iterated_even_pump_phase_two (h a : Nat) :
    run (.p2,16384^h*a) (14*h) = (.p2,59049^h*a) := by
  induction h generalizing a with
  | zero => simp only [Nat.pow_zero, Nat.one_mul, run]
  | succ h ih =>
    have time : 14*(h+1) = 14+14*h := by omega
    have initial : 16384^(h+1)*a = 16384*(16384^h*a) := by
      rw [Nat.pow_succ]
      ac_rfl
    have rearrange : 59049*(16384^h*a) = 16384^h*(59049*a) := by ac_rfl
    have final : 59049^h*(59049*a) = 59049^(h+1)*a := by
      rw [Nat.pow_succ]
      ac_rfl
    have pump : run (.p2,16384*(16384^h*a)) 14 = (.p2,59049*(16384^h*a)) := by
      simpa only [Nat.add_zero] using even_pump_phase_two (16384^h*a)
    rw [time,initial,run_add,pump,rearrange,ih,final]

/-- The terminal U,T,U block merges the ratio-three pair on this odd-part guard. -/
theorem b1_three_step_terminal (r : Nat) (hr : r % 4 = 1) :
    run (.p2,18*r) 3 = run (.p2,6*r) 3 := by
  have small : next (.p2,6*r) = (.p3,9*r) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have large : next (.p2,18*r) = (.p3,27*r) := by
    apply Prod.ext
    · rfl
    · simp only [next,update,U]; split <;> omega
  have x : 9*r = 4*((9*r)/4)+1 := by omega
  have triple : 27*r = 3*(4*((9*r)/4)+1) := by omega
  change run (next (.p2,18*r)) 2 = run (next (.p2,6*r)) 2
  rw [small,large,x,triple]
  exact (ratio_three_TU_merger .p3 ((9*r)/4) (Or.inl rfl)).symm

/-- The exact positive parameter domain of this recursive subfamily. -/
def b1RecursiveParameter (h v : Nat) : Nat := 2^(14*h+1)*(4*v+1)

theorem b1RecursiveParameter_pos (h v : Nat) : 0 < b1RecursiveParameter h v := by
  unfold b1RecursiveParameter
  exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem binary_pump_power (h : Nat) : 2^(14*h+1) = 2*16384^h := by
  rw [Nat.pow_add,Nat.pow_mul]
  change 16384^h*2 = 2*16384^h
  omega

/-- The entire infinite h,v family has a phase-correct meeting at explicit unbounded times. -/
theorem b1_recursive_merger (h v : Nat) :
    run (.p1,6*b1RecursiveParameter h v) (14*h+4) =
      run (.p2,3*b1RecursiveParameter h v) (14*h+3) := by
  let q := 4*v+1
  let r := 59049^h*q
  have parameter : b1RecursiveParameter h v = 2*16384^h*q := by
    unfold b1RecursiveParameter q
    rw [binary_pump_power]
  have small_start : 3*b1RecursiveParameter h v = 16384^h*(6*q) := by
    rw [parameter]
    change 3*(2*16384^h*q) = 16384^h*((3*2)*q)
    ac_rfl
  have large_start : 9*b1RecursiveParameter h v = 16384^h*(18*q) := by
    rw [parameter]
    change 9*(2*16384^h*q) = 16384^h*((9*2)*q)
    ac_rfl
  have small_end : 59049^h*(6*q) = 6*r := by unfold r; ac_rfl
  have large_end : 59049^h*(18*q) = 18*r := by unfold r; ac_rfl
  have small_pump : run (.p2,3*b1RecursiveParameter h v) (14*h) = (.p2,6*r) := by
    rw [small_start,iterated_even_pump_phase_two,small_end]
  have large_pump : run (.p2,9*b1RecursiveParameter h v) (14*h) = (.p2,18*r) := by
    rw [large_start,iterated_even_pump_phase_two,large_end]
  have residue : r % 4 = 1 := by
    have power_residue : 59049^h % 4 = 1 := by
      rw [Nat.pow_mod]
      change 1^h % 4 = 1
      simp
    have odd_residue : q % 4 = 1 := by unfold q; omega
    change (59049^h*q) % 4 = 1
    rw [Nat.mul_mod,power_residue,odd_residue]
  calc
    run (.p1,6*b1RecursiveParameter h v) (14*h+4)
        = run (.p2,9*b1RecursiveParameter h v) (14*h+3) := by
          rw [show 14*h+4 = 1+(14*h+3) by omega,run_add,b1_initial_step]
    _ = run (.p2,18*r) 3 := by rw [run_add,large_pump]
    _ = run (.p2,6*r) 3 := b1_three_step_terminal r residue
    _ = run (.p2,3*b1RecursiveParameter h v) (14*h+3) := by rw [run_add,small_pump]

/-- The unbounded merger is also exact in the signed physical recurrence. -/
theorem b1_recursive_signed_merger (h v : Nat) :
    physicalRun (.p1, ((6*b1RecursiveParameter h v : Nat) : Int)-1) (14*h+4) =
      physicalRun (.p2, ((3*b1RecursiveParameter h v : Nat) : Int)-1) (14*h+3) := by
  have pos := b1RecursiveParameter_pos h v
  have meet := congrArg decode (b1_recursive_merger h v)
  rw [run_faithful (.p1,6*b1RecursiveParameter h v) (by omega),
      run_faithful (.p2,3*b1RecursiveParameter h v) (by omega)] at meet
  simpa only [decode,physical,height,Int.add_zero] using meet

/-- Every member of the unbounded recursive family has a strictly smaller section witness. -/
theorem b1_recursive_rank_reduction (h v : Nat) :
    rank .p2 (b1RecursiveParameter h v) < rank .p1 (2*b1RecursiveParameter h v) :=
  b1_smaller_rank _ (b1RecursiveParameter_pos h v)

/-- Conditional capture transfer uses only the smaller witness, not a global residual assumption. -/
theorem b1_recursive_capture_transfer (h v : Nat)
    (partner : Captured (.p2,3*b1RecursiveParameter h v)) :
    Captured (.p1,6*b1RecursiveParameter h v) :=
  captured_of_coalescence _ _ (14*h+4) (14*h+3) (b1_recursive_merger h v) partner

end Collatz.SevenStepCertificate
