import Collatz.SevenStepCertificate.B1Recursive
import Collatz.SevenStepCertificate.B1Terminals

/-! Full unbounded merger certification for all ten elementary B1 binary-run guards.
The guard predicate is explicit and exhaustive for this rule. It is not a claim
that these guards exhaust the entire B1 family. -/
namespace Collatz.SevenStepCertificate

/-- The ten accepted valuation and odd-part residues of the elementary B1 rule. -/
def B1ElementaryGuard (r c : Nat) : Prop :=
  (r = 1 ∧ c = 1) ∨ (r = 2 ∧ c = 3) ∨ (r = 4 ∧ c = 1) ∨
  (r = 5 ∧ c = 3) ∨ (r = 6 ∧ c = 1) ∨ (r = 8 ∧ c = 3) ∨
  (r = 9 ∧ c = 1) ∨ (r = 11 ∧ c = 3) ∨ (r = 12 ∧ c = 1) ∨
  (r = 13 ∧ c = 3)

theorem b1_guard_properties (r c : Nat) (guard : B1ElementaryGuard r c) :
    1 ≤ r ∧ r < 14 ∧ 0 < c ∧ c < 4 := by
  unfold B1ElementaryGuard at guard
  omega

/-- All ten residual finite blocks are checked on their complete affine domains. -/
theorem b1_all_finite_terminals (r c v : Nat) (guard : B1ElementaryGuard r c) :
    run (.p2,9*(2^r*(4*v+c))) (r+2) = run (.p2,3*(2^r*(4*v+c))) (r+2) := by
  rcases guard with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact b1_terminal_1_1 v
  · exact b1_terminal_2_3 v
  · exact b1_terminal_4_1 v
  · exact b1_terminal_5_3 v
  · exact b1_terminal_6_1 v
  · exact b1_terminal_8_3 v
  · exact b1_terminal_9_1 v
  · exact b1_terminal_11_3 v
  · exact b1_terminal_12_1 v
  · exact b1_terminal_13_3 v

theorem b1_all_terminal_residues (r c q : Nat) (guard : B1ElementaryGuard r c)
    (hq : q % 4 = c) :
    run (.p2,9*(2^r*q)) (r+2) = run (.p2,3*(2^r*q)) (r+2) := by
  have decomposition : q = 4*(q/4)+c := by omega
  rw [decomposition]
  exact b1_all_finite_terminals r c (q/4) guard

def b1GuardedParameter (h r c v : Nat) : Nat := 2^(14*h+r)*(4*v+c)

theorem b1GuardedParameter_pos (h r c v : Nat) (guard : B1ElementaryGuard r c) :
    0 < b1GuardedParameter h r c v := by
  have conditions := b1_guard_properties r c guard
  unfold b1GuardedParameter
  exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem binary_pump_power_general (h r : Nat) : 2^(14*h+r) = 16384^h*2^r := by
  rw [Nat.pow_add,Nat.pow_mul]

theorem pump_multiplier_mod_four (h : Nat) : 59049^h % 4 = 1 := by
  rw [Nat.pow_mod]
  change 1^h % 4 = 1
  simp

/-- Arbitrarily many pumps followed by any one of the ten exact terminal blocks. -/
theorem b1_all_guards_merger (h r c v : Nat) (guard : B1ElementaryGuard r c) :
    run (.p1,6*b1GuardedParameter h r c v) (14*h+r+3) =
      run (.p2,3*b1GuardedParameter h r c v) (14*h+r+2) := by
  let q := 4*v+c
  let tail := 59049^h*q
  have conditions := b1_guard_properties r c guard
  have parameter : b1GuardedParameter h r c v = 16384^h*2^r*q := by
    unfold b1GuardedParameter q
    rw [binary_pump_power_general]
  have small_start : 3*b1GuardedParameter h r c v = 16384^h*(3*(2^r*q)) := by
    rw [parameter]
    ac_rfl
  have large_start : 9*b1GuardedParameter h r c v = 16384^h*(9*(2^r*q)) := by
    rw [parameter]
    ac_rfl
  have small_end : 59049^h*(3*(2^r*q)) = 3*(2^r*tail) := by unfold tail; ac_rfl
  have large_end : 59049^h*(9*(2^r*q)) = 9*(2^r*tail) := by unfold tail; ac_rfl
  have small_pump : run (.p2,3*b1GuardedParameter h r c v) (14*h) = (.p2,3*(2^r*tail)) := by
    rw [small_start,iterated_even_pump_phase_two,small_end]
  have large_pump : run (.p2,9*b1GuardedParameter h r c v) (14*h) = (.p2,9*(2^r*tail)) := by
    rw [large_start,iterated_even_pump_phase_two,large_end]
  have residue : tail % 4 = c := by
    have q_residue : q % 4 = c := by unfold q; omega
    change (59049^h*q) % 4 = c
    rw [Nat.mul_mod,pump_multiplier_mod_four,q_residue,Nat.one_mul]
    exact Nat.mod_eq_of_lt conditions.2.2.2
  calc
    run (.p1,6*b1GuardedParameter h r c v) (14*h+r+3)
        = run (.p2,9*b1GuardedParameter h r c v) (14*h+(r+2)) := by
          rw [show 14*h+r+3 = 1+(14*h+(r+2)) by omega,run_add,b1_initial_step]
    _ = run (.p2,9*(2^r*tail)) (r+2) := by rw [run_add,large_pump]
    _ = run (.p2,3*(2^r*tail)) (r+2) := b1_all_terminal_residues r c tail guard residue
    _ = run (.p2,3*b1GuardedParameter h r c v) (14*h+r+2) := by
          rw [show 14*h+r+2 = 14*h+(r+2) by omega,
              run_add (.p2,3*b1GuardedParameter h r c v) (14*h) (r+2),small_pump]

/-- Every accepted unbounded guard family has a strictly smaller section witness. -/
theorem b1_all_guards_rank_reduction (h r c v : Nat) (guard : B1ElementaryGuard r c) :
    rank .p2 (b1GuardedParameter h r c v) < rank .p1 (2*b1GuardedParameter h r c v) :=
  b1_smaller_rank _ (b1GuardedParameter_pos h r c v guard)

/-- Exact phase-correct merger in the signed physical recurrence, with safe positivity. -/
theorem b1_all_guards_signed_merger (h r c v : Nat) (guard : B1ElementaryGuard r c) :
    physicalRun (.p1, ((6*b1GuardedParameter h r c v : Nat) : Int)-1) (14*h+r+3) =
      physicalRun (.p2, ((3*b1GuardedParameter h r c v : Nat) : Int)-1) (14*h+r+2) := by
  have pos := b1GuardedParameter_pos h r c v guard
  have meet := congrArg decode (b1_all_guards_merger h r c v guard)
  rw [run_faithful (.p1,6*b1GuardedParameter h r c v) (by omega),
      run_faithful (.p2,3*b1GuardedParameter h r c v) (by omega)] at meet
  simpa only [decode,physical,height,Int.add_zero] using meet

/-- Capture transfer assumes only capture of the strictly smaller alternate launch. -/
theorem b1_all_guards_capture_transfer (h r c v : Nat) (guard : B1ElementaryGuard r c)
    (partner : Captured (.p2,3*b1GuardedParameter h r c v)) :
    Captured (.p1,6*b1GuardedParameter h r c v) :=
  captured_of_coalescence _ _ (14*h+r+3) (14*h+r+2) (b1_all_guards_merger h r c v guard) partner

/-- Quotient/remainder parameters recover every input of the stated binary-run form. -/
theorem b1GuardedParameter_quotients (k q : Nat) :
    b1GuardedParameter (k/14) (k%14) (q%4) (q/4) = 2^k*q := by
  have exponent : 14*(k/14)+k%14 = k := by omega
  have odd_part : 4*(q/4)+q%4 = q := by omega
  unfold b1GuardedParameter
  rw [exponent,odd_part]

/-- Direct formulation on the valuation and odd-part residue guard; no bounded k is assumed. -/
theorem b1_guarded_binary_run_merger (k q : Nat)
    (guard : B1ElementaryGuard (k%14) (q%4)) :
    run (.p1,6*(2^k*q)) (k+3) = run (.p2,3*(2^k*q)) (k+2) := by
  have exponent : 14*(k/14)+k%14 = k := by omega
  have meet := b1_all_guards_merger (k/14) (k%14) (q%4) (q/4) guard
  simpa only [b1GuardedParameter_quotients,exponent] using meet

theorem b1_guarded_binary_run_rank_reduction (k q : Nat)
    (guard : B1ElementaryGuard (k%14) (q%4)) :
    rank .p2 (2^k*q) < rank .p1 (2*(2^k*q)) := by
  simpa only [b1GuardedParameter_quotients] using
    b1_all_guards_rank_reduction (k/14) (k%14) (q%4) (q/4) guard

theorem b1_guarded_binary_run_capture_transfer (k q : Nat)
    (guard : B1ElementaryGuard (k%14) (q%4)) (partner : Captured (.p2,3*(2^k*q))) :
    Captured (.p1,6*(2^k*q)) :=
  captured_of_coalescence _ _ (k+3) (k+2) (b1_guarded_binary_run_merger k q guard) partner

end Collatz.SevenStepCertificate
