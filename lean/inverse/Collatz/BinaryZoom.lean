import Collatz.Coverage

/-! Exact inverse copies of every phase-zero orbit in nested binary residue classes. -/
namespace Collatz.BinaryZoom

/-- Append the three low bits 110 once per level. -/
def lift : Nat → Nat → Nat
  | 0, n => n
  | h+1, n => 8 * lift h n + 6

/-- Apply the same phase-zero return h times. -/
def laps : Nat → Nat → Nat
  | 0, n => n
  | h+1, n => laps h (oneLap n)

theorem even_lap_steps (n : Nat) :
    T (8*n+6) + 1 = 4*n+4 ∧ T (4*n+4) = 2*n+2 ∧ T (2*n+2) = n+1 := by
  constructor
  · unfold T; split <;> omega
  constructor <;> unfold T <;> split <;> omega

theorem inverse_lap (n : Nat) : oneLap (8*n+6) = n := by
  obtain ⟨hp, hc, hm⟩ := even_lap_steps n
  simp [oneLap, hp, hc, hm]

theorem laps_lift (h n : Nat) : laps h (lift h n) = n := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change laps h (oneLap (8 * lift h n + 6)) = n
    rw [inverse_lap, ih]

theorem lift_affine (h n : Nat) : lift h n = 8^h*n + lift h 0 := by
  induction h with
  | zero => simp [lift]
  | succ h ih =>
    have power : 8^(h+1)*n = 8*(8^h*n) := by
      rw [Nat.pow_succ]
      ac_rfl
    change 8 * lift h n + 6 = 8^(h+1)*n + (8 * lift h 0 + 6)
    rw [power, ih, Nat.mul_add]
    omega

theorem residue_lt (h : Nat) : lift h 0 < 8^h := by
  induction h with
  | zero => decide
  | succ h ih =>
    change 8 * lift h 0 + 6 < 8^(h+1)
    rw [Nat.pow_succ]
    omega

theorem lift_residue (h n : Nat) : lift h n % 8^h = lift h 0 := by
  rw [lift_affine, Nat.mul_add_mod, Nat.mod_eq_of_lt (residue_lt h)]

theorem run_laps (h n : Nat) : run (.plus,n) (3*h) = (.plus, laps h n) := by
  induction h generalizing n with
  | zero => rfl
  | succ h ih =>
    rw [show 3*(h+1) = 3+3*h by omega, Coverage.run_add, three_steps, ih]
    rfl

/-- Every member of the binary cylinder recovers its high digits after exactly
3h physical steps, with its original forcing phase. -/
theorem residue_return (h n : Nat) (hr : n % 8^h = lift h 0) :
    run (.plus,n) (3*h) = (.plus, n / 8^h) := by
  have he : n = lift h (n / 8^h) := by
    rw [lift_affine, ← hr, Nat.add_comm]
    exact (Nat.mod_add_div n (8^h)).symm
  rw [run_laps]
  exact congrArg (fun m => (Phase.plus, m))
    ((congrArg (laps h) he).trans (laps_lift h (n / 8^h)))

end Collatz.BinaryZoom
