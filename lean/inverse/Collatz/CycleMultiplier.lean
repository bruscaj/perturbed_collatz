import Collatz.Admissibility

namespace Collatz.Physical

/-- Count physical odd branches among the first k ticks of the forced orbit. -/
def oddCount (w : Word) (s : State w) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k+1 => oddCount w (step w s) k + (if s.2%2 = 0 then 0 else 1)

/-- Exact one-tick factor and nonnegative remainder, including signed n. -/
theorem doubled_coordinate (w : Word) (h : Clock w → Int) (b : Binary h)
    (g : Gradient w h) (s : State w) :
    2*coordinate h (step w s) = parityFactor s.2 * coordinate h s + coordinate h s%2 := by
  change 2*(shortcut s.2 + w.impulse s.1 + 1-h (s.1+1)) =
    parityFactor s.2*(s.2+1-h s.1) + (s.2+1-h s.1)%2
  rw [g]
  unfold shortcut parityFactor
  have binary := b s.1
  split <;> omega

theorem gain_succ (w : Word) (s : State w) (k : Nat) :
    (3:Int)^oddCount w s (k+1) = 3^oddCount w (step w s) k * parityFactor s.2 := by
  rw [oddCount]; unfold parityFactor
  split <;> simp [Int.pow_succ]

theorem segment_multiplier_bound (w : Word) (h : Clock w → Int) (b : Binary h)
    (g : Gradient w h) (s : State w) (k : Nat) :
    (3:Int)^oddCount w s k * coordinate h s ≤
      2^k * coordinate h (run (step w) k s) := by
  induction k generalizing s with
  | zero => simp [oddCount,run]
  | succ k ih =>
    let a : Int := 3^oddCount w (step w s) k
    let z := coordinate h s
    let next := coordinate h (step w s)
    let last := coordinate h (run (step w) k (step w s))
    have one := doubled_coordinate w h b g s
    have stepBound : parityFactor s.2*z ≤ 2*next := by
      change 2*next = parityFactor s.2*z + z%2 at one
      omega
    have aPos : 0 < a := Int.pow_pos (by decide)
    have oneScaled := Int.mul_le_mul_of_nonneg_left stepBound (Int.le_of_lt aPos)
    have rest : a*next ≤ 2^k * last := ih (step w s)
    rw [gain_succ, Int.pow_succ]
    change (a*parityFactor s.2)*z ≤ (2^k*2)*last
    calc
      (a*parityFactor s.2)*z = a*(parityFactor s.2*z) := Int.mul_assoc ..
      _ ≤ a*(2*next) := oneScaled
      _ = 2*(a*next) := Int.mul_left_comm ..
      _ ≤ 2*(2^k*last) := Int.mul_le_mul_of_nonneg_left rest (by decide)
      _ = (2^k*2)*last := by ac_rfl

private theorem odd_power (k : Nat) : (3:Int)^k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ, Int.mul_emod, ih]; decide

/-- Every nonempty physical return on the safe domain satisfies the strict arithmetic
    cycle-multiplier inequality. The word can have arbitrary signed integer entries. -/
theorem cycle_multiplier_lt_one (w : Word) (ad : Admissible w) (c : Conservative w)
    (s : State w) (safe : Safe w s) (k : Nat) (nonempty : 0 < k)
    (cycle : run (step w) k s = s) : (3:Int)^oddCount w s k < 2^k := by
  let h := leastSafe w
  have bound := segment_multiplier_bound w h (leastSafe_binary w)
    (floor_gradient w c h (leastSafe_floor w ad)) s k
  rw [cycle] at bound
  have hz : 0 < coordinate h s := by
    have := leastSafe_le w s safe; dsimp [coordinate,h]; omega
  have le := Int.le_of_mul_le_mul_right bound hz
  have odd := odd_power (oddCount w s k)
  cases k with
  | zero => contradiction
  | succ k =>
    have even : (2:Int)^(k+1)%2 = 0 := by rw [Int.pow_succ]; omega
    omega

end Collatz.Physical
