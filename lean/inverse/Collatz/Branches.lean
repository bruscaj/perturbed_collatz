import Std

namespace Collatz

/-- Accelerated Collatz, including T 0 = 0. -/
def T (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- One complete forcing word (+1, 0, -1), starting immediately before +1. -/
def oneLap (n : Nat) : Nat := T (T (T n + 1)) - 1
def twoLaps (n : Nat) : Nat := oneLap (oneLap n)

inductive Phase where
  | plus | coast | minus
  deriving DecidableEq

def Phase.next : Phase → Phase
  | .plus => .coast
  | .coast => .minus
  | .minus => .plus

def impulse : Phase → Int
  | .plus => 1
  | .coast => 0
  | .minus => -1

theorem conservative : impulse .plus + impulse .coast + impulse .minus = 0 := by decide

def step : Phase → Nat → Nat
  | .plus, n => T n + 1
  | .coast, n => T n
  | .minus, n => T n - 1

/-- Zero is safe immediately before the positive impulse. -/
def Safe : Phase → Nat → Prop
  | .plus, _ => True
  | .coast, n => 0 < n
  | .minus, n => 0 < n

theorem T_pos {n : Nat} (h : 0 < n) : 0 < T n := by
  unfold T
  split <;> omega

theorem positive_safe (p : Phase) {n : Nat} (h : 0 < n) : Safe p n := by
  cases p <;> simp [Safe, h]

theorem step_safe (p : Phase) (n : Nat) (h : Safe p n) :
    Safe p.next (step p n) := by
  cases p with
  | plus => exact Nat.zero_lt_succ _
  | coast => exact T_pos h
  | minus => trivial

/-- In safe states the natural-number model agrees with signed integer addition. -/
theorem step_faithful (p : Phase) (n : Nat) (h : Safe p n) :
    (step p n : Int) = (T n : Int) + impulse p := by
  cases p with
  | plus => simp [step, impulse]
  | coast => simp [step, impulse]
  | minus =>
    have hT := T_pos (n := n) h
    change ((T n - 1 : Nat) : Int) = (T n : Int) + (-1)
    omega

def run (s : Phase × Nat) : Nat → Phase × Nat
  | 0 => s
  | k+1 =>
    let z := run s k
    (z.1.next, step z.1 z.2)

theorem run_safe {s : Phase × Nat} (h : Safe s.1 s.2) (k : Nat) :
    Safe (run s k).1 (run s k).2 := by
  induction k with
  | zero => exact h
  | succ k ih => exact step_safe _ _ ih

/-- Every physical step from every positive seed at every starting phase is faithful. -/
theorem admissible (p : Phase) {n : Nat} (hn : 0 < n) (k : Nat) :
    ((run (p,n) (k+1)).2 : Int) =
      (T (run (p,n) k).2 : Int) + impulse (run (p,n) k).1 := by
  exact step_faithful _ _ (run_safe (s := (p,n)) (positive_safe p hn) k)

theorem three_steps (n : Nat) : run (.plus,n) 3 = (.plus,oneLap n) := rfl
theorem six_steps (n : Nat) : run (.plus,n) 6 = (.plus,twoLaps n) := rfl

/-- The roots reach two different cycles at the same sampling phase. -/
theorem root_orbits :
    oneLap 0 = 0 ∧ oneLap 1 = 7 ∧ oneLap 7 = 2 ∧ oneLap 2 = 1 ∧
    oneLap 5 = 6 ∧ oneLap 6 = 0 := by decide

def Good (y : Nat) : Prop := 0 < y ∧ y % 3 ≠ 0

def A (y : Nat) : Nat := 64 * y + 54

/-- Value of the one-odd branch on the least representative of each eligible row. -/
private def rowBase : Nat → Nat
  | 1 => 22 | 2 => 62 | 4 => 86 | 5 => 122 | 7 => 167 | 8 => 190 | _ => 0

def B (y : Nat) : Nat := 192 * (y / 9) + rowBase (y % 9)

private theorem replay {n u v w a b y : Nat}
    (h₁ : T n + 1 = u) (h₂ : T u = v) (h₃ : T v - 1 = w)
    (h₄ : T w + 1 = a) (h₅ : T a = b) (h₆ : T b - 1 = y) : twoLaps n = y := by
  simp only [twoLaps, oneLap, h₁, h₂, h₃, h₄, h₅, h₆]

/-- All-even predecessor for every natural target, including zero. -/
theorem A_parent (y : Nat) : twoLaps (A y) = y := by
  unfold A
  apply replay (u := 32*y+28) (v := 16*y+14) (w := 8*y+6) (a := 4*y+4) (b := 2*y+2)
  all_goals unfold T; split <;> omega

private theorem row1 (q : Nat) : twoLaps (192*q+22) = 9*q+1 := by
  apply replay (u := 96*q+12) (v := 48*q+6) (w := 24*q+2) (a := 12*q+2) (b := 6*q+1)
  all_goals unfold T; split <;> omega

private theorem row2 (q : Nat) : twoLaps (192*q+62) = 9*q+2 := by
  apply replay (u := 96*q+32) (v := 48*q+16) (w := 24*q+7) (a := 36*q+12) (b := 18*q+6)
  all_goals unfold T; split <;> omega

private theorem row4 (q : Nat) : twoLaps (192*q+86) = 9*q+4 := by
  apply replay (u := 96*q+44) (v := 48*q+22) (w := 24*q+10) (a := 12*q+6) (b := 6*q+3)
  all_goals unfold T; split <;> omega

private theorem row5 (q : Nat) : twoLaps (192*q+122) = 9*q+5 := by
  apply replay (u := 96*q+62) (v := 48*q+31) (w := 72*q+46) (a := 36*q+24) (b := 18*q+12)
  all_goals unfold T; split <;> omega

private theorem row7 (q : Nat) : twoLaps (192*q+167) = 9*q+7 := by
  apply replay (u := 288*q+252) (v := 144*q+126) (w := 72*q+62) (a := 36*q+32) (b := 18*q+16)
  all_goals unfold T; split <;> omega

private theorem row8 (q : Nat) : twoLaps (192*q+190) = 9*q+8 := by
  apply replay (u := 96*q+96) (v := 48*q+48) (w := 24*q+23) (a := 36*q+36) (b := 18*q+18)
  all_goals unfold T; split <;> omega

/-- Modulo 9 distinguishes the six targets for which the children branch again. -/
theorem good_residues {y : Nat} (hy : Good y) :
    y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by
  rcases hy with ⟨_, h⟩
  have hmod : y % 9 % 3 = y % 3 := Nat.mod_mod_of_dvd y (by decide : 3 ∣ 9)
  omega

theorem B_parent {y : Nat} (hy : Good y) : twoLaps (B y) = y := by
  rcases good_residues hy with h|h|h|h|h|h
  all_goals simp [B, h, rowBase, row1, row2, row4, row5, row7, row8] <;> omega

theorem A_good {y : Nat} (hy : Good y) : Good (A y) := by
  rcases hy with ⟨hp, hm⟩
  unfold Good A
  omega

theorem A_grow (y : Nat) : y < A y := by unfold A; omega

theorem A_bound (y : Nat) : A y + 1 ≤ 64*(y+1) := by unfold A; omega

private theorem B_properties {y : Nat} (hy : Good y) :
    Good (B y) ∧ y < B y ∧ B y < A y ∧ 3*(B y+1) ≤ 64*(y+1) := by
  rcases good_residues hy with h|h|h|h|h|h
  all_goals simp [Good, A, B, h, rowBase] <;> omega

theorem B_good {y : Nat} (hy : Good y) : Good (B y) := (B_properties hy).1
theorem B_grow {y : Nat} (hy : Good y) : y < B y := (B_properties hy).2.1
theorem B_lt_A {y : Nat} (hy : Good y) : B y < A y := (B_properties hy).2.2.1
theorem B_bound {y : Nat} (hy : Good y) : 3*(B y+1) ≤ 64*(y+1) := (B_properties hy).2.2.2

end Collatz
