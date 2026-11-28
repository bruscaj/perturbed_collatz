import Arithmetic
import Progressions
import Mathlib.Tactic.Ring

/-! Literal arithmetic cylinders. No countable-density conclusion is assumed. -/
namespace ExternalO3Cylinders
open ExternalO3Spec
open Filter
open scoped Topology

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem valuation_odd_form (A r : ℕ) (hA : 0 < A) :
    padicValNat 2 A = r ↔ ∃ q : ℕ, A = 2 ^ r * (2 * q + 1) := by
  constructor
  · intro hr
    have hd : 2 ^ r ∣ A := by rw [← hr]; exact pow_padicValNat_dvd
    have hpos : 0 < A / 2 ^ r := Nat.div_pos (Nat.le_of_dvd hA hd) (pow_pos (by decide) _)
    have hv : padicValNat 2 (A / 2 ^ r) = 0 := by
      rw [padicValNat.div_pow hd, hr, Nat.sub_self]
    have hnot : ¬2 ∣ A / 2 ^ r := by
      rcases padicValNat.eq_zero_iff.mp hv with h | h | h
      · omega
      · omega
      · exact h
    have hm : (A / 2 ^ r) % 2 ≠ 0 := by
      intro hz
      exact hnot (Nat.dvd_of_mod_eq_zero hz)
    have heq : A / 2 ^ r = 2 * ((A / 2 ^ r) / 2) + 1 := by omega
    refine ⟨(A / 2 ^ r) / 2, ?_⟩
    calc
      A = 2 ^ r * (A / 2 ^ r) := (Nat.mul_div_cancel' hd).symm
      _ = 2 ^ r * (2 * ((A / 2 ^ r) / 2) + 1) :=
        congrArg (fun t : ℕ => 2 ^ r * t) heq
  · rintro ⟨q, rfl⟩
    have hnot : ¬2 ∣ 2 * q + 1 := by
      intro hd
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [padicValNat_base_pow_mul (by decide) (by omega)]
    simp [padicValNat.eq_zero_of_not_dvd hnot]

theorem ascending_cylinder (a n : ℕ) :
    blockLength (2 * n + 1) = a + 2 ↔
      n % 2 ^ (a + 2) = 2 ^ (a + 1) - 1 := by
  have hb : blockLength (2 * n + 1) = padicValNat 2 (n + 1) + 1 := by
    unfold blockLength
    have hn : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [hn, padicValNat_base_mul (by decide) (by omega)]
  rw [hb]
  have hv : padicValNat 2 (n + 1) + 1 = a + 2 ↔ padicValNat 2 (n + 1) = a + 1 := by omega
  rw [hv, valuation_odd_form (n + 1) (a + 1) (by omega)]
  have hp : 0 < 2 ^ (a + 1) := pow_pos (by decide) _
  have hpow : 2 ^ (a + 2) = 2 ^ (a + 1) * 2 := by
    rw [show a + 2 = (a + 1) + 1 by omega, pow_succ]
  have hlt : 2 ^ (a + 1) - 1 < 2 ^ (a + 2) := by rw [hpow]; omega
  constructor
  · rintro ⟨q, hq⟩
    have he : 2 ^ (a + 1) * (2 * q + 1) =
        2 ^ (a + 2) * q + 2 ^ (a + 1) := by rw [hpow]; ring
    rw [he] at hq
    have hn : n = (2 ^ (a + 1) - 1) + 2 ^ (a + 2) * q := by omega
    rw [hn, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hlt
  · intro hm
    refine ⟨n / 2 ^ (a + 2), ?_⟩
    calc
      n + 1 = 2 ^ (a + 2) * (n / 2 ^ (a + 2)) + 2 ^ (a + 1) := by
        have h := Nat.mod_add_div n (2 ^ (a + 2))
        rw [hm] at h
        omega
      _ = 2 ^ (a + 1) * (2 * (n / 2 ^ (a + 2)) + 1) := by rw [hpow]; ring

theorem ascending_residue_lt (a : ℕ) : 2 ^ (a + 1) - 1 < 2 ^ (a + 2) := by
  have hp : 0 < 2 ^ (a + 1) := pow_pos (by decide) _
  rw [show a + 2 = (a + 1) + 1 by omega, pow_succ]
  omega

theorem ascending_density (a : ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => blockLength (2 * n + 1) = a + 2)).card : ℝ) /
        (N : ℝ)) atTop (𝓝 (1 / (2 : ℝ) ^ (a + 2))) := by
  simpa only [ascending_cylinder] using
    ExternalO3Progressions.dyadicClass_density (a + 2)
      (2 ^ (a + 1) - 1) (ascending_residue_lt a)

end ExternalO3Cylinders
