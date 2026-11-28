import Cylinders
import Progressions
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq

/-! Exact exit cylinders for the literal Syracuse map. -/
namespace ExternalO3ExitCylinders
open ExternalO3Spec ExternalO3Arithmetic ExternalO3Cylinders Filter
open scoped Topology

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem exit_residue_lt (a b : ℕ) :
    2 ^ (a + 1) * (2 ^ (b + 1) - 1) < 2 ^ (a + b + 3) := by
  have hP : 0 < 2 ^ (a + 1) := pow_pos (by decide) _
  have hQ : 0 < 2 ^ (b + 1) := pow_pos (by decide) _
  have hM : 2 ^ (a + b + 3) = 2 ^ (a + 1) * (2 * 2 ^ (b + 1)) := by
    rw [show a + b + 3 = (a + 1) + ((b + 1) + 1) by omega, pow_add, pow_succ]
    ring
  rw [hM]
  exact Nat.mul_lt_mul_of_pos_left (by omega) hP

theorem exit_cylinder (a b n : ℕ) :
    strideValuation (2 * n + 1) = a + 2 ∧
      blockLength (stride (2 * n + 1)) = b + 1 ↔
    (3 * n + 2) % 2 ^ (a + b + 3) = 2 ^ (a + 1) * (2 ^ (b + 1) - 1) := by
  let P := 2 ^ (a + 1)
  let Q := 2 ^ (b + 1)
  have hP : 0 < P := pow_pos (by decide) _
  have hQ : 0 < Q := pow_pos (by decide) _
  have hK : 2 ^ (a + 2) = 2 * P := by dsimp [P]; rw [pow_succ]; omega
  have hM : 2 ^ (a + b + 3) = 2 * P * Q := by
    dsimp [P, Q]
    rw [show a + b + 3 = (a + 1) + ((b + 1) + 1) by omega, pow_add, pow_succ]
    ring
  have hsub : Q - 1 + 1 = Q := by omega
  constructor
  · rintro ⟨hk, hr⟩
    have hnum : 3 * (2 * n + 1) + 1 = 2 ^ (a + 2) * stride (2 * n + 1) := by
      rw [← hk]
      exact (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := 3 * (2 * n + 1) + 1))).symm
    have hhalf : 3 * n + 2 = P * stride (2 * n + 1) := by rw [hK] at hnum; nlinarith
    obtain ⟨q, hq⟩ := (valuation_odd_form (stride (2 * n + 1) + 1) (b + 1) (by omega)).mp hr
    change stride (2 * n + 1) + 1 = Q * (2 * q + 1) at hq
    have hy : stride (2 * n + 1) = Q - 1 + 2 * Q * q := by nlinarith
    have he : 3 * n + 2 = P * (Q - 1) + 2 ^ (a + b + 3) * q := by
      rw [hhalf, hy, hM]
      ring
    rw [he, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (exit_residue_lt a b)
  · intro hc
    let q := (3 * n + 2) / 2 ^ (a + b + 3)
    have he : 3 * n + 2 = P * (Q - 1) + 2 ^ (a + b + 3) * q := by
      have hd := Nat.mod_add_div (3 * n + 2) (2 ^ (a + b + 3))
      rw [hc] at hd
      exact hd.symm
    let t := 2 ^ b - 1 + Q * q
    let y := 2 * t + 1
    have hpowb : Q = 2 * 2 ^ b := by dsimp [Q]; rw [pow_succ]; omega
    have hposb : 0 < 2 ^ b := pow_pos (by decide) _
    have hsubb : 2 ^ b - 1 + 1 = 2 ^ b := by omega
    have hy : y = Q - 1 + 2 * Q * q := by dsimp [y, t]; nlinarith
    have hnum : 3 * (2 * n + 1) + 1 = 2 ^ (a + 2) * y := by
      rw [hK, hy, hM] at *
      nlinarith
    have hk : strideValuation (2 * n + 1) = a + 2 := by
      exact (valuation_odd_form _ _ (by omega)).mpr ⟨t, hnum⟩
    have hs : stride (2 * n + 1) = y := by
      unfold stride
      rw [hk, hnum, Nat.mul_div_cancel_left y (pow_pos (by decide) _)]
    refine ⟨hk, ?_⟩
    apply (valuation_odd_form _ _ (by omega)).mpr
    refine ⟨q, ?_⟩
    rw [hs, hy]
    change Q - 1 + 2 * Q * q + 1 = Q * (2 * q + 1)
    nlinarith

theorem affine_mod_iff (e C d : ℕ) (hd : d < 2 ^ e)
    (hsol : (3 * d + 2) % 2 ^ e = C) (n : ℕ) :
    (3 * n + 2) % 2 ^ e = C ↔ n % 2 ^ e = d := by
  have hcop : Nat.Coprime (2 ^ e) 3 := (by decide : Nat.Coprime 2 3).pow_left e
  constructor
  · intro hn
    have hcon : Nat.ModEq (2 ^ e) (3 * n + 2) (3 * d + 2) := hn.trans hsol.symm
    have hmul : Nat.ModEq (2 ^ e) (3 * n) (3 * d) := hcon.add_right_cancel' 2
    have hnd : Nat.ModEq (2 ^ e) n d := hmul.cancel_left_of_coprime hcop
    change n % 2 ^ e = d % 2 ^ e at hnd
    exact hnd.trans (Nat.mod_eq_of_lt hd)
  · intro hn
    have hnd : Nat.ModEq (2 ^ e) n d := hn.trans (Nat.mod_eq_of_lt hd).symm
    have hcon := (hnd.mul_left 3).add_right 2
    change (3 * n + 2) % 2 ^ e = (3 * d + 2) % 2 ^ e at hcon
    exact hcon.trans hsol

theorem affine_dyadic_unique (e C : ℕ) (hC2 : 2 ≤ C) (hC : C < 2 ^ e) :
    ∃! d : ℕ, d < 2 ^ e ∧ (3 * d + 2) % 2 ^ e = C := by
  have hm : 2 ^ e ≠ 0 := ne_of_gt (pow_pos (by decide) _)
  have hcop : Nat.Coprime 3 (2 ^ e) := (by decide : Nat.Coprime 3 2).pow_right e
  obtain ⟨d, hd, hmul⟩ := Nat.exists_mul_mod_eq_of_coprime (C - 2) hcop hm
  have hsol : (3 * d + 2) % 2 ^ e = C := by
    have hcon : Nat.ModEq (2 ^ e) (3 * d) (C - 2) := hmul
    have hadd := hcon.add_right 2
    simpa [Nat.ModEq, Nat.sub_add_cancel hC2, Nat.mod_eq_of_lt hC] using hadd
  refine ⟨d, ⟨hd, hsol⟩, ?_⟩
  rintro d' ⟨hd', hsol'⟩
  have heq := (affine_mod_iff e C d hd hsol d').mp hsol'
  simpa [Nat.mod_eq_of_lt hd'] using heq

theorem exit_residue_ge_two (a b : ℕ) :
    2 ≤ 2 ^ (a + 1) * (2 ^ (b + 1) - 1) := by
  have hpa : 0 < 2 ^ a := pow_pos (by decide) _
  have hpb : 0 < 2 ^ b := pow_pos (by decide) _
  have hP : 2 ≤ 2 ^ (a + 1) := by rw [pow_succ]; omega
  have hQ : 1 ≤ 2 ^ (b + 1) - 1 := by rw [pow_succ]; omega
  exact (Nat.mul_le_mul hP hQ)

/-- The current block is automatically the last stride when its valuation is at least two. -/
theorem exit_current_block_one (a n : ℕ)
    (hk : strideValuation (2 * n + 1) = a + 2) :
    blockLength (2 * n + 1) = 1 := by
  have hx : IsOddSeed (2 * n + 1) := ⟨by omega, by omega⟩
  have hpos := block_length_positive (2 * n + 1) hx
  by_contra hr
  have hlong : 2 ≤ blockLength (2 * n + 1) := by omega
  have hv := valuation_one_of_long_block (2 * n + 1) hx hlong
  omega

/-- Every exact exit event is one uniquely realized seed-parameter residue class. -/
theorem exit_cylinder_unique_class (a b : ℕ) :
    ∃! d : ℕ, d < 2 ^ (a + b + 3) ∧
      ∀ n : ℕ,
        (strideValuation (2 * n + 1) = a + 2 ∧
          blockLength (stride (2 * n + 1)) = b + 1) ↔
        n % 2 ^ (a + b + 3) = d := by
  let C := 2 ^ (a + 1) * (2 ^ (b + 1) - 1)
  obtain ⟨d, ⟨hd, hsol⟩, _⟩ := affine_dyadic_unique (a + b + 3) C
    (exit_residue_ge_two a b) (exit_residue_lt a b)
  have hevent : ∀ n : ℕ,
      (strideValuation (2 * n + 1) = a + 2 ∧
        blockLength (stride (2 * n + 1)) = b + 1) ↔
      n % 2 ^ (a + b + 3) = d := by
    intro n
    rw [exit_cylinder]
    exact affine_mod_iff (a + b + 3) C d hd hsol n
  refine ⟨d, ⟨hd, hevent⟩, ?_⟩
  rintro d' ⟨hd', hevent'⟩
  have he := (hevent d').mp ((hevent' d').mpr (Nat.mod_eq_of_lt hd'))
  simpa [Nat.mod_eq_of_lt hd'] using he

/-- Unconditional relative odd-seed density of the literal two-field exit event. -/
theorem exit_cylinder_density (a b : ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n =>
        strideValuation (2 * n + 1) = a + 2 ∧
          blockLength (stride (2 * n + 1)) = b + 1)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (2 : ℝ) ^ (a + b + 3))) := by
  classical
  obtain ⟨d, ⟨hd, hevent⟩, _⟩ := exit_cylinder_unique_class a b
  have hp : (fun n => strideValuation (2 * n + 1) = a + 2 ∧
      blockLength (stride (2 * n + 1)) = b + 1) =
      (fun n => n % 2 ^ (a + b + 3) = d) := by
    funext n
    exact propext (hevent n)
  simp only [hp]
  exact ExternalO3Progressions.dyadicClass_density (a + b + 3) d hd

end ExternalO3ExitCylinders
