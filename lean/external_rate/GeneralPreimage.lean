import ExitCylinders

/-! Exact backward dyadic cylinders for one literal odd Syracuse stride. -/
namespace ExternalO3GeneralPreimage
open ExternalO3Spec ExternalO3Arithmetic ExternalO3Cylinders ExternalO3ExitCylinders

/-- Solve every affine target, including residue one excluded by the older helper. -/
theorem affine_dyadic_all (e C : ℕ) (hC : C < 2 ^ e) :
    ∃! d : ℕ, d < 2 ^ e ∧ (3 * d + 2) % 2 ^ e = C := by
  by_cases he : e = 0
  · subst e
    have hc : C = 0 := by simpa using hC
    subst C
    refine ⟨0, by simp, ?_⟩
    intro d hd
    have := hd.1
    simpa using this
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he
  have hm2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he1
  have hm : 2 ^ e ≠ 0 := ne_of_gt (pow_pos (by decide) _)
  have hcop : Nat.Coprime 3 (2 ^ e) := (by decide : Nat.Coprime 3 2).pow_right e
  obtain ⟨d, hd, hmul⟩ := Nat.exists_mul_mod_eq_of_coprime (C + 2 ^ e - 2) hcop hm
  have hsol : (3 * d + 2) % 2 ^ e = C := by
    have hc : Nat.ModEq (2 ^ e) (3 * d) (C + 2 ^ e - 2) := hmul
    have ha := hc.add_right 2
    simpa [Nat.ModEq, Nat.sub_add_cancel (show 2 ≤ C + 2 ^ e by omega),
      Nat.add_mod_right, Nat.mod_eq_of_lt hC] using ha
  refine ⟨d, ⟨hd, hsol⟩, ?_⟩
  rintro d' ⟨hd', hsol'⟩
  have heq := (affine_mod_iff e C d hd hsol d').mp hsol'
  simpa [Nat.mod_eq_of_lt hd'] using heq

theorem lifted_residue_lt (k e d : ℕ) (hk : 1 ≤ k) (hd : d < 2 ^ e) :
    2 ^ (k - 1) * (2 * d + 1) < 2 ^ (k + e) := by
  have hP : 0 < 2 ^ (k - 1) := pow_pos (by decide) _
  have hE : 2 ^ (k + e) = 2 ^ (k - 1) * (2 * 2 ^ e) := by
    rw [show k + e = (k - 1) + (e + 1) by omega, pow_add, pow_succ]
    ring
  rw [hE]
  exact Nat.mul_lt_mul_of_pos_left (by omega) hP

/-- The next odd-seed parameter is existentially encoded, with exact valuation. -/
theorem stride_preimage_mod (k e d n : ℕ) (hk : 1 ≤ k) (hd : d < 2 ^ e) :
    (∃ m : ℕ, strideValuation (2 * n + 1) = k ∧
      stride (2 * n + 1) = 2 * m + 1 ∧ m % 2 ^ e = d) ↔
    (3 * n + 2) % 2 ^ (k + e) = 2 ^ (k - 1) * (2 * d + 1) := by
  let P := 2 ^ (k - 1)
  let Q := 2 ^ e
  have hK : 2 ^ k = 2 * P := by
    have hh := pow_succ (2 : ℕ) (k - 1)
    rw [Nat.sub_add_cancel hk] at hh
    simpa [P, Nat.mul_comm] using hh
  have hM : 2 ^ (k + e) = 2 * P * Q := by rw [pow_add, hK]
  constructor
  · rintro ⟨m, hv, hs, hm⟩
    have hnum : 3 * (2 * n + 1) + 1 = 2 ^ k * (2 * m + 1) := by
      have hh := (Nat.mul_div_cancel'
        (pow_padicValNat_dvd (p := 2) (n := 3 * (2 * n + 1) + 1))).symm
      change 3 * (2 * n + 1) + 1 = 2 ^ strideValuation (2 * n + 1) * stride (2 * n + 1) at hh
      simpa only [hv, hs] using hh
    have hhalf : 3 * n + 2 = P * (2 * m + 1) := by rw [hK] at hnum; nlinarith
    have hmd : m = d + Q * (m / Q) := by
      have hh := Nat.mod_add_div m Q
      change m % Q = d at hm
      rw [hm] at hh
      exact hh.symm
    have he : 3 * n + 2 = P * (2 * d + 1) + 2 ^ (k + e) * (m / Q) := by
      calc 3 * n + 2 = P * (2 * m + 1) := hhalf
           _ = P * (2 * d + 1) + 2 ^ (k + e) * (m / Q) := by
             rw [hM]
             conv_lhs => rw [hmd]
             ring
    rw [he, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (lifted_residue_lt k e d hk hd)
  · intro hc
    let q := (3 * n + 2) / 2 ^ (k + e)
    let m := d + Q * q
    have he : 3 * n + 2 = P * (2 * d + 1) + 2 ^ (k + e) * q := by
      have hh := Nat.mod_add_div (3 * n + 2) (2 ^ (k + e))
      rw [hc] at hh
      exact hh.symm
    have hnum : 3 * (2 * n + 1) + 1 = 2 ^ k * (2 * m + 1) := by
      calc 3 * (2 * n + 1) + 1 = 2 * (3 * n + 2) := by ring
           _ = 2 ^ k * (2 * m + 1) := by rw [he, hK, hM]; dsimp [m]; ring
    have hv : strideValuation (2 * n + 1) = k :=
      (valuation_odd_form _ _ (by omega)).mpr ⟨m, hnum⟩
    have hs : stride (2 * n + 1) = 2 * m + 1 := by
      unfold stride
      rw [hv, hnum, Nat.mul_div_cancel_left _ (pow_pos (by decide) _)]
    refine ⟨m, hv, hs, ?_⟩
    dsimp [m, Q]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

/-- Exact preimage realization for every positive stride valuation. -/
theorem stride_preimage_unique_class (k e d : ℕ) (hk : 1 ≤ k) (hd : d < 2 ^ e) :
    ∃! c : ℕ, c < 2 ^ (k + e) ∧ ∀ n : ℕ,
      (∃ m : ℕ, strideValuation (2 * n + 1) = k ∧
        stride (2 * n + 1) = 2 * m + 1 ∧ m % 2 ^ e = d) ↔
      n % 2 ^ (k + e) = c := by
  obtain ⟨c, ⟨hc, hsol⟩, _⟩ := affine_dyadic_all (k + e)
    (2 ^ (k - 1) * (2 * d + 1)) (lifted_residue_lt k e d hk hd)
  have hevent : ∀ n : ℕ,
      (∃ m : ℕ, strideValuation (2 * n + 1) = k ∧
        stride (2 * n + 1) = 2 * m + 1 ∧ m % 2 ^ e = d) ↔
      n % 2 ^ (k + e) = c := by
    intro n
    rw [stride_preimage_mod k e d n hk hd]
    exact affine_mod_iff (k + e) _ c hc hsol n
  refine ⟨c, ⟨hc, hevent⟩, ?_⟩
  rintro c' ⟨hc', hevent'⟩
  have hh := (hevent c').mp ((hevent' c').mpr (Nat.mod_eq_of_lt hc'))
  simpa [Nat.mod_eq_of_lt hc'] using hh

end ExternalO3GeneralPreimage
