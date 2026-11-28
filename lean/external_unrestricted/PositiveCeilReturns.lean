import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
Positive natural ceiling returns for an arbitrary irrational real slope.
The proof starts with Dirichlet's signed error k*α-j. Negative errors are
doubled. Positive errors are multiplied by floor(1/error), putting the product
strictly below the next integer; irrationality excludes equality. Every return
index constructed is a natural number at least two. No signed dense-orbit
argument, equidistribution premise or source-specific irrationality is used.
-/
namespace ExternalO3PositiveCeilReturns

/-- An integer less than one above x must be its ceiling. -/
theorem ceil_of_small_positive_gap (x : ℝ) (z : ℤ)
    (hpos : 0 < (z : ℝ) - x) (hsmall : (z : ℝ) - x < 1) :
    Int.ceil x = z := by
  apply Int.ceil_eq_iff.mpr
  constructor <;> linarith

/-- Convert either sign of a small irrational approximation into a positive
natural return from below an integer. -/
theorem signed_approximation_to_ceiling (α ε : ℝ) (hα : Irrational α)
    (_hε : 0 < ε) (k : ℕ) (hk : 0 < k) (j : ℤ)
    (hsmall : |(k : ℝ) * α - (j : ℝ)| < min (ε / 2) (1 / 8)) :
    ∃ r : ℕ, 2 ≤ r ∧
      0 < (Int.ceil ((r : ℝ) * α) : ℝ) - (r : ℝ) * α ∧
      (Int.ceil ((r : ℝ) * α) : ℝ) - (r : ℝ) * α < ε := by
  let e : ℝ := (k : ℝ) * α - (j : ℝ)
  have hene : e ≠ 0 :=
    sub_ne_zero.mpr ((hα.natCast_mul (ne_of_gt hk)).ne_int j)
  have habε : |e| < ε / 2 := hsmall.trans_le (min_le_left _ _)
  have hab8 : |e| < (1 : ℝ) / 8 := hsmall.trans_le (min_le_right _ _)
  rcases lt_or_gt_of_ne hene with he | he
  · rw [abs_of_neg he] at habε hab8
    have hgap : ((2 * j : ℤ) : ℝ) - ((2 * k : ℕ) : ℝ) * α = -2 * e := by
      dsimp [e]
      push_cast
      ring
    have hpos : 0 < ((2 * j : ℤ) : ℝ) - ((2 * k : ℕ) : ℝ) * α := by
      rw [hgap]
      linarith
    have hlt : ((2 * j : ℤ) : ℝ) - ((2 * k : ℕ) : ℝ) * α < 1 := by
      rw [hgap]
      linarith
    have hceil := ceil_of_small_positive_gap (((2 * k : ℕ) : ℝ) * α) (2 * j) hpos hlt
    refine ⟨2 * k, by omega, ?_, ?_⟩
    · simpa only [hceil] using hpos
    · rw [hceil, hgap]
      linarith
  · rw [abs_of_pos he] at habε hab8
    let m : ℕ := Nat.floor (1 / e)
    have hrecip : 0 ≤ (1 : ℝ) / e := (one_div_pos.mpr he).le
    have htwo : (2 : ℝ) ≤ 1 / e := (le_div_iff₀ he).mpr (by linarith)
    have hm : 2 ≤ m := (Nat.le_floor_iff hrecip).mpr htwo
    have hme : (m : ℝ) * e ≤ 1 :=
      (le_div_iff₀ he).mp (Nat.floor_le hrecip)
    have hfloor : 1 / e < (m : ℝ) + 1 := Nat.lt_floor_add_one (1 / e)
    have hme_lower : 1 - e < (m : ℝ) * e := by
      have h := (div_lt_iff₀ he).mp hfloor
      nlinarith
    have hr : 2 ≤ m * k := by
      simpa using Nat.mul_le_mul hm hk
    have hneq : (m : ℝ) * e ≠ 1 := by
      intro heq
      apply ((hα.natCast_mul (m := m * k) (by omega)).ne_int
        ((m : ℤ) * j + 1))
      simp only [Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one]
      dsimp [e] at heq
      nlinarith
    have hme_lt : (m : ℝ) * e < 1 := by
      rcases lt_or_eq_of_le hme with h | h
      · exact h
      · exact False.elim (hneq h)
    have hgap : (((m : ℤ) * j + 1 : ℤ) : ℝ) - ((m * k : ℕ) : ℝ) * α =
        1 - (m : ℝ) * e := by
      dsimp [e]
      push_cast
      ring
    have hpos : 0 < (((m : ℤ) * j + 1 : ℤ) : ℝ) - ((m * k : ℕ) : ℝ) * α := by
      rw [hgap]
      linarith
    have hlt : (((m : ℤ) * j + 1 : ℤ) : ℝ) - ((m * k : ℕ) : ℝ) * α < 1 := by
      rw [hgap]
      linarith
    have hceil := ceil_of_small_positive_gap (((m * k : ℕ) : ℝ) * α)
      ((m : ℤ) * j + 1) hpos hlt
    refine ⟨m * k, hr, ?_, ?_⟩
    · simpa only [hceil] using hpos
    · rw [hceil, hgap]
      linarith

/-- Every irrational slope has arbitrarily small strictly positive ceiling
gaps at natural indices at least two. -/
theorem exists_positive_ceil_gap (α : ℝ) (hα : Irrational α) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, 2 ≤ r ∧
      0 < (Int.ceil ((r : ℝ) * α) : ℝ) - (r : ℝ) * α ∧
      (Int.ceil ((r : ℝ) * α) : ℝ) - (r : ℝ) * α < ε := by
  let η : ℝ := min (ε / 2) (1 / 8)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  let N : ℕ := n + 1
  have hN : 0 < N := by omega
  have hden : (n : ℝ) + 1 ≤ (N : ℝ) + 1 := by
    dsimp [N]
    push_cast
    linarith
  have hbound : (1 : ℝ) / ((N : ℝ) + 1) < η :=
    (one_div_le_one_div_of_le (by positivity) hden).trans_lt hn
  obtain ⟨k, hk, _, happ⟩ := Real.exists_nat_abs_mul_sub_round_le α hN
  exact signed_approximation_to_ceiling α ε hα hε k hk (round ((k : ℝ) * α))
    (happ.trans_lt hbound)

end ExternalO3PositiveCeilReturns
