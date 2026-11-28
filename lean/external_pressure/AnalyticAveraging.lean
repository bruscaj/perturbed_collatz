import AnalyticRotationGrid

/-! Elementary bounded-sequence shift averaging; no invariant-measure premise. -/
namespace ExternalBridgePressureAnalyticAveraging
open scoped BigOperators

/-- Moving a finite window only changes its two boundary pieces. -/
theorem shifted_sum_difference (f : ℕ → ℝ) (n s : ℕ) :
    (∑ t ∈ Finset.range n, f (t+s)) - (∑ t ∈ Finset.range n, f t) =
      (∑ t ∈ Finset.range s, f (t+n)) - (∑ t ∈ Finset.range s, f t) := by
  have h1 : (∑ t ∈ Finset.range (n+s), f t) =
      (∑ t ∈ Finset.range s, f t) + (∑ t ∈ Finset.range n, f (t+s)) := by
    simpa only [Nat.add_comm s] using Finset.sum_range_add f s n
  have h2 : (∑ t ∈ Finset.range (n+s), f t) =
      (∑ t ∈ Finset.range n, f t) + (∑ t ∈ Finset.range s, f (t+n)) := by
    simpa only [Nat.add_comm n] using Finset.sum_range_add f n s
  linarith

theorem shifted_sum_error (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (n s : ℕ) :
    |(∑ t ∈ Finset.range n, f (t+s)) - (∑ t ∈ Finset.range n, f t)| ≤ (s : ℝ) := by
  rw [shifted_sum_difference]
  have lo1 : 0 ≤ ∑ t ∈ Finset.range s, f (t+n) := Finset.sum_nonneg (fun t _ => (hf _).1)
  have lo2 : 0 ≤ ∑ t ∈ Finset.range s, f t := Finset.sum_nonneg (fun t _ => (hf _).1)
  have hi1 : (∑ t ∈ Finset.range s, f (t+n)) ≤ (s : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range s, (1 : ℝ) := Finset.sum_le_sum (fun t _ => (hf _).2)
      _ = _ := by simp
  have hi2 : (∑ t ∈ Finset.range s, f t) ≤ (s : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range s, (1 : ℝ) := Finset.sum_le_sum (fun t _ => (hf _).2)
      _ = _ := by simp
  rw [abs_le]
  constructor <;> linarith

/-- The deliberately coarse rT error is enough after division by n. -/
theorem averaged_shift_error (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (n r T : ℕ) (hT : 0 < T) :
    |((∑ j ∈ Finset.range T, ∑ t ∈ Finset.range n, f (t+j*r))/(T : ℝ)) -
      (∑ t ∈ Finset.range n, f t)| ≤ (r*T : ℕ) := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hid : ((∑ j ∈ Finset.range T, ∑ t ∈ Finset.range n, f (t+j*r))/(T : ℝ)) -
      (∑ t ∈ Finset.range n, f t) =
        (∑ j ∈ Finset.range T, ((∑ t ∈ Finset.range n, f (t+j*r)) -
          (∑ t ∈ Finset.range n, f t)))/(T : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hid, abs_div, abs_of_pos hTp]
  apply (div_le_iff₀ hTp).mpr
  calc
    _ ≤ ∑ j ∈ Finset.range T, |(∑ t ∈ Finset.range n, f (t+j*r)) -
        (∑ t ∈ Finset.range n, f t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range T, ((r*T : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (shifted_sum_error f hf n (j*r)).trans (by
        exact_mod_cast (show j*r ≤ r*T by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right r (Finset.mem_range.mp hj).le))
    _ = ((r*T : ℕ) : ℝ)*(T : ℝ) := by simp; ring


theorem bounded_average_error (g : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (c C : ℝ)
    (hg : ∀ t < n, |g t-c| ≤ C) :
    |(∑ t ∈ Finset.range n, g t)/(n : ℝ)-c| ≤ C := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : (∑ t ∈ Finset.range n, g t)/(n : ℝ)-c =
      (∑ t ∈ Finset.range n, (g t-c))/(n : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hid, abs_div, abs_of_pos hnp]
  apply (div_le_iff₀ hnp).mpr
  calc
    _ ≤ ∑ t ∈ Finset.range n, |g t-c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range n, C := Finset.sum_le_sum (fun t ht => hg t (Finset.mem_range.mp ht))
    _ = C*(n : ℝ) := by simp; ring

end ExternalBridgePressureAnalyticAveraging
