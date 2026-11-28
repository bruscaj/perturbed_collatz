import RateMarker
import GeneralDensity

/-! Marker upper-bound foundations for the frozen literal model. -/
namespace ExternalO3RateMarkerUpper
open ExternalO3GeneralDraft ExternalO3RateDraft ExternalO3RateMarker
open ExternalO3GeneralWeights ExternalO3GeneralDensity
open scoped BigOperators

/-- The selector reads only future entries, including its first-tie rule. -/
theorem selector_future_congr (h : Depth) (hh : 2 ≤ h.val) (w v : Window h)
    (hv : ∀ i, 0 < i.val → w i = v i) :
    firstFutureMax h w = firstFutureMax h v := by
  obtain ⟨hwpos, hwmax, hwfirst⟩ := marker_selector_law h w hh
  obtain ⟨hvpos, hvmax, hvfirst⟩ := marker_selector_law h v hh
  have hwa := hv (firstFutureMax h w) hwpos
  have hva := hv (firstFutureMax h v) hvpos
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hvfirst (firstFutureMax h w) hwpos hlt
    have hm := hwmax (firstFutureMax h v) hvpos
    omega
  · have hs := hwfirst (firstFutureMax h v) hvpos hgt
    have hm := hvmax (firstFutureMax h w) hwpos
    omega

/-- Every ascending step moves the selected future marker one stride closer. -/
theorem markerDistance_decrement (h : Depth) (hh : 2 ≤ h.val) (w : Window h)
    (hw : 1 ≤ w (zeroIndex h)) :
    markerDistance h (decrementHead h w) + 1 = markerDistance h w := by
  have hsel : firstFutureMax h (decrementHead h w) = firstFutureMax h w := by
    apply selector_future_congr h hh
    intro i hi
    simp [decrementHead, Nat.ne_of_gt hi]
  have hpos := (marker_selector_law h w hh).1
  have hpoint : ∀ i : Fin h.val,
      (if i.val < (firstFutureMax h w).val then w i else 0) =
      (if i.val < (firstFutureMax h w).val then decrementHead h w i else 0) +
      (if i = zeroIndex h then 1 else 0) := by
    intro i
    by_cases hi : i = zeroIndex h
    · subst i
      simp only [show (zeroIndex h).val = 0 from rfl, hpos, ite_true, decrementHead]
      omega
    · have hi0 : i.val ≠ 0 := by
        intro he
        apply hi
        apply Fin.ext
        exact he
      simp [decrementHead, hi0, hi]
  unfold markerDistance
  rw [hsel]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib] at hs
  simpa using hs.symm

/-- Every symbolic ascending gain of this marker is strictly negative. -/
theorem marker_ascending_gain_neg (h : Depth) (hh : 2 ≤ h.val)
    (a : AscendingIndex h) : gain h (markerCorrection h) (.inl a) < 0 := by
  have hw : 1 ≤ ascendingWindow h a (zeroIndex h) := by
    simp [ascendingWindow, zeroIndex]
  have hd := markerDistance_decrement h hh (ascendingWindow h a) hw
  have hc : (markerDistance h (decrementHead h (ascendingWindow h a)) : ℝ) + 1 =
      (markerDistance h (ascendingWindow h a) : ℝ) := by exact_mod_cast hd
  have hl : Real.log ((3 : ℝ) / 2) < Real.log 2 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  simp only [gain, markerCorrection]
  calc
    _ = Real.log ((3 : ℝ) / 2) - Real.log 2 := by rw [← hc]; ring
    _ < 0 := sub_neg.mpr hl

theorem marker_ascending_weight_zero (h : Depth) (hh : 2 ≤ h.val)
    (a : AscendingIndex h) : selectedWeight h (markerCorrection h) (.inl a) = 0 := by
  have hn := not_le_of_gt (marker_ascending_gain_neg h hh a)
  simp [selectedWeight, Bad, hn]

/-- First rigorous achieved-density cap; the sharper depth bound is separate. -/
theorem marker_density_half (h : Depth) (hh : 2 ≤ h.val) :
    ∃ d : ℝ, HasFailureDensity h (markerCorrection h) d ∧ d ≤ 1 / 2 := by
  let φ := markerCorrection h
  have hs := selected_mass_summable h φ
  refine ⟨symbolicFailureDensity h φ, (density_equals_symbolic h φ).2.2.2, ?_⟩
  unfold symbolicFailureDensity
  rw [Summable.tsum_sum (f := selectedWeight h φ) (hs.comp_injective Sum.inl_injective) (hs.comp_injective Sum.inr_injective)]
  have hz : (fun a : AscendingIndex h => selectedWeight h φ (.inl a)) = fun _ => 0 := by
    funext a
    exact marker_ascending_weight_zero h hh a
  rw [hz, tsum_zero, zero_add]
  calc
    _ ≤ ∑' p : ExitIndex h, weight h (.inr p) :=
      Summable.tsum_le_tsum (fun p => selectedWeight_le h φ (.inr p))
        (hs.comp_injective Sum.inr_injective) (exit_summable h)
    _ = 1 / 2 := exit_tsum h

/-- Algebraic lower bound for a power increment; no calculus is used. -/
theorem power_increment_lower (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    ((n : ℝ) + 1) * x ^ n * (y - x) ≤ y ^ (n + 1) - x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_left ih hx
    have hp := pow_le_pow_left₀ hx hxy (n + 1)
    have hp' := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hxy)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at *
    nlinarith

/-- One dyadic maximum-probability term is bounded by a telescoping increment. -/
theorem dyadic_term_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * (1 - t) ^ n ≤
      (2 / ((n : ℝ) + 1)) * ((1 - t / 2) ^ (n + 1) - (1 - t) ^ (n + 1)) := by
  have hi := power_increment_lower (1 - t) (1 - t / 2) (by linarith)
    (by linarith) n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hn]
  nlinarith

/-- Finite dyadic telescoping bound for the first weak-maximum series. -/
theorem weak_max_partial_sum_le (n N : ℕ) :
    (∑ r ∈ Finset.range N, (1 / 2 : ℝ) ^ (r + 1) *
      (1 - (1 / 2 : ℝ) ^ (r + 1)) ^ n) ≤ 2 / ((n : ℝ) + 1) := by
  let F : ℕ → ℝ := fun r => (1 - (1 / 2 : ℝ) ^ (r + 1)) ^ (n + 1)
  have hstep (r : ℕ) :
      (1 / 2 : ℝ) ^ (r + 1) * (1 - (1 / 2 : ℝ) ^ (r + 1)) ^ n ≤
      (2 / ((n : ℝ) + 1)) * (F (r + 1) - F r) := by
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (r + 1) := by positivity
    have hp1 : (1 / 2 : ℝ) ^ (r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have he : (1 / 2 : ℝ) ^ (r + 1) / 2 = (1 / 2 : ℝ) ^ (r + 1 + 1) := by
      rw [pow_succ]; ring
    simpa only [F, ← he] using dyadic_term_le n ((1 / 2 : ℝ) ^ (r + 1)) hp hp1
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun r _ => hstep r)
  rw [← Finset.mul_sum, Finset.sum_range_sub] at hsum
  have hFN : F N ≤ 1 := by
    apply pow_le_one₀
    · have hp : (1 / 2 : ℝ) ^ (N + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      exact sub_nonneg.mpr hp
    · have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N + 1) := by positivity
      linarith
  have hF0 : 0 ≤ F 0 := by dsimp [F]; positivity
  have hc : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  exact hsum.trans (mul_le_of_le_one_right hc (by linarith))

/-- Discrete first-maximum estimate without integration. -/
theorem weak_max_tsum_le (n : ℕ) :
    (∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) *
      (1 - (1 / 2 : ℝ) ^ (r + 1)) ^ n) ≤ 2 / ((n : ℝ) + 1) := by
  apply Real.tsum_le_of_sum_range_le
  · intro r
    apply mul_nonneg (by positivity)
    apply pow_nonneg
    have hp : (1 / 2 : ℝ) ^ (r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact sub_nonneg.mpr hp
  · exact weak_max_partial_sum_le n

end ExternalO3RateMarkerUpper
