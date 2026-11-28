import RateLower
import RateCantelli
import RateInfimum

/-! Actual lower bounds; full inverse-depth theorem still awaits shrinking upper proof. -/
namespace ExternalO3RateBounds
open ExternalO3RateDraft ExternalO3GeneralDraft ExternalO3RateInfimum
open ExternalO3RateLower ExternalO3RateCantelli

theorem infimum_lower_strong (h : Depth) :
    1 / (4 * ((h.val : ℝ) + 33)) ≤ failureInfimum h := by
  have hn : (0 : ℝ) < (h.val : ℝ) + 1 := by positivity
  have hp : (0 : ℝ) < 4 * ((h.val : ℝ) + 1) := by positivity
  apply le_csInf (infimum_well_posed h).2.1
  rintro d ⟨φ, hd⟩
  have hm := positive_cycle_mass_lower_bound h
  have hl := cyclic_density_lower_bound h φ d hd
  have he : (((h.val : ℝ) + 1) / ((h.val : ℝ) + 33)) /
      (4 * ((h.val : ℝ) + 1)) = 1 / (4 * ((h.val : ℝ) + 33)) := by
    field_simp
  rw [← he]
  exact (div_le_div_of_nonneg_right hm hp.le).trans hl

theorem infimum_lower_uniform (h : Depth) :
    1 / (136 * (h.val : ℝ)) ≤ failureInfimum h := by
  have h1 : (1 : ℝ) ≤ (h.val : ℝ) := by exact_mod_cast h.property
  calc
    1 / (136 * (h.val : ℝ)) ≤ 1 / (4 * ((h.val : ℝ) + 33)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ ≤ failureInfimum h := infimum_lower_strong h

theorem frozen_lower_bound (h : Depth) :
    (127 : ℝ) / (32768 * (h.val : ℝ)) ≤ failureInfimum h := by
  have hh : (0 : ℝ) < (h.val : ℝ) := Nat.cast_pos.mpr h.property
  calc
    (127 : ℝ) / (32768 * (h.val : ℝ)) ≤ 1 / (136 * (h.val : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ ≤ failureInfimum h := infimum_lower_uniform h

/-- This conditional assembly is not the still-missing upper-bound theorem. -/
theorem explicit_rate_of_marker_upper (hu : MarkerUpperBound) : ExplicitInverseDepthRate := by
  intro h
  refine ⟨frozen_lower_bound h, ?_⟩
  have hh : (0 : ℝ) < (h.val : ℝ) := Nat.cast_pos.mpr h.property
  by_cases h2 : 2 ≤ h.val
  · obtain ⟨d, hd, hb⟩ := hu h h2
    have h2R : (2 : ℝ) ≤ (h.val : ℝ) := by exact_mod_cast h2
    have hp : (0 : ℝ) < (h.val : ℝ) - 1 := by linarith
    have hrec : 1 / ((h.val : ℝ) - 1) ≤ 2 / (h.val : ℝ) := by
      apply (div_le_div_iff₀ hp hh).mpr
      linarith
    calc
      failureInfimum h ≤ d := infimum_le_density h (markerCorrection h) d hd
      _ ≤ 1 / ((h.val : ℝ) - 1) + 1 / (2 * (h.val : ℝ)) := hb.trans (min_le_right _ _)
      _ ≤ 2 / (h.val : ℝ) + 1 / (2 * (h.val : ℝ)) := add_le_add hrec (le_refl (1 / (2 * (h.val : ℝ))))
      _ = (5 : ℝ) / (2 * (h.val : ℝ)) := by field_simp; ring
  · have h1 : h.val = 1 := by have hp := h.property; omega
    calc
      failureInfimum h ≤ 1 := infimum_le_one h
      _ ≤ (5 : ℝ) / (2 * (h.val : ℝ)) := by rw [h1]; norm_num

end ExternalO3RateBounds
