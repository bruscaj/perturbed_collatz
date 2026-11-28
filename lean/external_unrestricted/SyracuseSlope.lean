import RungTransfer
import LogRatioIrrational

/-! Actual source slope instantiated using the separately audited 2/3 log proof. -/
namespace ExternalSyracuseSlope
open ExternalO3DepthOneSeries ExternalO3LogRatio ExternalRungSpec ExternalRungTransfer

noncomputable def theta : ℝ := Real.log 3 / Real.log 2

theorem theta_eq : theta = ascent / Real.log 2 + 1 := by
  unfold theta
  rw [ascent_eq]
  field_simp; ring

theorem theta_irrational : Irrational theta := by
  rw [theta_eq]
  simpa using ascent_ratio_irrational.add_intCast 1

theorem one_lt_theta : 1 < theta := by
  rw [theta_eq]
  have := div_pos ascent_pos log_two_pos
  linarith

theorem theta_lt_two : theta < 2 := by
  unfold theta
  apply (div_lt_iff₀ log_two_pos).mpr
  have h : Real.log 3 < Real.log ((2 : ℝ) ^ 2) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem source_closing (r : ℕ) (hr : IsRung theta r)
    (K : ExternalPrefixSpec.Profile) :
    SourceAdmissible theta K r ↔
      ExternalPrefixSpec.ClosingAdmissible (floorProfile theta) K r :=
  source_closing_iff theta theta_irrational r hr K

end ExternalSyracuseSlope
