import SpaceReward
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Explicit continuous cutoffs at the actual Haar-null circle seam. -/
namespace ExternalCriticalWeakReward
open ExternalCriticalSpaceDraft ExternalCriticalSpaceTopology ExternalCriticalSpaceReward
open MeasureTheory Filter
open scoped Topology
noncomputable section

def phaseCutoff (k : ℕ) (x : Phase) : ℝ := min 1 (((k : ℝ)+1)*dist x 0)
def cutoffReward (k : ℕ) (w : Config) : ℝ := phaseCutoff k w.1 * localReward w

theorem phase_cutoff_continuous (k : ℕ) : Continuous (phaseCutoff k) := by
  exact continuous_const.min (continuous_const.mul (continuous_id.dist continuous_const))

theorem phase_cutoff_bounds (k : ℕ) (x : Phase) : 0 ≤ phaseCutoff k x ∧ phaseCutoff k x ≤ 1 := by
  exact ⟨le_min (by norm_num) (mul_nonneg (by positivity) dist_nonneg), min_le_left _ _⟩

theorem phase_cutoff_zero (k : ℕ) : phaseCutoff k 0 = 0 := by simp [phaseCutoff]

theorem cutoff_reward_bounds (k : ℕ) (w : Config) : 0 ≤ cutoffReward k w ∧ cutoffReward k w ≤ 1 := by
  have hc := phase_cutoff_bounds k w.1
  have hr := local_reward_bounds w
  exact ⟨mul_nonneg hc.1 hr.1,
    (mul_le_mul_of_nonneg_left hr.2 hc.1).trans (by simpa using hc.2)⟩

theorem cutoff_reward_le_phase_distance (k : ℕ) (w : Config) :
    cutoffReward k w ≤ ((k : ℝ)+1)*dist w.1 0 := by
  have hc := phase_cutoff_bounds k w.1
  have hr := local_reward_bounds w
  calc
    cutoffReward k w ≤ phaseCutoff k w.1 := by
      exact (mul_le_mul_of_nonneg_left hr.2 hc.1).trans_eq (mul_one _)
    _ ≤ _ := min_le_right _ _

theorem cutoff_reward_continuous (k : ℕ) : Continuous (cutoffReward k) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases h : w.1 = 0
  · have he : cutoffReward k w = 0 := by simp [cutoffReward,h,phase_cutoff_zero]
    have ht : Tendsto (fun z : Config => ((k : ℝ)+1)*dist z.1 0) (𝓝 w) (𝓝 0) := by
      have hc : Continuous (fun z : Config => ((k : ℝ)+1)*dist z.1 0) :=
        continuous_const.mul (continuous_fst.dist continuous_const)
      simpa only [h, dist_self, mul_zero] using (hc.continuousAt (x := w)).tendsto
    rw [ContinuousAt,he]
    exact squeeze_zero (fun z => (cutoff_reward_bounds k z).1)
      (cutoff_reward_le_phase_distance k) ht
  · exact ((phase_cutoff_continuous k).comp continuous_fst).continuousAt.mul
      (local_reward_continuousAt w h)

def seamError (k : ℕ) (w : Config) : ℝ := 1-phaseCutoff k w.1

theorem seam_error_continuous (k : ℕ) : Continuous (seamError k) :=
  continuous_const.sub ((phase_cutoff_continuous k).comp continuous_fst)

theorem seam_error_bounds (k : ℕ) (w : Config) : 0 ≤ seamError k w ∧ seamError k w ≤ 1 := by
  have h := phase_cutoff_bounds k w.1
  exact ⟨sub_nonneg.mpr h.2, sub_le_self 1 h.1⟩

theorem seam_error_tendsto (w : Config) (hw : w.1 ≠ 0) :
    Tendsto (fun k => seamError k w) atTop (𝓝 0) := by
  have hd : 0 < dist w.1 0 := dist_pos.mpr hw
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / dist w.1 0)
  have hmul : 1 < (N : ℝ)*dist w.1 0 := (div_lt_iff₀ hd).mp hN
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkn : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
  have hh : 1 ≤ ((k : ℝ)+1)*dist w.1 0 := by nlinarith
  change 0 = 1-min 1 (((k : ℝ)+1)*dist w.1 0)
  rw [min_eq_left hh]
  ring

theorem uniform_phase_seam_null (nu : ProbabilityMeasure Config)
    (hu : HasUniformPhase (nu : Measure Config)) :
    (nu : Measure Config) {w | w.1 = 0} = 0 := by
  have hm := Measure.map_apply (μ := (nu : Measure Config))
    (f := (Prod.fst : Config → Phase)) continuous_fst.measurable (MeasurableSet.singleton (0 : Phase))
  change (nu : Measure Config) (Prod.fst ⁻¹' ({0} : Set Phase)) = 0
  rw [← hm, hu]
  simpa [uniformPhase] using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := (0 : Phase)) 0)

theorem seam_error_integral_tendsto (nu : ProbabilityMeasure Config)
    (hu : HasUniformPhase (nu : Measure Config)) :
    Tendsto (fun k => ∫ w, seamError k w ∂(nu : Measure Config)) atTop (𝓝 0) := by
  have hae : ∀ᵐ w ∂(nu : Measure Config), w.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using uniform_phase_seam_null nu hu
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := (nu : Measure Config))
    (F := seamError) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun k => (seam_error_continuous k).aestronglyMeasurable)
    (Eventually.of_forall fun k => Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (seam_error_bounds k w).1]
      exact (seam_error_bounds k w).2)
    (integrable_const 1)
    (hae.mono fun w hw => seam_error_tendsto w hw)
  simpa only [integral_zero] using ht

theorem reward_integrable (mu : ProbabilityMeasure Config) :
    Integrable localReward (mu : Measure Config) := by
  exact (integrable_const (1 : ℝ)).mono' local_reward_measurable.aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (local_reward_bounds w).1]
      exact (local_reward_bounds w).2)

theorem cutoff_reward_integrable (mu : ProbabilityMeasure Config) (k : ℕ) :
    Integrable (cutoffReward k) (mu : Measure Config) := by
  exact (integrable_const (1 : ℝ)).mono' (cutoff_reward_continuous k).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_reward_bounds k w).1]
      exact (cutoff_reward_bounds k w).2)

theorem seam_error_integrable (mu : ProbabilityMeasure Config) (k : ℕ) :
    Integrable (seamError k) (mu : Measure Config) := by
  exact (integrable_const (1 : ℝ)).mono' (seam_error_continuous k).aestronglyMeasurable
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (seam_error_bounds k w).1]
      exact (seam_error_bounds k w).2)

theorem cutoff_error_bound (k : ℕ) (w : Config) :
    |localReward w-cutoffReward k w| ≤ seamError k w := by
  have hr := local_reward_bounds w
  have hc := phase_cutoff_bounds k w.1
  have he : localReward w-cutoffReward k w = (1-phaseCutoff k w.1)*localReward w := by
    unfold cutoffReward
    ring
  rw [he, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hc.2) hr.1)]
  exact (mul_le_mul_of_nonneg_left hr.2 (sub_nonneg.mpr hc.2)).trans_eq (mul_one _)

theorem integral_cutoff_error (mu : ProbabilityMeasure Config) (k : ℕ) :
    |(∫ w, localReward w ∂(mu : Measure Config)) -
      (∫ w, cutoffReward k w ∂(mu : Measure Config))| ≤
        ∫ w, seamError k w ∂(mu : Measure Config) := by
  rw [← integral_sub (reward_integrable mu) (cutoff_reward_integrable mu k), ← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono ((reward_integrable mu).sub (cutoff_reward_integrable mu k)).norm
      (seam_error_integrable mu k) (fun w => by simpa only [Real.norm_eq_abs] using cutoff_error_bound k w))

theorem weak_reward_passage : WeakRewardPassage := by
  intro mu nu hmu hu
  have hcut (k : ℕ) : Tendsto
      (fun n => ∫ w, cutoffReward k w ∂(mu n : Measure Config)) atTop
        (𝓝 (∫ w, cutoffReward k w ∂(nu : Measure Config))) := by
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu
      (BoundedContinuousFunction.mkOfCompact ⟨cutoffReward k, cutoff_reward_continuous k⟩)
  have herr (k : ℕ) : Tendsto
      (fun n => ∫ w, seamError k w ∂(mu n : Measure Config)) atTop
        (𝓝 (∫ w, seamError k w ∂(nu : Measure Config))) := by
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmu
      (BoundedContinuousFunction.mkOfCompact ⟨seamError k, seam_error_continuous k⟩)
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have he5 : 0 < eps/5 := by linarith
  have hsmall := (seam_error_integral_tendsto nu hu).eventually (gt_mem_nhds he5)
  obtain ⟨k, hk⟩ := hsmall.exists
  have h1 := Metric.tendsto_nhds.mp (hcut k) (eps/5) he5
  have h2 := Metric.tendsto_nhds.mp (herr k) (eps/5) he5
  filter_upwards [h1,h2] with n hn1 hn2
  rw [Real.dist_eq] at hn1 hn2 ⊢
  have ha := integral_cutoff_error (mu n) k
  have hb := integral_cutoff_error nu k
  rw [abs_sub_comm (∫ w, localReward w ∂(nu : Measure Config))] at hb
  have hc := abs_sub_le
    (∫ w, localReward w ∂(mu n : Measure Config))
    (∫ w, cutoffReward k w ∂(mu n : Measure Config))
    (∫ w, localReward w ∂(nu : Measure Config))
  have hd := abs_sub_le
    (∫ w, cutoffReward k w ∂(mu n : Measure Config))
    (∫ w, cutoffReward k w ∂(nu : Measure Config))
    (∫ w, localReward w ∂(nu : Measure Config))
  have hg := le_abs_self
    ((∫ w, seamError k w ∂(mu n : Measure Config))-
      (∫ w, seamError k w ∂(nu : Measure Config)))
  linarith

end
end ExternalCriticalWeakReward
