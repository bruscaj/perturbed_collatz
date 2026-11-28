import AnalyticCapDiscrepancy
import WordPartitionTransport
import AnalyticCompactnessCompletion

/-! Actual finite-volume bounds and eventual equicontinuity. The functions themselves
may be discontinuous; no pressure limit is used. -/
namespace ExternalBridgePressureAnalyticOscillation
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureAnalyticCapDiscrepancy
open ExternalBridgePressureWordFiniteComparison ExternalBridgePressureWordPartitionTransport
open ExternalBridgePressureAnalyticCompactness
open Filter
open scoped Topology

private theorem coefficient_positive (lam : ℝ) (hl : 0 ≤ lam) : 0 < Real.log 2+lam := by
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

private theorem ordered_oscillation (lam eps : ℝ) (hl : 0 ≤ lam) (heps : 0 < eps)
    (n : ℕ) (hn : 1 ≤ n) (x y : ℝ) (hxy : OrderedPhases x y)
    (hd : |(Dcount x y n : ℝ)/(n : ℝ)-(y-x)| < eps/(2*(Real.log 2+lam))) :
    |auxFamily lam n x-auxFamily lam n y| ≤ (Real.log 2+lam)*(y-x)+eps := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hC := coefficient_positive lam hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogone : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ)<2) (by norm_num : (2 : ℝ)≠1)
    norm_num at h
    exact h
  have hcoeff : lam*Real.log 2 ≤ Real.log 2+lam := by nlinarith
  have hdist : 0 ≤ y-x := sub_nonneg.mpr hxy.2.2
  have hcomp := phase_log_comparison x y n lam hxy hn hl
  have hlo : auxLogPartition x n lam/(n : ℝ)-auxLogPartition y n lam/(n : ℝ) ≤
      lam*Real.log 2*(y-x) := by
    rw [← sub_div]
    apply (div_le_iff₀ hnp).mpr
    nlinarith [hcomp.2.2.1]
  have hhi : auxLogPartition y n lam/(n : ℝ)-auxLogPartition x n lam/(n : ℝ) ≤
      (Real.log 2+lam)*((Dcount x y n : ℝ)/(n : ℝ)) := by
    rw [← sub_div, ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hnp).mpr (by linarith [hcomp.2.2.2])
  have hD : (Dcount x y n : ℝ)/(n : ℝ) < (y-x)+eps/(2*(Real.log 2+lam)) := by
    linarith [(abs_lt.mp hd).2]
  have hsmall : (Real.log 2+lam)*(eps/(2*(Real.log 2+lam))) = eps/2 := by field_simp
  have hup : (Real.log 2+lam)*((Dcount x y n : ℝ)/(n : ℝ)) <
      (Real.log 2+lam)*(y-x)+eps := by
    have := mul_lt_mul_of_pos_left hD hC
    rw [mul_add,hsmall] at this
    linarith
  change |auxLogPartition x n lam/(n : ℝ)-auxLogPartition y n lam/(n : ℝ)| ≤ _
  rw [abs_le]
  constructor
  · linarith
  · have := mul_le_mul_of_nonneg_right hcoeff hdist
    linarith

/-- Frozen A04, symmetrized from the ordered cap comparison. -/
theorem auxiliary_oscillation_estimate : AuxiliaryOscillationEstimate := by
  intro lam hl eps heps
  have hC := coefficient_positive lam hl
  obtain ⟨N,hN,h⟩ := cap_difference_discrepancy (eps/(2*(Real.log 2+lam))) (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn x y hx hy
  rcases le_total x y with hxy | hyx
  · have hr := ordered_oscillation lam eps hl heps n (hN.trans hn) x y ⟨hx,hy,hxy⟩
      (h n hn x y ⟨hx,hy,hxy⟩)
    simpa only [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using hr
  · have hr := ordered_oscillation lam eps hl heps n (hN.trans hn) y x ⟨hy,hx,hyx⟩
      (h n hn y x ⟨hy,hx,hyx⟩)
    simpa only [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hyx)] using hr

/-- Frozen A05; n=0 is handled explicitly by the frozen zero denominator. -/
theorem auxiliary_boundedness_and_equicontinuity : AuxiliaryBoundednessAndEquicontinuity := by
  intro lam hl
  have hC := coefficient_positive lam hl
  constructor
  · have hM : 0 ≤ Real.log 4+lam := by
      have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      linarith
    refine ⟨Real.log 4+lam,hM,?_⟩
    intro n x hx
    by_cases hn : n=0
    · simp [auxFamily,auxLogPressure,hn,hM]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hb := (finite_partition_bounds x n lam hx).2 hl
      change |auxLogPartition x n lam/(n : ℝ)| ≤ _
      rw [abs_of_nonneg (div_nonneg hb.1 hn0.le)]
      apply (div_le_iff₀ hn0).mpr
      nlinarith [hb.2]
  · intro eps heps
    obtain ⟨N,hN,h⟩ := auxiliary_oscillation_estimate lam hl (eps/2) (by positivity)
    refine ⟨eps/(2*(Real.log 2+lam)),by positivity,N,hN,?_⟩
    intro n hn x y hx hy hxy
    have hsmall : (Real.log 2+lam)*(eps/(2*(Real.log 2+lam))) = eps/2 := by field_simp
    have hd := mul_lt_mul_of_pos_left hxy hC
    rw [hsmall] at hd
    exact lt_of_le_of_lt (h n hn x y hx hy) (by linarith)

/-- Frozen A11, using actual A05 and the discontinuous-sequence compactness theorem. -/
theorem auxiliary_subsequence_compactness : AuxiliarySubsequenceCompactness := by
  intro lam hl s hs
  have h := auxiliary_boundedness_and_equicontinuity lam hl
  exact discontinuous_sequence_compactness (auxFamily lam) h.1 h.2 s hs

end ExternalBridgePressureAnalyticOscillation
