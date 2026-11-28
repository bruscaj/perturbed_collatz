import AnalyticReference
import WordFiniteComparison
import AnalyticUniformPressure

/-! Literal finite reward/reference/cost identities. -/
namespace ExternalBridgePressureAnalyticCost
open ExternalBridgePressureDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureWordDraft
open ExternalBridgePressureWordPartitions ExternalBridgePressureWordFiniteComparison
open ExternalBridgePressureAnalyticReference ExternalBridgePressureAnalyticUniformPressure
open scoped BigOperators

theorem path_reward_cost (x : ℝ) (n : ℕ) (j : Path n) :
    pathReward x n j + pathCost x n j = reference x n := by
  unfold pathReward pathCost reference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem partition_factor (x : ℝ) (n : ℕ) (lam : ℝ) :
    rewardPartition x n lam = Real.exp (lam*reference x n)*costPartition x n lam := by
  classical
  unfold rewardPartition costPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : PathLegal x n j
  · simp only [hj,ite_true]
    rw [← Real.exp_add]
    congr 1
    have hreward : pathReward x n j = reference x n-pathCost x n j := by linarith [path_reward_cost x n j]
    rw [hreward]
    ring
  · simp only [hj,ite_false,mul_zero]

theorem cost_partition_positive (x : ℝ) (hx : ActualPhase x) (n : ℕ) (lam : ℝ) :
    0 < costPartition x n lam := by
  have hp : 0 < rewardPartition x n lam := by
    rw [← word_path_partition_equality x n lam hx]
    exact (finite_partition_bounds x n lam ⟨hx.1,hx.2.le⟩).1
  rw [partition_factor] at hp
  by_contra h
  have := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (lam*reference x n)).le (le_of_not_gt h)
  linarith

theorem finite_cost_pressure (x : ℝ) (hx : ActualPhase x) (n : ℕ) (lam : ℝ) :
    costLogPressure x lam n = rewardLogPressure x lam n-lam*(reference x n/(n : ℝ)) := by
  unfold costLogPressure rewardLogPressure
  rw [partition_factor,Real.log_mul (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (cost_partition_positive x hx n lam)),Real.log_exp,add_div]
  ring


/-- Compact-tilt cost convergence from actual reward convergence and actual reference averaging. -/
theorem compact_cost_pressure (L : ℝ) (hL : 0 ≤ L) :
    CompactTiltActualConvergence physicalCostFamily candidateCostPressure L := by
  intro eps heps
  obtain ⟨N1,hN1,h1⟩ := physical_reward_pressure_composition.2 L hL (eps/2) (by positivity)
  obtain ⟨N2,hN2,h2⟩ := uniform_reference_composition (eps/(2*(L+1))) (by positivity)
  refine ⟨max N1 N2,le_trans hN1 (le_max_left _ _),?_⟩
  intro n hn x hx lam hl hlL
  have hn1 : N1 ≤ n := (le_max_left _ _).trans hn
  have hn2 : N2 ≤ n := (le_max_right _ _).trans hn
  have hre := h1 n hn1 x hx.1 hx.2 lam hl hlL
  have href := h2 n hn2 x hx.1 hx.2
  have hscale : lam*|reference x n/(n : ℝ)-meanReference| < eps/2 := by
    have hη : 0 < eps/(2*(L+1)) := by positivity
    have hmul := mul_le_mul_of_nonneg_left href.le hl
    have hstrict : lam*(eps/(2*(L+1))) < (L+1)*(eps/(2*(L+1))) :=
      mul_lt_mul_of_pos_right (by linarith) hη
    have hid : (L+1)*(eps/(2*(L+1))) = eps/2 := by field_simp
    rw [hid] at hstrict
    exact hmul.trans_lt hstrict
  change |costLogPressure x lam n-candidateCostPressure lam| < eps
  rw [finite_cost_pressure x hx n lam]
  have hid : rewardLogPressure x lam n-lam*(reference x n/(n : ℝ))-candidateCostPressure lam =
      (rewardLogPressure x lam n-candidatePressure lam)-
        lam*(reference x n/(n : ℝ)-meanReference) := by
    unfold candidateCostPressure
    ring
  rw [hid]
  calc
    _ ≤ |rewardLogPressure x lam n-candidatePressure lam|+
        |lam*(reference x n/(n : ℝ)-meanReference)| := abs_sub _ _
    _ < eps := by rw [abs_mul,abs_of_nonneg hl]; linarith

/-- Frozen A27: all nonnegative tilts, compact tilt ranges, and the shared algebraic identity. -/
theorem cost_pressure_composition : CostPressureComposition := by
  refine ⟨?_,compact_cost_pressure,?_⟩
  · intro lam hl eps heps
    obtain ⟨N,hN,h⟩ := compact_cost_pressure lam hl eps heps
    refine ⟨N,hN,?_⟩
    intro n hn x hx0 hx1
    exact h n hn x ⟨hx0,hx1⟩ lam hl le_rfl
  · intro lam _hl
    unfold candidateCostPressure
    ring

end ExternalBridgePressureAnalyticCost
