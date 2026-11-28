import AnalyticPhaseInfimum
import AnalyticConstant

/-! Fixed-shift normalization and actual subsequence limit identification. -/
namespace ExternalBridgePressureAnalyticSubsequence
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureAnalyticDraft ExternalBridgePressureAnalyticPhaseInfimum
open ExternalBridgePressureWordPartitionTransport ExternalBridgePressureAnalyticConstant
open Set Filter
open scoped Topology

theorem log_nat_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (nhds 0) := by
  simpa only [pow_one,one_mul,add_zero,Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem fixed_shift_normalized_completion : FixedShiftNormalizedCompletion := by
  intro lam hl m eps heps
  let A : ℝ := lam*(m : ℝ)+((m+1 : ℕ) : ℝ)*Real.log ((2*m+3 : ℕ) : ℝ)
  let roof : ℕ → ℝ := fun n => A/(n : ℝ)+((m+1 : ℕ) : ℝ)*(Real.log (n : ℝ)/(n : ℝ))
  have hA : Tendsto (fun n : ℕ => A/(n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hB : Tendsto (fun n : ℕ => ((m+1 : ℕ) : ℝ)*(Real.log (n : ℝ)/(n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul log_nat_div_tendsto_zero
  have ht : Tendsto roof atTop (nhds 0) := by
    simpa only [zero_add] using hA.add hB
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  refine ⟨max N 1,le_max_right _ _,fun n hn x hx => ?_⟩
  have hn1 : 1≤n := le_trans (le_max_right _ _) hn
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn1
  have hf := fixed_shift_comparison x n m lam hx hn1 hl
  have hp : (0 : ℝ)<((2*(n+m)+1 : ℕ) : ℝ) := by positivity
  have hC : (0 : ℝ)<((2*m+3 : ℕ) : ℝ) := by positivity
  have hbound : ((2*(n+m)+1 : ℕ) : ℝ) ≤ ((2*m+3 : ℕ) : ℝ)*(n : ℝ) := by
    have hn' : (1 : ℝ)≤n := by exact_mod_cast hn1
    push_cast
    nlinarith
  have hlog := Real.log_le_log hp hbound
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt hnR)] at hlog
  have hdiff : auxLogPartition x (n+m) lam-auxLogPartition x n lam ≤
      A+((m+1 : ℕ) : ℝ)*Real.log (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (m+1))
    dsimp [A]
    nlinarith [hf.2.2.2]
  calc
    |(auxLogPartition x (n+m) lam-auxLogPartition x n lam)/(n : ℝ)| =
        (auxLogPartition x (n+m) lam-auxLogPartition x n lam)/(n : ℝ) :=
      abs_of_nonneg (div_nonneg hf.2.2.1 (le_of_lt hnR))
    _ ≤ (A+((m+1 : ℕ) : ℝ)*Real.log (n : ℝ))/(n : ℝ) :=
      div_le_div_of_nonneg_right hdiff (le_of_lt hnR)
    _ = roof n := by dsimp [roof]; ring
    _ < eps := hN n (le_trans (le_max_left _ _) hn)

theorem uniform_along_pointwise (lam : ℝ) (q : ℕ → ℕ) (f : ℝ → ℝ)
    (hu : UniformAlong (auxFamily lam) q f) (x : ℝ) (hx : ClosedPhase x) :
    Tendsto (fun j => auxLogPressure x (q j) lam) atTop (nhds (f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N,_,hN⟩ := hu eps heps
  refine ⟨N,fun j hj => ?_⟩
  simpa only [Real.dist_eq,auxFamily] using hN j hj x hx

theorem completion_along_tendsto (lam : ℝ) (hl : 0≤lam) (m : ℕ)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (x : ℝ) (hx : ClosedPhase x) :
    Tendsto (fun j => (auxLogPartition x (q j+m) lam-auxLogPartition x (q j) lam)/(q j : ℝ)) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨N,_,hN⟩ := fixed_shift_normalized_completion lam hl m eps heps
  filter_upwards [hq.eventually (eventually_ge_atTop N)] with j hj
  simpa only [Real.dist_eq,sub_zero] using hN (q j) hj x hx

theorem subsequence_rotation_domination : SubsequenceRotationDomination := by
  intro lam hl q hq f hu x hx m _
  have hy : ActualPhase (phaseShift x m) := phase_actual x m
  have hxc : ClosedPhase x := ⟨hx.1,le_of_lt hx.2⟩
  have hyc : ClosedPhase (phaseShift x m) := ⟨hy.1,le_of_lt hy.2⟩
  have hxf := uniform_along_pointwise lam q f hu x hxc
  have hyf := uniform_along_pointwise lam q f hu (phaseShift x m) hyc
  have he := completion_along_tendsto lam hl m q hq x hxc
  have hc : Tendsto (fun j => auxLogPartition x m lam/(q j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hq)
  have hright : Tendsto (fun j => auxLogPressure x (q j) lam+
      (auxLogPartition x (q j+m) lam-auxLogPartition x (q j) lam)/(q j : ℝ)-
      auxLogPartition x m lam/(q j : ℝ)) atTop (nhds (f x)) := by
    simpa only [add_zero,sub_zero] using (hxf.add he).sub hc
  apply le_of_tendsto_of_tendsto hyf hright
  filter_upwards [hq.eventually (eventually_ge_atTop 1)] with j hj
  have hp : (0 : ℝ)<q j := by exact_mod_cast hj
  have h := ExternalBridgePressureWordConcatenation.partition_cocycle x m (q j) lam hx hl
  rw [Nat.add_comm m (q j)] at h
  have hd := div_le_div_of_nonneg_right h (le_of_lt hp)
  unfold auxLogPressure
  simp only [add_div,sub_div] at hd ⊢
  linarith only [hd]

theorem auxiliary_subsequence_constant : AuxiliarySubsequenceConstant := by
  intro lam hl q hq f hf hu
  exact rotation_domination_implies_constant f hf
    (subsequence_rotation_domination lam hl q hq f hu)

theorem phase_infimum_along_uniform_constant (lam : ℝ) (hl : 0≤lam)
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (c : ℝ)
    (hu : UniformAlong (auxFamily lam) q (fun _ => c)) :
    Tendsto (fun j => phaseInfimum (q j) lam/(q j : ℝ)) atTop (nhds c) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨N,_,hN⟩ := hu (eps/2) (by positivity)
  filter_upwards [eventually_ge_atTop N,hq.eventually (eventually_ge_atTop 1)] with j hj hqj
  have hp : (0 : ℝ)<q j := by exact_mod_cast hqj
  have hzero : ActualPhase (0 : ℝ) := by constructor <;> norm_num
  have h0 := hN j hj 0 ⟨hzero.1,le_of_lt hzero.2⟩
  change |auxLogPartition 0 (q j) lam/(q j : ℝ)-c|<eps/2 at h0
  have hlo : c-eps/2 ≤ phaseInfimum (q j) lam/(q j : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    apply le_phase_infimum (q j) lam
    intro x hx
    have h := hN j hj x ⟨hx.1,le_of_lt hx.2⟩
    change |auxLogPartition x (q j) lam/(q j : ℝ)-c|<eps/2 at h
    have ha : c-eps/2 ≤ auxLogPartition x (q j) lam/(q j : ℝ) := by
      have := (abs_lt.mp h).1
      linarith
    exact (le_div_iff₀ hp).mp ha
  have hhi : phaseInfimum (q j) lam/(q j : ℝ) ≤ c+eps/2 := by
    have h := div_le_div_of_nonneg_right (phase_infimum_le_phase (q j) lam hl 0 hzero) (le_of_lt hp)
    have := (abs_lt.mp h0).2
    linarith
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

theorem subsequence_constant_identification : SubsequenceConstantIdentification := by
  intro lam hl q hq c hu
  have hc := phase_infimum_along_uniform_constant lam hl q hq c hu
  have hP := (fekete_candidate_limit lam hl).comp hq
  exact tendsto_nhds_unique hc hP

end ExternalBridgePressureAnalyticSubsequence
