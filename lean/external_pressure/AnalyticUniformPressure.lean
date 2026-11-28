import AnalyticSubsequence
import AnalyticOscillation
import BridgeRungs
import WordRung

/-! Actual auxiliary uniform pressure and finite-tilt/source compositions.
No pressure-law premise is introduced. -/
namespace ExternalBridgePressureAnalyticUniformPressure
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureAnalyticDraft ExternalBridgePressureAnalyticSubsequence
open ExternalBridgePressureAnalyticPhaseInfimum ExternalBridgePressureAnalyticOscillation
open ExternalBridgePressureWordFiniteComparison ExternalBridgePressureWordReward
open ExternalBridgePressureWordPartitions ExternalBridgePressureWordRung
open ExternalBridgePressureAnalyticCompactness ExternalFiniteBridgeRungs
open Filter Set
open scoped Topology

 theorem full_auxiliary_uniform_pressure : FullAuxiliaryUniformPressure := by
  classical
  intro lam hl
  by_contra hnot
  change ¬(∀ eps : ℝ,0<eps → ∃ N : ℕ,1≤N ∧ ∀ n : ℕ,N≤n →
    ∀ x : ℝ,ClosedPhase x → |auxFamily lam n x-candidatePressure lam|<eps) at hnot
  push Not at hnot
  obtain ⟨eps,heps,hbad⟩ := hnot
  choose q hq x hx hfail using (fun k : ℕ => hbad (k+1) (by omega))
  have hqt : Tendsto q atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    exact eventually_atTop.mpr ⟨B,fun k hk => by have := hq k; omega⟩
  obtain ⟨k,hk,f,hfc,hfu⟩ := auxiliary_subsequence_compactness lam hl q hqt
  have hqk := hqt.comp hk.tendsto_atTop
  obtain ⟨c,hc⟩ := auxiliary_subsequence_constant lam hl (q ∘ k) hqk f hfc hfu
  have hcu : UniformAlong (auxFamily lam) (q ∘ k) (fun _ => c) := by
    intro d hd
    obtain ⟨N,hN,hconv⟩ := hfu d hd
    refine ⟨N,hN,fun j hj y hy => ?_⟩
    rw [← hc y hy]
    exact hconv j hj y hy
  have hP := subsequence_constant_identification lam hl (q ∘ k) hqk c hcu
  obtain ⟨N,_,hN⟩ := hcu eps heps
  have h := hN N (le_refl _) (x (k N)) (hx (k N))
  rw [hP] at h
  have hbadN := hfail (k N)
  exact (not_lt_of_ge hbadN) h

theorem normalized_tilt_bound (x : ℝ) (n : ℕ) (hx : ClosedPhase x) (hn : 1≤n)
    (lam mu : ℝ) (hl : 0≤lam) (hm : 0≤mu) :
    |auxLogPressure x n lam-auxLogPressure x n mu|≤|lam-mu| := by
  have hp : (0 : ℝ)<n := by exact_mod_cast hn
  unfold auxLogPressure
  rw [← sub_div,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  simpa only [mul_comm] using ExternalBridgePressureWordFiniteComparison.finite_tilt_lipschitz x n lam mu hx hl hm

theorem candidate_tilt_lipschitz : CandidateTiltLipschitz := by
  intro lam mu hl hm
  have hz : ClosedPhase (0 : ℝ) := by constructor <;> norm_num
  have hL := uniform_along_pointwise lam id (fun _ => candidatePressure lam)
    (full_auxiliary_uniform_pressure lam hl) 0 hz
  have hM := uniform_along_pointwise mu id (fun _ => candidatePressure mu)
    (full_auxiliary_uniform_pressure mu hm) 0 hz
  apply le_of_tendsto ((hL.sub hM).abs)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact normalized_tilt_bound 0 n hz hn lam mu hl hm

theorem compact_auxiliary_tilt_pressure : CompactAuxiliaryTiltPressure := by
  classical
  intro L hL eps heps
  let M : ℝ := L+1
  have hM : 0<M := by dsimp [M]; linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (3*M/eps)
  have hmR : (0 : ℝ)<m := lt_trans (by positivity : (0 : ℝ)<3*M/eps) hm
  have hm1 : 1≤m := by exact_mod_cast hmR
  have hmesh : M/(m : ℝ)<eps/3 := by
    have h := (div_lt_iff₀ heps).mp hm
    apply (div_lt_iff₀ hmR).mpr
    nlinarith
  have hg := grid_mesh_cover m hm1
  let mu : Fin (m+1) → ℝ := fun i => M*gridPoint m i
  have hmu (i : Fin (m+1)) : 0≤mu i := mul_nonneg (le_of_lt hM) (hg.1 i).1
  have hex (i : Fin (m+1)) := full_auxiliary_uniform_pressure (mu i) (hmu i) (eps/3) (by positivity)
  choose Ns hNs hconv using hex
  let N : ℕ := max 1 (Finset.univ.sup Ns)
  refine ⟨N,le_max_left _ _,fun n hn x hx lam hl hlam => ?_⟩
  have hn1 : 1≤n := le_trans (le_max_left _ _) hn
  let z : ℝ := lam/M
  have hz : ClosedPhase z := by
    refine ⟨div_nonneg hl (le_of_lt hM),?_⟩
    apply (div_le_one hM).mpr
    dsimp [M]
    linarith
  obtain ⟨i,hi⟩ := hg.2 z hz
  have he : M*z=lam := by dsimp [z]; field_simp
  have hclose : |lam-mu i|<eps/3 := by
    have hdist : |lam-mu i| = M*|z-gridPoint m i| := by
      rw [← he]
      change |M*z-M*gridPoint m i| = _
      rw [← mul_sub,abs_mul,abs_of_pos hM]
    rw [hdist]
    calc
      M*|z-gridPoint m i| ≤ M*(1/(m : ℝ)) := mul_le_mul_of_nonneg_left hi (le_of_lt hM)
      _ = M/(m : ℝ) := by ring
      _ < eps/3 := hmesh
  have hiN : Ns i≤n := by
    exact le_trans (Finset.le_sup (Finset.mem_univ i)) (le_trans (le_max_right _ _) hn)
  have hc := hconv i n hiN x hx
  have hfinite := normalized_tilt_bound x n hx hn1 lam (mu i) hl (hmu i)
  have hlimit := candidate_tilt_lipschitz (mu i) lam (hmu i) hl
  rw [abs_sub_comm (mu i) lam] at hlimit
  have ht1 := abs_sub_le (auxFamily lam n x) (auxFamily (mu i) n x) (candidatePressure lam)
  have ht2 := abs_sub_le (auxFamily (mu i) n x) (candidatePressure (mu i)) (candidatePressure lam)
  change |auxLogPressure x n (mu i)-candidatePressure (mu i)|<eps/3 at hc
  change |auxLogPressure x n lam-auxLogPressure x n (mu i)|≤|lam-mu i| at hfinite
  change |auxLogPressure x n lam-candidatePressure lam|<eps
  change |auxLogPressure x n lam-candidatePressure lam| ≤
    |auxLogPressure x n lam-auxLogPressure x n (mu i)|+|auxLogPressure x n (mu i)-candidatePressure lam| at ht1
  change |auxLogPressure x n (mu i)-candidatePressure lam| ≤
    |auxLogPressure x n (mu i)-candidatePressure (mu i)|+|candidatePressure (mu i)-candidatePressure lam| at ht2
  linarith

theorem actual_reward_pressure_eq (x : ℝ) (n : ℕ) (lam : ℝ) (hx : ActualPhase x) :
    rewardLogPressure x lam n = auxLogPressure x n lam := by
  unfold rewardLogPressure auxLogPressure auxLogPartition
  rw [word_path_partition_equality x n lam hx]

theorem physical_reward_pressure_composition : PhysicalRewardPressureComposition := by
  constructor
  · intro lam hl eps heps
    obtain ⟨N,hN,hconv⟩ := full_auxiliary_uniform_pressure lam hl eps heps
    refine ⟨N,hN,fun n hn x hx0 hx1 => ?_⟩
    change |rewardLogPressure x lam n-candidatePressure lam|<eps
    rw [actual_reward_pressure_eq x n lam ⟨hx0,hx1⟩]
    exact hconv n hn x ⟨hx0,le_of_lt hx1⟩
  · intro L hL eps heps
    obtain ⟨N,hN,hconv⟩ := compact_auxiliary_tilt_pressure L hL eps heps
    refine ⟨N,hN,fun n hn x hx0 hx1 lam hl hlam => ?_⟩
    rw [actual_reward_pressure_eq x n lam ⟨hx0,hx1⟩]
    exact hconv n hn x ⟨hx0,le_of_lt hx1⟩ lam hl hlam

theorem source_rung_pressure_composition : SourceRungPressureComposition := by
  intro lam hl
  refine ⟨fun r hr => ?_,source_rungs_unbounded,?_⟩
  · rw [rung_word_transport r lam hr]
    exact aux_partition_positive 0 r (by constructor <;> norm_num) lam
  · intro eps heps
    obtain ⟨N,_,hconv⟩ := full_auxiliary_uniform_pressure lam hl eps heps
    refine ⟨N,fun r hrN hr => ?_⟩
    have h := hconv r hrN 0 (by constructor <;> norm_num)
    change |auxLogPressure 0 r lam-candidatePressure lam|<eps at h
    unfold sourceLogPressure
    rw [rung_word_transport r lam hr]
    exact h

theorem closing_tilt_bounds (lam : ℝ) (hl : 0≤lam) (r : ℕ) :
    lam≤lam*Real.rpow 2 (defect slope r) ∧ lam*Real.rpow 2 (defect slope r)≤2*lam := by
  have hd := closing_phase_bounds r
  have hlo : (1 : ℝ)≤Real.rpow 2 (defect slope r) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hd.1
    simpa only [Real.rpow_eq_pow,Real.rpow_zero] using h
  have hhi : Real.rpow 2 (defect slope r)≤(2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) (le_of_lt hd.2)
    simpa only [Real.rpow_eq_pow,Real.rpow_one] using h
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hl]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hl]

theorem variable_tilt_source_asymptotic : VariableTiltSourceAsymptotic := by
  intro lam hl eps heps
  obtain ⟨N,hN,hconv⟩ := compact_auxiliary_tilt_pressure (2*lam) (by positivity) eps heps
  refine ⟨N,hN,fun r hr => ?_⟩
  have hr1 : 1≤r := hN.trans hr
  have hd := closing_phase_bounds r
  have ht := closing_tilt_bounds lam hl r
  have h := hconv r hr (defect slope r) ⟨hd.1,le_of_lt hd.2⟩
    (lam*Real.rpow 2 (defect slope r)) (hl.trans ht.1) ht.2
  change |auxLogPressure (defect slope r) r (lam*Real.rpow 2 (defect slope r))-
    candidatePressure (lam*Real.rpow 2 (defect slope r))|<eps at h
  unfold sourceLogPressure
  rw [closing_phase_transport r lam (by omega)]
  exact h

end ExternalBridgePressureAnalyticUniformPressure
