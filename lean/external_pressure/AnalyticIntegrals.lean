import AnalyticCore
import AnalyticQualitative
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Actual finite log-partition integrability and integrated brackets. -/
namespace ExternalBridgePressureAnalyticIntegrals
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureCompleteDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressurePhase ExternalBridgePressureWordReward
open ExternalBridgePressureAnalyticQualitative ExternalBridgePressureAnalyticUniformPressure
open MeasureTheory Filter Set
open scoped Topology BigOperators

theorem phase_floor_measurable (t : ℕ) : Measurable (fun x : ℝ => phaseFloor x t) :=
  (measurable_id.add_const _).floor.sub measurable_id.floor

theorem phase_increment_measurable (t : ℕ) : Measurable (fun x : ℝ => phaseIncrement x t) :=
  (phase_floor_measurable (t+1)).sub (phase_floor_measurable t)

theorem phase_weight_measurable (t : ℕ) : Measurable (fun x : ℝ => phaseWeight x t) := by
  exact (Real.continuous_const_rpow (a := (2 : ℝ))).measurable.comp
    (measurable_id.add_const _).fract.neg

theorem path_legal_measurable (n : ℕ) (j : Path n) : MeasurableSet {x : ℝ | PathLegal x n j} := by
  have hi (i : Fin n) : MeasurableSet {x : ℝ | ((j i.succ).val : ℤ)≤
      ((j i.castSucc).val : ℤ)+phaseIncrement x i.val-1} :=
    measurableSet_le measurable_const ((measurable_const.add (phase_increment_measurable i.val)).sub_const 1)
  unfold PathLegal NaturalPathLegal
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply (MeasurableSet.iInter hi).congr
  ext x
  simp
  rfl

theorem path_reward_measurable (n : ℕ) (j : Path n) : Measurable (fun x : ℝ => pathReward x n j) :=
  Finset.measurable_sum _ (fun t _ => (phase_weight_measurable t.val).mul_const _)

theorem reward_partition_measurable (n : ℕ) (lam : ℝ) : Measurable (fun x : ℝ => rewardPartition x n lam) := by
  exact Finset.measurable_sum _ (fun j _ => (((path_reward_measurable n j).const_mul lam).exp).ite
    (path_legal_measurable n j) measurable_const)

theorem phase_weight_bounds (x : ℝ) (t : ℕ) : 0≤phaseWeight x t ∧ phaseWeight x t≤1 := by
  constructor
  · unfold phaseWeight
    exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  · unfold phaseWeight
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact neg_nonpos.mpr (Int.fract_nonneg _)

theorem path_reward_bounds (x : ℝ) (n : ℕ) (j : Path n) : 0≤pathReward x n j ∧ pathReward x n j≤(n : ℝ) := by
  have ht (t : Fin n) : 0≤phaseWeight x t.val*(2 : ℝ)^(-((j t.castSucc).val : ℤ)) ∧
      phaseWeight x t.val*(2 : ℝ)^(-((j t.castSucc).val : ℤ))≤1 := by
    have hw := phase_weight_bounds x t.val
    have hp : (2 : ℝ)^(-((j t.castSucc).val : ℤ))≤1 :=
      zpow_le_one_of_nonpos₀ (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
    refine ⟨mul_nonneg hw.1 (by positivity),?_⟩
    calc
      _ ≤ phaseWeight x t.val*1 := mul_le_mul_of_nonneg_left hp hw.1
      _ ≤ 1 := by simpa only [mul_one] using hw.2
  refine ⟨Finset.sum_nonneg (fun t _ => (ht t).1),?_⟩
  calc
    pathReward x n j ≤ ∑ _t : Fin n,(1 : ℝ) := Finset.sum_le_sum (fun t _ => (ht t).2)
    _ = (n : ℝ) := by simp

theorem reward_partition_lower_one (x : ℝ) (n : ℕ) (lam : ℝ) (hl : 0≤lam) : 1≤rewardPartition x n lam := by
  classical
  unfold rewardPartition
  have hz := zero_depth_legal x n
  have hr := (path_reward_bounds x n (zeroDepth n)).1
  calc
    1 ≤ (if PathLegal x n (zeroDepth n) then Real.exp (lam*pathReward x n (zeroDepth n)) else 0) := by
      rw [ite_eq_left hz]
      exact Real.one_le_exp_iff.mpr (mul_nonneg hl hr)
    _ ≤ ∑ j : Path n,if PathLegal x n j then Real.exp (lam*pathReward x n j) else 0 := by
      apply Finset.single_le_sum (f := fun j : Path n => if PathLegal x n j then Real.exp (lam*pathReward x n j) else 0)
        (s := Finset.univ) (a := zeroDepth n)
      · intro j _
        split_ifs <;> positivity
      · exact Finset.mem_univ _

theorem reward_partition_upper (x : ℝ) (n : ℕ) (lam : ℝ) (hl : 0≤lam) :
    rewardPartition x n lam≤(Fintype.card (Path n) : ℝ)*Real.exp (lam*(n : ℝ)) := by
  classical
  unfold rewardPartition
  calc
    (∑ j : Path n,if PathLegal x n j then Real.exp (lam*pathReward x n j) else 0) ≤
        ∑ _j : Path n,Real.exp (lam*(n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (path_reward_bounds x n j).2 hl)
      · exact le_of_lt (Real.exp_pos _)
    _ = _ := by simp

theorem log_partition_norm_bound (x : ℝ) (n : ℕ) (lam : ℝ) (hl : 0≤lam) :
    ‖Real.log (rewardPartition x n lam)‖≤Real.log ((Fintype.card (Path n) : ℝ)*Real.exp (lam*(n : ℝ))) := by
  have hlow := reward_partition_lower_one x n lam hl
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hlow)]
  exact Real.log_le_log (lt_of_lt_of_le (by norm_num) hlow) (reward_partition_upper x n lam hl)

theorem log_partition_integrable (n : ℕ) (lam : ℝ) (hl : 0≤lam) :
    IntervalIntegrable (fun x : ℝ => Real.log (rewardPartition x n lam)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
  apply Integrable.of_bound ((reward_partition_measurable n lam).log.aestronglyMeasurable)
    (Real.log ((Fintype.card (Path n) : ℝ)*Real.exp (lam*(n : ℝ))))
  exact Eventually.of_forall (fun x => log_partition_norm_bound x n lam hl)

theorem finite_phase_log_integrability : FinitePhaseLogIntegrability := by
  intro L _ lam hl
  exact log_partition_integrable L lam hl

theorem ae_ne_one : ∀ᵐ x : ℝ ∂volume,x≠1 := by
  apply ae_iff.mpr
  simp

theorem integrated_lower_bracket_cofinality : IntegratedLowerBracketCofinality := by
  intro lam hl
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N,hN,hconv⟩ := physical_reward_pressure_composition.1 lam hl (eps/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hi : IntervalIntegrable (fun x : ℝ => rewardLogPressure x lam n) volume 0 1 :=
    (log_partition_integrable n lam hl).div_const (n : ℝ)
  have he : blockLower n lam-candidatePressure lam =
      ∫ x in (0 : ℝ)..1,(rewardLogPressure x lam n-candidatePressure lam) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    unfold blockLower rewardLogPressure
    rw [intervalIntegral.integral_div,intervalIntegral.integral_const]
    simp only [sub_zero,one_smul]
  have hb : ∀ᵐ x : ℝ ∂volume,x∈Set.uIoc (0 : ℝ) 1 →
      ‖rewardLogPressure x lam n-candidatePressure lam‖≤eps/2 := by
    filter_upwards [ae_ne_one] with x hx1
    intro hx
    have hx' : x∈Set.Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
    have hxlt : x<1 := by
      by_contra h
      exact hx1 (le_antisymm hx'.2 (le_of_not_gt h))
    have h := hconv n hn x (le_of_lt hx'.1) hxlt
    simpa only [Real.norm_eq_abs] using le_of_lt h
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
  rw [Real.dist_eq,he]
  have hn' : ‖∫ x in (0 : ℝ)..1,(rewardLogPressure x lam n-candidatePressure lam)‖≤eps/2 := by
    simpa only [sub_zero,abs_one,mul_one] using hint
  rw [Real.norm_eq_abs] at hn'
  linarith

theorem phase_floor_period (x : ℝ) (t : ℕ) : phaseFloor (x+1) t=phaseFloor x t := by
  have he : (x+1)+(t : ℝ)*slope=(x+(t : ℝ)*slope)+1 := by ring
  unfold phaseFloor
  rw [he,Int.floor_add_one,Int.floor_add_one]
  omega

theorem phase_tick_period (x : ℝ) (t : ℕ) : phaseTick (x+1) t=phaseTick x t := by
  have he : (x+1)+(t : ℝ)*slope=(x+(t : ℝ)*slope)+1 := by ring
  unfold phaseTick
  rw [he,Int.fract_add_one]

theorem path_legal_period (x : ℝ) (n : ℕ) (j : Path n) : PathLegal (x+1) n j ↔ PathLegal x n j := by
  simp only [PathLegal,NaturalPathLegal,phaseIncrement,phase_floor_period]

theorem path_reward_period (x : ℝ) (n : ℕ) (j : Path n) : pathReward (x+1) n j=pathReward x n j := by
  unfold pathReward phaseWeight
  simp only [phase_tick_period]

theorem reward_partition_period (n : ℕ) (lam : ℝ) : Function.Periodic (fun x : ℝ => rewardPartition x n lam) 1 := by
  intro x
  classical
  unfold rewardPartition
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : PathLegal x n j
  · have hj1 := (path_legal_period x n j).mpr hj
    simp only [hj,hj1,ite_true,path_reward_period]
  · have hj1 : ¬PathLegal (x+1) n j := fun h => hj ((path_legal_period x n j).mp h)
    simp only [hj,hj1,ite_false]

theorem log_partition_period (n : ℕ) (lam : ℝ) :
    Function.Periodic (fun x : ℝ => Real.log (rewardPartition x n lam)) 1 :=
  fun x => congrArg Real.log (reward_partition_period n lam x)

theorem shifted_log_partition (x : ℝ) (m n : ℕ) (lam : ℝ) :
    Real.log (rewardPartition (phaseShift x m) n lam)=Real.log (rewardPartition (x+(m : ℝ)*slope) n lam) := by
  have h := (log_partition_period n lam).sub_int_mul_eq (x := x+(m : ℝ)*slope)
    (Int.floor (x+(m : ℝ)*slope))
  simpa only [mul_one,phaseShift,phaseTick,Int.fract] using h

theorem shifted_log_partition_integral (m n : ℕ) (lam : ℝ) :
    (∫ x in (0 : ℝ)..1,Real.log (rewardPartition (phaseShift x m) n lam))=
      ∫ x in (0 : ℝ)..1,Real.log (rewardPartition x n lam) := by
  have hf : (fun x : ℝ => Real.log (rewardPartition (phaseShift x m) n lam))=
      fun x : ℝ => Real.log (rewardPartition (x+(m : ℝ)*slope) n lam) := funext (fun x => shifted_log_partition x m n lam)
  rw [hf,intervalIntegral.integral_comp_add_right (fun z : ℝ => Real.log (rewardPartition z n lam)) ((m : ℝ)*slope)]
  simpa only [zero_add,add_comm 1 ((m : ℝ)*slope)] using
    (log_partition_period n lam).intervalIntegral_add_eq ((m : ℝ)*slope) 0

theorem shifted_log_partition_integrable (m n : ℕ) (lam : ℝ) (hl : 0≤lam) :
    IntervalIntegrable (fun x : ℝ => Real.log (rewardPartition (phaseShift x m) n lam)) volume 0 1 := by
  have hf : (fun x : ℝ => Real.log (rewardPartition (phaseShift x m) n lam))=
      fun x : ℝ => Real.log (rewardPartition (x+(m : ℝ)*slope) n lam) := funext (fun x => shifted_log_partition x m n lam)
  rw [hf]
  have hi := (log_partition_period n lam).intervalIntegrable₀ (by norm_num) (log_partition_integrable n lam hl)
    ((m : ℝ)*slope) (1+(m : ℝ)*slope)
  simpa only [sub_self,add_sub_cancel_right] using hi.comp_add_right ((m : ℝ)*slope)

theorem physical_log_cocycle (x : ℝ) (m n : ℕ) (lam : ℝ) (hx : ActualPhase x) (hl : 0≤lam) :
    Real.log (rewardPartition x m lam)+Real.log (rewardPartition (phaseShift x m) n lam)≤
      Real.log (rewardPartition x (m+n) lam) := by
  have hy : ActualPhase (phaseShift x m) := phase_shift_bounds x m
  have h := ExternalBridgePressureWordConcatenation.partition_cocycle x m n lam hx hl
  unfold auxLogPartition at h
  rw [ExternalBridgePressureWordPartitions.word_path_partition_equality x m lam hx,
    ExternalBridgePressureWordPartitions.word_path_partition_equality _ n lam hy,
    ExternalBridgePressureWordPartitions.word_path_partition_equality x (m+n) lam hx] at h
  exact h

theorem integrated_log_superadditivity (m n : ℕ) (lam : ℝ) (hl : 0≤lam) :
    (∫ x in (0 : ℝ)..1,Real.log (rewardPartition x m lam))+
      (∫ x in (0 : ℝ)..1,Real.log (rewardPartition x n lam))≤
      ∫ x in (0 : ℝ)..1,Real.log (rewardPartition x (m+n) lam) := by
  have hm := log_partition_integrable m lam hl
  have hn := shifted_log_partition_integrable m n lam hl
  have hs := log_partition_integrable (m+n) lam hl
  have hae : (fun x : ℝ => Real.log (rewardPartition x m lam)+Real.log (rewardPartition (phaseShift x m) n lam))
      ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun x => Real.log (rewardPartition x (m+n) lam)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae ae_ne_one] with x hx hx1
    have hxlt : x<1 := by
      by_contra h
      exact hx1 (le_antisymm hx.2 (le_of_not_gt h))
    exact physical_log_cocycle x m n lam ⟨hx.1,hxlt⟩ hl
  have h := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ)≤1) (hm.add hn) hs hae
  rw [intervalIntegral.integral_add hm hn,shifted_log_partition_integral] at h
  exact h

theorem block_multiple_integral_bound (L k : ℕ) (lam : ℝ) (hl : 0≤lam) :
    (k : ℝ)*(∫ x in (0 : ℝ)..1,Real.log (rewardPartition x L lam))≤
      ∫ x in (0 : ℝ)..1,Real.log (rewardPartition x (k*L) lam) := by
  induction k with
  | zero => simp [ExternalBridgePressureWordPartitions.reward_partition_zero]
  | succ k ih =>
    have h := integrated_log_superadditivity (k*L) L lam hl
    rw [Nat.succ_mul]
    push_cast
    nlinarith

theorem block_lower_le_multiple (L k : ℕ) (hL : 1≤L) (hk : 1≤k) (lam : ℝ) (hl : 0≤lam) :
    blockLower L lam≤blockLower (k*L) lam := by
  have hLR : (0 : ℝ)<L := by exact_mod_cast hL
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hKL : (0 : ℝ)<(k*L : ℕ) := by exact_mod_cast mul_pos hkR hLR
  unfold blockLower
  apply (div_le_div_iff₀ hLR hKL).mpr
  have h := mul_le_mul_of_nonneg_right (block_multiple_integral_bound L k lam hl) (le_of_lt hLR)
  push_cast
  nlinarith

theorem integrated_lower_bracket_validity : IntegratedLowerBracketValidity := by
  intro L hL lam hl
  have hq : Tendsto (fun k : ℕ => k*L) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    refine eventually_atTop.mpr ⟨B,fun k hk => ?_⟩
    have h := Nat.mul_le_mul_left k hL
    simp only [Nat.mul_one] at h
    omega
  have hlim := (integrated_lower_bracket_cofinality lam hl).comp hq
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact block_lower_le_multiple L k hL hk lam hl

end ExternalBridgePressureAnalyticIntegrals
