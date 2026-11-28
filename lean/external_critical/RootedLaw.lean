import SpaceTopology
import SpaceArithmetic
import SpaceReward
import PhaseCocycle
import Mathlib.MeasureTheory.Function.Floor

/-! Measurability and normalization foundations for the literal finite rooted law. -/
namespace ExternalCriticalRootedLaw
open ExternalCriticalSpaceDraft ExternalBridgePressureDraft ExternalFiniteBridgeDraft
open ExternalCriticalSpaceArithmetic ExternalCriticalSpaceTopology
open ExternalCriticalSpaceReward ExternalBridgePressurePhase
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem phase_floor_measurable (t : ℕ) : Measurable (fun x : ℝ => phaseFloor x t) := by
  exact (measurable_id.add_const _).floor.sub measurable_id.floor

theorem phase_increment_measurable (t : ℕ) : Measurable (fun x : ℝ => phaseIncrement x t) := by
  exact (phase_floor_measurable (t+1)).sub (phase_floor_measurable t)

theorem phase_weight_measurable (t : ℕ) : Measurable (fun x : ℝ => phaseWeight x t) := by
  exact (Real.continuous_const_rpow (a := (2 : ℝ))).measurable.comp
    (measurable_id.add_const _).fract.neg

theorem path_legal_measurable (n : ℕ) (j : Path n) :
    MeasurableSet {x : ℝ | PathLegal x n j} := by
  have hi (i : Fin n) : MeasurableSet {x : ℝ | ((j i.succ).val : ℤ) ≤
      ((j i.castSucc).val : ℤ) + phaseIncrement x i.val - 1} := by
    exact measurableSet_le measurable_const
      ((measurable_const.add (phase_increment_measurable i.val)).sub_const 1)
  unfold PathLegal NaturalPathLegal
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply (MeasurableSet.iInter hi).congr
  ext x
  simp
  rfl

theorem path_reward_measurable (n : ℕ) (j : Path n) :
    Measurable (fun x : ℝ => pathReward x n j) := by
  exact Finset.measurable_sum _ (fun t _ => (phase_weight_measurable t.val).mul_const _)

theorem reward_partition_measurable (n : ℕ) (lam : ℝ) :
    Measurable (fun x : ℝ => rewardPartition x n lam) := by
  exact Finset.measurable_sum _ (fun j _ =>
    (((path_reward_measurable n j).const_mul lam).exp).ite
      (path_legal_measurable n j) measurable_const)

theorem zero_path_legal (x : ℝ) (n : ℕ) : PathLegal x n (fun _ => 0) := by
  refine ⟨rfl, rfl, ?_⟩
  intro i
  rcases phase_increment_alphabet x i.val with h | h <;> simp [h]

theorem reward_partition_pos (x : ℝ) (n : ℕ) (lam : ℝ) : 0 < rewardPartition x n lam := by
  unfold rewardPartition
  apply Finset.sum_pos'
  · intro j _
    split_ifs <;> positivity
  · exact ⟨fun _ => 0, Finset.mem_univ _, by rw [ite_eq_left (zero_path_legal x n)]; positivity⟩

def pathMass (x : ℝ) (n : ℕ) (lam : ℝ) (j : Path n) : ℝ :=
  if PathLegal x n j then Real.exp (lam*pathReward x n j)/rewardPartition x n lam else 0

theorem path_mass_nonneg (x : ℝ) (n : ℕ) (lam : ℝ) (j : Path n) :
    0 ≤ pathMass x n lam j := by
  unfold pathMass
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le (reward_partition_pos x n lam).le
  · exact le_rfl

theorem path_mass_sum (x : ℝ) (n : ℕ) (lam : ℝ) :
    ∑ j : Path n, pathMass x n lam j = 1 := by
  have he (j : Path n) : pathMass x n lam j =
      (if PathLegal x n j then Real.exp (lam*pathReward x n j) else 0)/rewardPartition x n lam := by
    unfold pathMass
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_div, ← rewardPartition]
  exact div_self (ne_of_gt (reward_partition_pos x n lam))

theorem path_mass_measurable (n : ℕ) (lam : ℝ) (j : Path n) :
    Measurable (fun x : ℝ => pathMass x n lam j) := by
  exact ((((path_reward_measurable n j).const_mul lam).exp).div
    (reward_partition_measurable n lam)).ite (path_legal_measurable n j) measurable_const

theorem rooted_config_continuous (n : ℕ) (j : Path n) (i : Fin n) :
    Continuous (fun x => rootedConfig n x j i) := by
  apply Continuous.prodMk
  · exact continuous_id.add continuous_const
  · apply continuous_pi
    intro t
    exact continuous_const

/-- A proof-local factorization of the unchanged frozen raw bind integrand. -/
def rootKernel (n : ℕ) (lam : ℝ) (x : Phase) : Measure Config :=
  ∑ i : Fin n, ∑ j : Path n,
    ENNReal.ofReal (pathMass (phaseRepresentative x) n lam j / (n : ℝ)) •
      Measure.dirac (rootedConfig n x j i)

theorem rooted_measure_bind_kernel (n : ℕ) (lam : ℝ) :
    rootedMeasure n lam = uniformPhase.bind (rootKernel n lam) := by
  unfold rootedMeasure rootKernel
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : PathLegal (phaseRepresentative x) n j
  · simp [pathMass, h, div_div]
  · simp [pathMass, h]

theorem root_kernel_measurable (n : ℕ) (lam : ℝ) : Measurable (rootKernel n lam) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [rootKernel, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · exact ENNReal.measurable_ofReal.comp
      (((path_mass_measurable n lam j).comp phase_representative_measurable).div_const _)
  · exact (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (rooted_config_continuous n j i).measurable)

theorem path_mass_ennreal_sum (n : ℕ) (lam : ℝ) (x : Phase) :
    ∑ j : Path n, ENNReal.ofReal (pathMass (phaseRepresentative x) n lam j / (n : ℝ)) =
      ENNReal.ofReal (1 / (n : ℝ)) := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun j _ => div_nonneg (path_mass_nonneg _ _ _ _) (Nat.cast_nonneg n)),
    ← Finset.sum_div, path_mass_sum]

theorem root_kernel_univ (n : ℕ) (lam : ℝ) (x : Phase) (hn : 0 < n) :
    rootKernel n lam x Set.univ = 1 := by
  have hreal : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)]
  simp only [rootKernel, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
  simp_rw [path_mass_ennreal_sum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := by simp
  rw [hc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n), hreal]
  simp

theorem rooted_measure_univ (n : ℕ) (lam : ℝ) (hn : 0 < n) :
    rootedMeasure n lam Set.univ = 1 := by
  rw [rooted_measure_bind_kernel,
    Measure.bind_apply MeasurableSet.univ (root_kernel_measurable n lam).aemeasurable]
  simp [root_kernel_univ n lam _ hn, uniform_phase_probability]

theorem root_kernel_phase_apply (n : ℕ) (lam : ℝ) (x : Phase)
    (s : Set Phase) (hs : MeasurableSet s) :
    rootKernel n lam x (Prod.fst ⁻¹' s) = ∑ i : Fin n,
      ENNReal.ofReal (1 / (n : ℝ)) *
        Measure.dirac (x + (((i.val : ℝ)*slope : ℝ) : Phase)) s := by
  unfold rootKernel
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have he (j : Path n) : Measure.dirac (rootedConfig n x j i) (Prod.fst ⁻¹' s) =
      Measure.dirac (x + (((i.val : ℝ)*slope : ℝ) : Phase)) s := by
    rw [Measure.dirac_apply' _ (hs.preimage continuous_fst.measurable),
      Measure.dirac_apply' _ hs]
    rfl
  simp_rw [he]
  rw [← Finset.sum_mul, path_mass_ennreal_sum]

theorem phase_translation_dirac_integral (c : Phase) (s : Set Phase) (hs : MeasurableSet s) :
    (∫⁻ x, Measure.dirac (x+c) s ∂uniformPhase) = uniformPhase s := by
  have hm : Measurable (fun x : Phase => x+c) := (continuous_id.add continuous_const).measurable
  have hd : Measurable (fun x : Phase => Measure.dirac (x+c)) :=
    Measure.measurable_dirac.comp hm
  rw [← Measure.bind_apply (m := uniformPhase) (f := fun x : Phase => Measure.dirac (x+c))
    hs hd.aemeasurable,
    Measure.bind_dirac_eq_map uniformPhase hm]
  have he : Measure.map (fun x : Phase => x+c) uniformPhase = uniformPhase := by
    change Measure.map (fun x : Phase => x+c) volume = volume
    exact MeasureTheory.Measure.IsAddRightInvariant.map_add_right_eq_self c
  exact congrArg (fun m : Measure Phase => m s) he

theorem rooted_measure_uniform_phase (n : ℕ) (lam : ℝ) (hn : 0 < n) :
    HasUniformPhase (rootedMeasure n lam) := by
  unfold HasUniformPhase
  ext s hs
  rw [Measure.map_apply continuous_fst.measurable hs, rooted_measure_bind_kernel,
    Measure.bind_apply (hs.preimage continuous_fst.measurable)
      (root_kernel_measurable n lam).aemeasurable]
  simp_rw [root_kernel_phase_apply n lam _ s hs]
  have hd (i : Fin n) : Measurable (fun x : Phase =>
      Measure.dirac (x + (((i.val : ℝ)*slope : ℝ) : Phase)) s) :=
    (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp
      (continuous_id.add continuous_const).measurable)
  rw [lintegral_finsetSum (f := fun (i : Fin n) (x : Phase) =>
    ENNReal.ofReal (1 / (n : ℝ)) *
      Measure.dirac (x + (((i.val : ℝ)*slope : ℝ) : Phase)) s)
      Finset.univ (fun i _ => measurable_const.mul (hd i))]
  simp_rw [lintegral_const_mul _ (hd _), phase_translation_dirac_integral _ s hs]
  rw [← Finset.sum_mul]
  have hu := root_kernel_univ n lam (0 : Phase) hn
  simp only [rootKernel, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one] at hu
  simp_rw [path_mass_ennreal_sum] at hu
  rw [hu, one_mul]

theorem rooted_normalization : RootedNormalization := by
  intro n hn lam _
  exact ⟨rooted_measure_univ n lam hn, rooted_measure_uniform_phase n lam hn⟩

end
end ExternalCriticalRootedLaw
