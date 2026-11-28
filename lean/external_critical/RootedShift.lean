import RootedLaw

/-! Bounded real integration through the literal probability kernel, then
finite-orbit telescoping. No stationary measure is assumed. -/
namespace ExternalCriticalRootedShift
open ExternalCriticalSpaceDraft ExternalCriticalSpaceTopology ExternalCriticalSpaceArithmetic
open ExternalCriticalRootedLaw ExternalFiniteBridgeDraft ExternalBridgePressureDraft MeasureTheory Filter
open scoped Topology ENNReal BigOperators
noncomputable section

theorem bounded_probability_integrable {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ x, |f x| ≤ B) : Integrable f mu := by
  exact (integrable_const B).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem bounded_kernel_lintegral_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ker : α → Measure β) (hone : ∀ x, ker x Set.univ = 1)
    (f : β → ℝ) (B : ℝ) (hb : ∀ y, f y ≤ B) (x : α) :
    (∫⁻ y, ENNReal.ofReal (f y) ∂ker x) ≤ ENNReal.ofReal B := by
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal B ∂ker x := lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hb y)
    _ = _ := by simp only [lintegral_const, hone x, mul_one]

theorem bounded_kernel_integral_bind {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) [IsProbabilityMeasure mu] (ker : α → Measure β) (hker : Measurable ker)
    (hone : ∀ x, ker x Set.univ = 1) (f : β → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    (∫ y, f y ∂mu.bind ker) = ∫ x, ∫ y, f y ∂ker x ∂mu := by
  let (x : α) : IsProbabilityMeasure (ker x) := ⟨hone x⟩
  have hbind : mu.bind ker Set.univ = 1 := by
    rw [Measure.bind_apply MeasurableSet.univ hker.aemeasurable]
    simp [hone]
  let : IsProbabilityMeasure (mu.bind ker) := ⟨hbind⟩
  have hpos (x : α) := bounded_kernel_lintegral_le ker hone f B
    (fun y => (le_abs_self _).trans (hb y)) x
  have hneg (x : α) := bounded_kernel_lintegral_le ker hone (fun y => -f y) B
    (fun y => (neg_le_abs _).trans (hb y)) x
  have hpos_meas : Measurable (fun x => ∫⁻ y, ENNReal.ofReal (f y) ∂ker x) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf)).comp hker
  have hneg_meas : Measurable (fun x => ∫⁻ y, ENNReal.ofReal (-f y) ∂ker x) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.neg)).comp hker
  have hpos_lt (x : α) : (∫⁻ y, ENNReal.ofReal (f y) ∂ker x) < ∞ :=
    (hpos x).trans_lt ENNReal.ofReal_lt_top
  have hneg_lt (x : α) : (∫⁻ y, ENNReal.ofReal (-f y) ∂ker x) < ∞ :=
    (hneg x).trans_lt ENNReal.ofReal_lt_top
  have hpos_int : Integrable (fun x => (∫⁻ y, ENNReal.ofReal (f y) ∂ker x).toReal) mu := by
    apply (integrable_const B).mono' hpos_meas.ennreal_toReal.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hpos x)).trans_eq (ENNReal.toReal_ofReal hB)
  have hneg_int : Integrable (fun x => (∫⁻ y, ENNReal.ofReal (-f y) ∂ker x).toReal) mu := by
    apply (integrable_const B).mono' hneg_meas.ennreal_toReal.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hneg x)).trans_eq (ENNReal.toReal_ofReal hB)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (bounded_probability_integrable _ f hf B hb)]
  simp_rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (bounded_probability_integrable (ker _) f hf B hb)]
  rw [integral_sub hpos_int hneg_int,
    integral_toReal hpos_meas.aemeasurable (Eventually.of_forall hpos_lt),
    integral_toReal hneg_meas.aemeasurable (Eventually.of_forall hneg_lt),
    Measure.lintegral_bind (m := mu) (f := fun y => ENNReal.ofReal (f y))
      hker.aemeasurable (ENNReal.measurable_ofReal.comp hf).aemeasurable,
    Measure.lintegral_bind (m := mu) (f := fun y => ENNReal.ofReal (-f y))
      hker.aemeasurable (ENNReal.measurable_ofReal.comp hf.neg).aemeasurable]

/-- The same literal zero extension, with an unrestricted natural root index. -/
def orbitConfig (n : ℕ) (x : Phase) (j : Path n) (i : ℕ) : Config :=
  (x + (((i : ℝ)*slope : ℝ) : Phase), fun t =>
    let s := t + (i : ℤ)
    if hs : 0 ≤ s ∧ s ≤ (n : ℤ) then
      OnePoint.some ((j ⟨s.toNat, by omega⟩).val)
    else OnePoint.some 0)

theorem orbit_config_root (n : ℕ) (x : Phase) (j : Path n) (i : Fin n) :
    orbitConfig n x j i.val = rootedConfig n x j i := rfl

theorem orbit_config_shift (n : ℕ) (x : Phase) (j : Path n) (i : ℕ) :
    timeShift 1 (orbitConfig n x j i) = orbitConfig n x j (i+1) := by
  apply Prod.ext
  · change (x + (((i : ℝ)*slope : ℝ) : Phase)) + (((1 : ℤ) : ℝ)*slope : ℝ) =
      x + (((((i+1 : ℕ) : ℝ))*slope : ℝ) : Phase)
    simp only [Int.cast_one, Nat.cast_add, Nat.cast_one, add_mul, one_mul, AddCircle.coe_add]
    exact add_assoc _ _ _
  · funext t
    have he : t + (1 : ℤ) + (i : ℤ) = t + ((i+1 : ℕ) : ℤ) := by omega
    change (if hs : 0 ≤ t+1+(i : ℤ) ∧ t+1+(i : ℤ) ≤ (n : ℤ) then
      OnePoint.some ((j ⟨(t+1+(i : ℤ)).toNat, by omega⟩).val) else OnePoint.some 0) =
      (if hs : 0 ≤ t+((i+1 : ℕ) : ℤ) ∧ t+((i+1 : ℕ) : ℤ) ≤ (n : ℤ) then
      OnePoint.some ((j ⟨(t+((i+1 : ℕ) : ℤ)).toNat, by omega⟩).val) else OnePoint.some 0)
    simp only [he]

theorem finite_orbit_telescope (n : ℕ) (x : Phase) (j : Path n) (f : Config → ℝ) :
    (∑ i : Fin n, (f (timeShift 1 (rootedConfig n x j i))-f (rootedConfig n x j i))) =
      f (orbitConfig n x j n)-f (orbitConfig n x j 0) := by
  simp_rw [← orbit_config_root, orbit_config_shift]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => f (orbitConfig n x j (i+1))-f (orbitConfig n x j i)) n]
  exact Finset.sum_range_sub (fun i => f (orbitConfig n x j i)) n

theorem root_kernel_integral (n : ℕ) (lam : ℝ) (x : Phase) (f : Config → ℝ) :
    (∫ w, f w ∂rootKernel n lam x) = ∑ i : Fin n, ∑ j : Path n,
      (pathMass (phaseRepresentative x) n lam j / (n : ℝ)) * f (rootedConfig n x j i) := by
  have hp (j : Path n) : 0 ≤ pathMass (phaseRepresentative x) n lam j/(n : ℝ) :=
    div_nonneg (path_mass_nonneg _ _ _ _) (Nat.cast_nonneg n)
  have hi (i : Fin n) (j : Path n) : Integrable f
      (ENNReal.ofReal (pathMass (phaseRepresentative x) n lam j/(n : ℝ)) •
        Measure.dirac (rootedConfig n x j i)) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  unfold rootKernel
  rw [integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum_measure (fun j _ => hi i j)]
  simp_rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp _), smul_eq_mul]

theorem root_kernel_shift_bound (n : ℕ) (lam : ℝ) (x : Phase)
    (f : Config → ℝ) (B : ℝ) (hb : ∀ w, |f w| ≤ B) :
    |∫ w, (f (timeShift 1 w)-f w) ∂rootKernel n lam x| ≤ 2*B/(n : ℝ) := by
  rw [root_kernel_integral, Finset.sum_comm]
  have he (j : Path n) :
      (∑ i : Fin n, (pathMass (phaseRepresentative x) n lam j/(n : ℝ)) *
        (f (timeShift 1 (rootedConfig n x j i))-f (rootedConfig n x j i))) =
      (pathMass (phaseRepresentative x) n lam j/(n : ℝ)) *
        (f (orbitConfig n x j n)-f (orbitConfig n x j 0)) := by
    rw [← Finset.mul_sum, finite_orbit_telescope]
  simp_rw [he]
  have hp (j : Path n) : 0 ≤ pathMass (phaseRepresentative x) n lam j/(n : ℝ) :=
    div_nonneg (path_mass_nonneg _ _ _ _) (Nat.cast_nonneg n)
  calc
    _ ≤ ∑ j : Path n, |(pathMass (phaseRepresentative x) n lam j/(n : ℝ)) *
        (f (orbitConfig n x j n)-f (orbitConfig n x j 0))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Path n, (pathMass (phaseRepresentative x) n lam j/(n : ℝ))*(2*B) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hp j)]
      apply mul_le_mul_of_nonneg_left _ (hp j)
      exact (abs_sub _ _).trans (by linarith [hb (orbitConfig n x j n),hb (orbitConfig n x j 0)])
    _ = 2*B/(n : ℝ) := by
      rw [← Finset.sum_mul, ← Finset.sum_div, path_mass_sum]
      ring

theorem root_shift_error : RootShiftError := by
  intro n hn lam _ f hcont B hB hb
  let : IsProbabilityMeasure uniformPhase := uniform_phase_probability
  let : IsProbabilityMeasure (rootedMeasure n lam) := ⟨rooted_measure_univ n lam hn⟩
  have hcf : Continuous (fun w => f (timeShift 1 w)) := hcont.comp (time_shift_continuous 1)
  have hi1 := bounded_probability_integrable (rootedMeasure n lam) _ hcf.measurable B
    (fun w => hb (timeShift 1 w))
  have hi2 := bounded_probability_integrable (rootedMeasure n lam) f hcont.measurable B hb
  rw [← integral_sub hi1 hi2, rooted_measure_bind_kernel]
  have hg : Measurable (fun w => f (timeShift 1 w)-f w) := hcf.measurable.sub hcont.measurable
  have hgb (w : Config) : |f (timeShift 1 w)-f w| ≤ 2*B :=
    (abs_sub _ _).trans (by linarith [hb (timeShift 1 w),hb w])
  rw [bounded_kernel_integral_bind uniformPhase (rootKernel n lam)
    (root_kernel_measurable n lam) (fun x => root_kernel_univ n lam x hn)
    (fun w => f (timeShift 1 w)-f w) hg (2*B) (by positivity) hgb]
  have ht := norm_integral_le_of_norm_le_const (μ := uniformPhase)
    (f := fun x => ∫ w, (f (timeShift 1 w)-f w) ∂rootKernel n lam x) (C := 2*B/(n : ℝ))
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using root_kernel_shift_bound n lam x f B hb)
  simpa [Real.norm_eq_abs, measureReal_def] using ht

end
end ExternalCriticalRootedShift
