import GeneralArithmetic

/-! Exact full-class h=1 compatibility with the unchanged frozen scalar model. -/
namespace ExternalO3GeneralCompatibility

open ExternalO3GeneralDraft
open ExternalO3Spec (IsOddSeed stride blockLength)
open scoped BigOperators

theorem one_index_eq (i : Fin depthOne.val) : i = zeroIndex depthOne := by
  apply Fin.ext
  have ht := i.isLt
  change i.val < 1 at ht
  change i.val = 0
  omega

theorem one_window_constant (w : Window depthOne) :
    (fun _ => w (zeroIndex depthOne)) = w := by
  funext i
  rw [one_index_eq i]

theorem scalarize_lift_one (φ : ExternalO3Spec.Correction) :
    scalarizeOne (liftOne φ) = φ := by
  rfl

theorem lift_scalarize_one (φ : Correction depthOne) :
    liftOne (scalarizeOne φ) = φ := by
  funext w
  change φ (fun _ => w (zeroIndex depthOne)) = φ w
  rw [one_window_constant]

theorem rawPotential_one (φ : ExternalO3Spec.Correction) (x : ℕ) :
    rawPotential depthOne (liftOne φ) x = ExternalO3Spec.rawPotential φ x := by
  simp [rawPotential, liftOne, window, zeroIndex, futureBlockSeed,
    ExternalO3Spec.rawPotential]

theorem failsAt_one (φ : ExternalO3Spec.Correction) (x : ℕ) :
    FailsAt depthOne (liftOne φ) x ↔ ExternalO3Spec.FailsAt φ x := by
  simp only [FailsAt, rawPotential_one, ExternalO3Spec.FailsAt]

theorem failureFrequency_one (φ : ExternalO3Spec.Correction) (N : ℕ) :
    failureFrequency depthOne (liftOne φ) N = ExternalO3Spec.failureFrequency φ N := by
  classical
  unfold failureFrequency failureCount ExternalO3Spec.failureFrequency ExternalO3Spec.failureCount
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / (N : ℝ))
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, failsAt_one]

theorem sourceFrequency_one (φ : ExternalO3Spec.Correction) (X : ℕ) :
    sourceFrequency depthOne (liftOne φ) X = ExternalO3Spec.sourceFrequency φ X := by
  classical
  unfold sourceFrequency ExternalO3Spec.sourceFrequency
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ) /
    (((Finset.range (X + 1)).filter ExternalO3Spec.IsOddSeed).card : ℝ))
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, failsAt_one]

/-- All functions on Fin 1, including those containing zero, are retained. -/
def oneFunctionEquiv : Window depthOne ≃ ℕ where
  toFun w := w (zeroIndex depthOne)
  invFun r := fun _ => r
  left_inv := one_window_constant
  right_inv _ := rfl

def edgeOneEquiv : Edge depthOne ≃ ExternalO3PopulationWeights.Edge :=
  Equiv.sumCongr oneFunctionEquiv (Equiv.prodCongr (Equiv.refl ℕ) oneFunctionEquiv)

theorem windowSum_one (w : Window depthOne) : windowSum depthOne w = w (zeroIndex depthOne) := by
  unfold windowSum
  exact Finset.sum_eq_single_of_mem (zeroIndex depthOne) (Finset.mem_univ _)
    (fun i _ hne => False.elim (hne (one_index_eq i)))

theorem bad_one (φ : ExternalO3Spec.Correction) (e : Edge depthOne) :
    Bad depthOne (liftOne φ) e ↔ ExternalO3PopulationWeights.Bad φ (edgeOneEquiv e) := by
  cases e with
  | inl a =>
    change Bad depthOne (liftOne φ) (.inl a) ↔
      ExternalO3PopulationWeights.Bad φ (.inl (a (zeroIndex depthOne)))
    simp [Bad, gain, liftOne, decrementHead, ascendingWindow, zeroIndex,
      ExternalO3PopulationWeights.Bad, ExternalO3Spec.ascendingGain]
  | inr p =>
    rcases p with ⟨k, b⟩
    change Bad depthOne (liftOne φ) (.inr (k, b)) ↔
      ExternalO3PopulationWeights.Bad φ (.inr (k, b (zeroIndex depthOne)))
    simp [Bad, gain, liftOne, prependOne, positiveWindow, zeroIndex,
      ExternalO3PopulationWeights.Bad, ExternalO3Spec.exitGain]

theorem weight_one (e : Edge depthOne) :
    weight depthOne e = ExternalO3PopulationWeights.weight (edgeOneEquiv e) := by
  cases e with
  | inl a =>
    change weight depthOne (.inl a) =
      ExternalO3PopulationWeights.weight (.inl (a (zeroIndex depthOne)))
    simp only [weight, windowSum_one, ascendingWindow, zeroIndex,
      ExternalO3PopulationWeights.weight]
    congr 1
  | inr p =>
    rcases p with ⟨k, b⟩
    change weight depthOne (.inr (k, b)) =
      ExternalO3PopulationWeights.weight (.inr (k, b (zeroIndex depthOne)))
    simp only [weight, windowSum_one, positiveWindow, zeroIndex,
      ExternalO3PopulationWeights.weight]
    congr 1
    push_cast
    omega

theorem selectedWeight_one (φ : ExternalO3Spec.Correction) (e : Edge depthOne) :
    selectedWeight depthOne (liftOne φ) e =
      ExternalO3PopulationWeights.selectedWeight φ (edgeOneEquiv e) := by
  classical
  by_cases hb : Bad depthOne (liftOne φ) e
  · have hOld := (bad_one φ e).mp hb
    simp only [selectedWeight, ExternalO3PopulationWeights.selectedWeight,
      ite_eq_left hb, ite_eq_left hOld, weight_one]
  · have hOld : ¬ ExternalO3PopulationWeights.Bad φ (edgeOneEquiv e) :=
      fun h => hb ((bad_one φ e).mpr h)
    simp only [selectedWeight, ExternalO3PopulationWeights.selectedWeight,
      ite_eq_right hb, ite_eq_right hOld]

theorem symbolicDensity_one (φ : ExternalO3Spec.Correction) :
    symbolicFailureDensity depthOne (liftOne φ) = ExternalO3Spec.symbolicFailureDensity φ := by
  unfold symbolicFailureDensity
  simp_rw [selectedWeight_one]
  rw [edgeOneEquiv.tsum_eq]
  exact ExternalO3PopulationWeights.selectedWeight_tsum_eq_symbolic φ

theorem depth_one_compatibility : DepthOneCompatibility := by
  exact ⟨scalarize_lift_one, lift_scalarize_one, failureFrequency_one,
    sourceFrequency_one, symbolicDensity_one⟩

end ExternalO3GeneralCompatibility
