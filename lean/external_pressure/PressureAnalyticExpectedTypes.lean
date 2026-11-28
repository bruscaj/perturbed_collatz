import PressureAnalyticDefinitions

/-! UNFROZEN analytic support propositions. No theorem implementation or sorry.
Generic sequential hypotheses are ordinary compactness inputs, not a pressure
law assumed in place of the unconditional candidate/source conclusions. -/
namespace ExternalBridgePressureAnalyticDraft
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureCompleteDraft Filter
open scoped Topology
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def UniformIntervalDiscrepancy : Prop := ∀ eps : ℝ, 0 < eps →
  ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ a b : ℝ,
    0 ≤ a → a ≤ b → b ≤ 1 → |(intervalCount a b n : ℝ)/(n : ℝ)-(b-a)| < eps

def UniformShiftedIntervalDiscrepancy : Prop := ∀ eps : ℝ, 0 < eps →
  ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ x a b : ℝ,
    ActualPhase x → 0 ≤ a → a ≤ b → b ≤ 1 →
      |(shiftedIntervalCount x a b n : ℝ)/(n : ℝ)-(b-a)| < eps

def CapDifferenceDiscrepancy : Prop := ∀ eps : ℝ, 0 < eps →
  ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ x y : ℝ, OrderedPhases x y →
    |(Dcount x y n : ℝ)/(n : ℝ)-(y-x)| < eps

def AuxiliaryOscillationEstimate : Prop := ∀ lam : ℝ, 0 ≤ lam →
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ x y : ℝ, ClosedPhase x → ClosedPhase y →
      |auxFamily lam n x-auxFamily lam n y| ≤ (Real.log 2+lam)*|x-y|+eps

def AuxiliaryBoundednessAndEquicontinuity : Prop := ∀ lam : ℝ, 0 ≤ lam →
  UniformlyBoundedClosed (auxFamily lam) ∧ EventuallyEquicontinuousClosed (auxFamily lam)

def GridMeshCover : Prop := ∀ m : ℕ, 1 ≤ m →
  (∀ i : Fin (m+1), ClosedPhase (gridPoint m i)) ∧
  ∀ x : ℝ, ClosedPhase x → ∃ i : Fin (m+1), |x-gridPoint m i| ≤ 1/(m : ℝ)

/-- One strictly increasing extraction works for EVERY point of every grid. -/
def DenseGridSubsequence : Prop := ∀ u : FunctionSequence, UniformlyBoundedClosed u →
  ∀ s : ℕ → ℕ, Tendsto s atTop atTop → ∃ k : ℕ → ℕ, StrictMono k ∧
    ∀ m : ℕ, ∀ i : Fin (m+1), ∃ a : ℝ,
      Tendsto (fun j : ℕ => u (s (k j)) (gridPoint m i)) atTop (nhds a)

def GridToUniformCauchy : Prop := ∀ u : FunctionSequence,
  EventuallyEquicontinuousClosed u →
  (∀ m : ℕ, ∀ i : Fin (m+1), CauchySeq (fun n : ℕ => u n (gridPoint m i))) →
    UniformCauchyClosed u

def UniformCauchyContinuousLimit : Prop := ∀ u : FunctionSequence,
  UniformCauchyClosed u → EventuallyEquicontinuousClosed u →
  ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧ UniformClosedConvergence u f

def DiscontinuousSequenceCompactness : Prop := ∀ u : FunctionSequence,
  UniformlyBoundedClosed u → EventuallyEquicontinuousClosed u →
  ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ f : ℝ → ℝ,
      ContinuousOn f (Set.Icc 0 1) ∧ UniformAlong u (s ∘ k) f

def AuxiliarySubsequenceCompactness : Prop := ∀ lam : ℝ, 0 ≤ lam →
  ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ f : ℝ → ℝ,
      ContinuousOn f (Set.Icc 0 1) ∧ UniformAlong (auxFamily lam) (s ∘ k) f

def FixedShiftNormalizedCompletion : Prop := ∀ lam : ℝ, 0 ≤ lam → ∀ m : ℕ,
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ x : ℝ, ClosedPhase x →
      |(auxLogPartition x (n+m) lam-auxLogPartition x n lam)/(n : ℝ)| < eps

def SubsequenceRotationDomination : Prop := ∀ lam : ℝ, 0 ≤ lam →
  ∀ q : ℕ → ℕ, Tendsto q atTop atTop → ∀ f : ℝ → ℝ,
    UniformAlong (auxFamily lam) q f →
      ∀ x : ℝ, ActualPhase x → ∀ m : ℕ, 1 ≤ m → f (phaseShift x m) ≤ f x

def PositiveRotationOrbitDense : Prop := ∀ x y : ℝ, ActualPhase x → ClosedPhase y →
  ∀ eps : ℝ, 0 < eps → ∃ m : ℕ, 1 ≤ m ∧ |phaseShift x m-y| < eps

def RotationDominationImpliesConstant : Prop := ∀ f : ℝ → ℝ,
  ContinuousOn f (Set.Icc 0 1) →
  (∀ x : ℝ, ActualPhase x → ∀ m : ℕ, 1 ≤ m → f (phaseShift x m) ≤ f x) →
    ∃ c : ℝ, ∀ x : ℝ, ClosedPhase x → f x = c

def AuxiliarySubsequenceConstant : Prop := ∀ lam : ℝ, 0 ≤ lam →
  ∀ q : ℕ → ℕ, Tendsto q atTop atTop → ∀ f : ℝ → ℝ,
    ContinuousOn f (Set.Icc 0 1) → UniformAlong (auxFamily lam) q f →
      ∃ c : ℝ, ∀ x : ℝ, ClosedPhase x → f x = c

def PhaseInfimumWellPosed : Prop :=
  (∀ lam : ℝ, phaseInfimum 0 lam = 0) ∧
  ∀ lam : ℝ, 0 ≤ lam → ∀ n : ℕ,
    (phaseValues n lam).Nonempty ∧ BddBelow (phaseValues n lam) ∧ BddAbove (phaseValues n lam) ∧
    0 ≤ phaseInfimum n lam ∧ phaseInfimum n lam ≤ (n : ℝ)*(Real.log 4+lam) ∧
    (∀ x : ℝ, ActualPhase x → phaseInfimum n lam ≤ auxLogPartition x n lam) ∧
    ∀ a : ℝ, (∀ x : ℝ, ActualPhase x → a ≤ auxLogPartition x n lam) → a ≤ phaseInfimum n lam

def PhaseInfimumSuperadditivity : Prop := ∀ lam : ℝ, 0 ≤ lam → ∀ m n : ℕ,
  phaseInfimum m lam+phaseInfimum n lam ≤ phaseInfimum (m+n) lam

def CandidatePressureWellPosed : Prop := ∀ lam : ℝ, 0 ≤ lam →
  (pressureValues lam).Nonempty ∧ BddAbove (pressureValues lam) ∧ BddBelow (pressureValues lam) ∧
  0 ≤ candidatePressure lam ∧ candidatePressure lam ≤ Real.log 4+lam ∧
  ∀ L : ℕ, 1 ≤ L → phaseInfimum L lam/(L : ℝ) ≤ candidatePressure lam

def FeketeCandidateLimit : Prop := ∀ lam : ℝ, 0 ≤ lam →
  Tendsto (fun n : ℕ => phaseInfimum n lam/(n : ℝ)) atTop (nhds (candidatePressure lam))

def SubsequenceConstantIdentification : Prop := ∀ lam : ℝ, 0 ≤ lam →
  ∀ q : ℕ → ℕ, Tendsto q atTop atTop → ∀ c : ℝ,
    UniformAlong (auxFamily lam) q (fun _ => c) → c = candidatePressure lam

def FullAuxiliaryUniformPressure : Prop := ∀ lam : ℝ, 0 ≤ lam →
  UniformClosedConvergence (auxFamily lam) (fun _ => candidatePressure lam)

def CandidateTiltLipschitz : Prop := ∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu →
  |candidatePressure lam-candidatePressure mu| ≤ |lam-mu|

def CompactAuxiliaryTiltPressure : Prop := ∀ L : ℝ, 0 ≤ L →
  CompactTiltClosedConvergence auxFamily candidatePressure L

def PhysicalRewardPressureComposition : Prop :=
  UniformRewardPressureLaw candidatePressure ∧ CompactTiltPressureLaw candidatePressure

def UniformReferenceComposition : Prop := UniformReferenceAverage

def CostPressureComposition : Prop := UniformCostPressureLaw candidateCostPressure ∧
  (∀ L : ℝ, 0 ≤ L → CompactTiltActualConvergence physicalCostFamily candidateCostPressure L) ∧
  ∀ lam : ℝ, 0 ≤ lam → candidatePressure lam = lam*meanReference+candidateCostPressure lam

def SourceRungPressureComposition : Prop := SourcePressureLaw candidatePressure

def VariableTiltSourceAsymptotic : Prop := ∀ lam : ℝ, 0 ≤ lam → ∀ eps : ℝ, 0 < eps →
  ∃ N : ℕ, 1 ≤ N ∧ ∀ r : ℕ, N ≤ r →
    |sourceLogPressure lam r-candidatePressure (lam*Real.rpow 2 (defect slope r))| < eps

def CandidateQualitativePressure : Prop :=
  ConvexNonnegative candidatePressure ∧ ConvexNonnegative candidateCostPressure ∧
  (∀ lam : ℝ, 0 ≤ lam → 0 ≤ candidateCostPressure lam ∧ candidateCostPressure lam ≤ candidatePressure 0) ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ b → candidatePressure a ≤ candidatePressure b ∧
    candidateCostPressure b ≤ candidateCostPressure a) ∧
  ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |candidateCostPressure a-candidateCostPressure b| ≤ |a-b|

def CandidateCorePressureComponents : Prop := SourcePressureLaw candidatePressure ∧
  UniformRewardPressureLaw candidatePressure ∧ UniformCostPressureLaw candidateCostPressure ∧
  CompactTiltPressureLaw candidatePressure ∧
  ∀ lam : ℝ, 0 ≤ lam → candidatePressure lam = lam*meanReference+candidateCostPressure lam

def FinitePhaseLogIntegrability : Prop := ∀ L : ℕ, 1 ≤ L → ∀ lam : ℝ, 0 ≤ lam →
  IntervalIntegrable (fun x : ℝ => Real.log (rewardPartition x L lam)) MeasureTheory.volume 0 1

def IntegratedLowerBracketValidity : Prop := ∀ L : ℕ, 1 ≤ L → ∀ lam : ℝ, 0 ≤ lam →
  blockLower L lam ≤ candidatePressure lam

def IntegratedLowerBracketCofinality : Prop := ∀ lam : ℝ, 0 ≤ lam →
  Tendsto (fun L : ℕ => blockLower L lam) atTop (nhds (candidatePressure lam))

end
end ExternalBridgePressureAnalyticDraft
