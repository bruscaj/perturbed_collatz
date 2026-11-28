import CriticalSpaceDefinitions

/-! UNFROZEN supporting goals, not proofs. These do NOT yet specify all of
C01-C08: finite-window Gibbs, critical bridge and localized estimates remain. -/
namespace ExternalCriticalSpaceDraft
open ExternalBridgePressureDraft ExternalFiniteBridgeDraft MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section

def SpaceTopology : Prop := CompactSpace Config ∧ TopologicalSpace.MetrizableSpace Config ∧
  SecondCountableTopology Config ∧ BorelSpace Config ∧ IsProbabilityMeasure uniformPhase

def PhaseRepresentativeLaw : Prop :=
  (∀ x : Phase, 0 ≤ phaseRepresentative x ∧ phaseRepresentative x < 1 ∧
    ((phaseRepresentative x : ℝ) : Phase) = x) ∧
  ∀ a : ℝ, phaseRepresentative (a : Phase) = Int.fract a

def ShiftGroupAndContinuity : Prop :=
  (∀ w : Config, timeShift 0 w = w) ∧
  (∀ s t : ℤ, ∀ w : Config, timeShift s (timeShift t w) = timeShift (s+t) w) ∧
  ∀ s : ℤ, Continuous (timeShift s) ∧ Measurable (timeShift s)

def RewardRoofAndRegularity : Prop :=
  Measurable localReward ∧
  (∀ w : Config, 0 ≤ localReward w ∧ localReward w ≤ 1) ∧
  (∀ w : Config, w.2 0 = OnePoint.infty → localReward w = 0) ∧
  ∀ w : Config, w.1 ≠ 0 → ContinuousAt localReward w

def WeakRewardPassage : Prop :=
  ∀ mu : ℕ → ProbabilityMeasure Config, ∀ nu : ProbabilityMeasure Config,
    Tendsto mu atTop (𝓝 nu) → HasUniformPhase (nu : Measure Config) →
    Tendsto (fun k => ∫ w, localReward w ∂(mu k : Measure Config)) atTop
      (𝓝 (∫ w, localReward w ∂(nu : Measure Config)))

def RootedNormalization : Prop := ∀ n : ℕ, 0 < n → ∀ lam : ℝ, 0 ≤ lam →
  rootedMeasure n lam Set.univ = 1 ∧ HasUniformPhase (rootedMeasure n lam)

def RootShiftError : Prop := ∀ n : ℕ, 0 < n → ∀ lam : ℝ, 0 ≤ lam →
  ∀ f : Config → ℝ, Continuous f → ∀ B : ℝ, 0 ≤ B →
    (∀ w, |f w| ≤ B) →
    |(∫ w, f (timeShift 1 w) ∂rootedMeasure n lam) -
      (∫ w, f w ∂rootedMeasure n lam)| ≤ 2*B/(n : ℝ)

def RootedStationarySubsequence : Prop :=
  ∀ n : ℕ → ℕ, (∀ k, k+1 ≤ n k) →
  ∀ lam : ℕ → ℝ, (∀ k, 0 ≤ lam k) →
    ∃ mu : ℕ → ProbabilityMeasure Config,
      (∀ k, (mu k : Measure Config) = rootedMeasure (n k) (lam k)) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ nu : ProbabilityMeasure Config,
        Tendsto (fun k => mu (phi k)) atTop (𝓝 nu) ∧
        IsStationary (nu : Measure Config) ∧ HasUniformPhase (nu : Measure Config)

def FiniteInfinityExclusion : Prop := ∀ mu : ProbabilityMeasure Config,
  IsStationary (mu : Measure Config) →
  (∀ a : ℕ, (mu : Measure Config) (forbiddenUpwardCylinder a) = 0) →
  (mu : Measure Config) (allFinite ∪ allInfinite) = 1

def GapPacking : Prop := ∀ mu : ProbabilityMeasure Config,
  IsStationary (mu : Measure Config) → ∀ H : ℕ,
  Summable (fun m : ℕ => (m : ℝ)*((mu : Measure Config) (successiveGap H m)).toReal) ∧
  (∑' m : ℕ, (m : ℝ)*((mu : Measure Config) (successiveGap H m)).toReal) ≤ 1

def ExcursionFirstMoment : Prop := ∀ mu : ProbabilityMeasure Config,
  IsStationary (mu : Measure Config) → ∀ H L : ℕ, 0 < L →
  Summable (fun n : ℕ => (n : ℝ)*((mu : Measure Config) (longExcursion H L n)).toReal)

def PolynomialExcursionContradiction : Prop := ∀ mu : ProbabilityMeasure Config,
  IsStationary (mu : Measure Config) → ∀ H L : ℕ, 0 < L →
  ∀ c : ℝ, 0 < c →
  (∀ n : ℕ, L+2 ≤ n → c*Real.rpow (n : ℝ) (-((12 : ℝ)/7)) ≤
    ((mu : Measure Config) (longExcursion H L n)).toReal) → False

end
end ExternalCriticalSpaceDraft
