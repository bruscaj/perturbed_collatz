import PressureDefinitions
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! UNFROZEN candidate statement types, divided by scope in TARGETS.md.
No statement is implemented or assumed by another definition. -/
namespace ExternalBridgePressureDraft
open ExternalFiniteBridgeDraft Filter
open scoped Topology

-- Exact finite interfaces: new partition sums over the canonical word model.
def SourcePartitionBasics : Prop := (∀ lam : ℝ, sourcePartition 0 lam = 0) ∧
  (∀ r : ℕ, Finite {w : Word r // SourceWord slope r w}) ∧
  (∀ r : ℕ, ∀ lam : ℝ, Summable (fun w : {w : Word r // SourceWord slope r w} =>
    Real.exp (lam * reward r w.val))) ∧
  ∀ r : ℕ, StrictRung slope r → ∀ lam : ℝ, 0 < sourcePartition r lam

def PhasePathCompleteness : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → ∀ n : ℕ,
  (∀ j : Fin (n + 1) → ℕ, NaturalPathLegal x n j → ∀ t, j t ≤ t.val) ∧
  (∀ j : Fin (n + 1) → ℕ, NaturalPathLegal x n j ↔
    ∃ k : Path n, PathLegal x n k ∧ ∀ t, (k t).val = j t)

def ZeroPhaseBridgeDictionary : Prop := ∀ n : ℕ,
  ∃ e : {j : Path n // PathLegal 0 n j} ≃ {J : Depth n // DepthBridge slope n J},
    (∀ j t, (e j).val t = ((j.val t).val : ℤ)) ∧
    (∀ j, pathReward 0 n j.val = depthReward slope n (e j).val)

def PhasePartitionBasics : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → ∀ n : ℕ,
  (∀ lam : ℝ, rewardPartition x n lam = Real.exp (lam * reference x n) * costPartition x n lam) ∧
  (∀ lam : ℝ, 0 ≤ lam → 1 ≤ costPartition x n lam ∧ 1 ≤ rewardPartition x n lam) ∧
  (∀ lam : ℝ, 0 ≤ lam → costPartition x n lam ≤ (4 : ℝ) ^ n ∧
    rewardPartition x n lam ≤ (4 : ℝ) ^ n * Real.exp (lam * (n : ℝ))) ∧
  (∀ j : Path n, 0 ≤ pathCost x n j ∧ pathCost x n j ≤ (n : ℝ)) ∧
  (∀ lam : ℝ, rewardPartition x 0 lam = 1 ∧ costPartition x 0 lam = 1)

def RungPartitionTransport : Prop := ∀ r : ℕ, StrictRung slope r → ∀ lam : ℝ,
  sourcePartition r lam = rewardPartition 0 r lam ∧
  sourcePartition r lam = Real.exp (lam * phaseZeroReference slope r) * costPartition 0 r lam

-- Required literal R8 targets: ALL nonnegative tilts, not merely lambda>=6.
def RungPressureExists : Prop := ∃ P : ℝ → ℝ, SourcePressureLaw P

def FullR8Differentiability : Prop := ∃ P : ℝ → ℝ,
  SourcePressureLaw P ∧ DifferentiableOn ℝ P (Set.Ici 0)

-- Stronger finite/all-phase auxiliaries; not substitutes for the source targets.
def AllLengthClosingPhaseTransport : Prop := ∀ r : ℕ, 0 < r → ∀ lam : ℝ,
  sourcePartition r lam = rewardPartition (defect slope r) r (lam * Real.rpow 2 (defect slope r))

def PhaseCocycle : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → ∀ m n : ℕ,
  0 ≤ phaseShift x m ∧ phaseShift x m < 1 ∧
  phaseFloor x (m + n) = phaseFloor x m + phaseFloor (phaseShift x m) n ∧
  phaseTick x (m + n) = phaseTick (phaseShift x m) n ∧
  (phaseIncrement x n = 1 ∨ phaseIncrement x n = 2)

def UniformReferenceAverage : Prop :=
  UniformPhaseLimit (fun x n => reference x n / (n : ℝ)) meanReference

def ZeroDepthConcatenation : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → ∀ m n : ℕ,
  ∀ lam : ℝ, 0 ≤ lam →
    rewardPartition x m lam * rewardPartition (phaseShift x m) n lam ≤ rewardPartition x (m + n) lam ∧
    costPartition x m lam * costPartition (phaseShift x m) n lam ≤ costPartition x (m + n) lam

def AllPhasePressureExists : Prop := ∃ P : ℝ → ℝ, UniformRewardPressureLaw P

def CompactTiltUniformPressure : Prop := ∃ P : ℝ → ℝ, CompactTiltPressureLaw P

def RewardCostPressureCompatibility : Prop := ∃ P p : ℝ → ℝ,
  SourcePressureLaw P ∧ UniformRewardPressureLaw P ∧ UniformCostPressureLaw p ∧
  ∀ lam : ℝ, 0 ≤ lam → P lam = lam * meanReference + p lam

-- Large-tilt machinery has a deliberately distinct scope.
def LargeTiltCutBound : Prop := ∀ lam : ℝ, 6 ≤ lam →
  (0 ≤ largeTiltQ lam ∧ largeTiltQ lam < 1) ∧
  ∀ x : ℝ, 0 ≤ x → x < 1 → ∀ m n : ℕ,
    costPartition x (m + n) lam ≤ Real.exp (largeTiltCutConstant lam) *
      costPartition x m lam * costPartition (phaseShift x m) n lam

def LargeTiltOnlyPressure : Prop := ∃ p : ℝ → ℝ, LargeTiltCostLaw p

-- Critical/localized candidates remain separate and carry source existence.
def LocalizedDifferentiabilityCandidate : Prop := ∃ P : ℝ → ℝ, ∃ lamc : ℝ,
  SourcePressureLaw P ∧ CriticalGeometry P lamc ∧
  ∀ lam : ℝ, lamc < lam → DifferentiableAt ℝ P lam

def CriticalMatchingCandidate : Prop := ∃ P : ℝ → ℝ, ∃ lamc : ℝ,
  SourcePressureLaw P ∧ CriticalGeometry P lamc ∧ HasDerivAt P 0 lamc

-- M4 rung reading and R9 expansion are candidates, not replacements for R8.
def M4RungEntropyCandidate : Prop := ∃ ρ : ℝ → ℝ,
  ∀ c : ℝ, (3 : ℝ) / 4 ≤ c → c ≤ 1 → RungEntropyLaw ρ c

def R9NearOneCandidate : Prop := ∃ ρ : ℝ → ℝ, NearOneRungEntropyLaw ρ ∧
  Tendsto (nearOneResidual ρ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

end ExternalBridgePressureDraft
