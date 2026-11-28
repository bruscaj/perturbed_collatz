import Definitions

namespace ExternalO3Spec

open Filter
open scoped Topology BigOperators

/-- Exact valuation and the positive odd source domain must be proved. -/
def ValuationFoundation : Prop :=
  ∀ x : ℕ, IsOddSeed x →
    0 < strideValuation x ∧
    2 ^ strideValuation x ∣ 3 * x + 1 ∧
    ¬2 ^ (strideValuation x + 1) ∣ 3 * x + 1 ∧
    IsOddSeed (stride x)

def BlockLengthLaw : Prop :=
  ∀ x : ℕ, IsOddSeed x →
    0 < blockLength x ∧
    (∀ i : ℕ, i + 1 < blockLength x →
      strideValuation ((Nat.iterate stride i) x) = 1) ∧
    2 ≤ strideValuation ((Nat.iterate stride (blockLength x - 1)) x)

def FixedPointConvention : Prop := stride 1 = 1 ∧ blockLength 1 = 1

/-- h=1 does not read an extra future block; the correction value at 0 is immaterial. -/
def CorrectionZeroIrrelevant : Prop :=
  ∀ φ ψ : Correction, (∀ r : ℕ, 0 < r → φ r = ψ r) →
    ∀ x : ℕ, IsOddSeed x → (FailsAt φ x ↔ FailsAt ψ x)

def DensityExists : Prop :=
  ∀ φ : Correction, ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ HasFailureDensity φ d

def DensityUnique : Prop :=
  ∀ (φ : Correction) (d e : ℝ),
    HasFailureDensity φ d → HasFailureDensity φ e → d = e

def SourceDensityEquivalence : Prop :=
  ∀ (φ : Correction) (d : ℝ),
    HasFailureDensity φ d ↔ Tendsto (sourceFrequency φ) atTop (nhds d)

/-- Summability is a target, so no default value of a divergent tsum is evidence. -/
def SymbolicMassSummable : Prop :=
  ∀ φ : Correction,
    Summable (ascendingMass φ) ∧
    (∀ k : ℕ, Summable (exitMass φ k)) ∧
    Summable (fun k : ℕ => ∑' r : ℕ, exitMass φ k r)

def DensityEqualsSymbolic : Prop :=
  ∀ φ : Correction,
    0 ≤ symbolicFailureDensity φ ∧ symbolicFailureDensity φ ≤ 1 ∧
    HasFailureDensity φ (symbolicFailureDensity φ)

def InfimumWellPosed : Prop :=
  achievedDensities.Nonempty ∧ BddBelow achievedDensities ∧
    ∀ d ∈ achievedDensities, 0 ≤ d ∧ d ≤ 1

def DepthOneSeriesSummable : Prop :=
  Summable (fun r : ℕ => depthOneTerm (r + 1))

/-- Unconditional equality for the infimum of actual achieved literal densities. -/
def DepthOneFormula : Prop := failureInfimum = depthOneSeries

/-- Strictness for every arbitrary correction, not just additive run potentials. -/
def DepthOneNotAttained : Prop :=
  ∀ (φ : Correction) (d : ℝ), HasFailureDensity φ d → failureInfimum < d

def DepthOneTail : Prop :=
  ∀ M : ℕ,
    0 ≤ depthOneSeries - depthOnePartial M ∧
    depthOneSeries - depthOnePartial M ≤ (2 : ℝ) ^ (-(M : ℤ) - 1)

end ExternalO3Spec
