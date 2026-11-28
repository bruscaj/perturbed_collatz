import Mathlib.Data.Nat.PadicValNat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Function.Iterate

/-!
Initial source-model specification draft, subject to compilation and review.
No conclusion of an external problem is assumed in these definitions.
-/
namespace ExternalO3Spec

open Filter
open scoped Topology BigOperators

def IsOddSeed (x : ℕ) : Prop := 0 < x ∧ x % 2 = 1

abbrev OddSeed := { x : ℕ // IsOddSeed x }

def strideValuation (x : ℕ) : ℕ := padicValNat 2 (3 * x + 1)

/-- Literal total arithmetic expression; only positive odd inputs are source seeds. -/
def stride (x : ℕ) : ℕ := (3 * x + 1) / 2 ^ strideValuation x

/-- Remaining/current block, including the first stride with valuation at least two. -/
def blockLength (x : ℕ) : ℕ := padicValNat 2 (x + 1)

def nextBlock (x : ℕ) : ℕ := (Nat.iterate stride (blockLength x)) x

/-- The value at zero is redundant; no boundedness or regularity is imposed. -/
abbrev Correction := ℕ → ℝ

noncomputable def rawPotential (φ : Correction) (x : ℕ) : ℝ :=
  Real.log (x : ℝ) + φ (blockLength x)

noncomputable def potential (φ : Correction) (x : OddSeed) : ℝ :=
  rawPotential φ x.val

/-- Domain restriction is explicit. Equality counts as failure. -/
def FailsAt (φ : Correction) (x : ℕ) : Prop :=
  IsOddSeed x ∧ rawPotential φ (stride x) ≥ rawPotential φ x

def Fails (φ : Correction) (x : OddSeed) : Prop := FailsAt φ x.val

/-- Exactly N initial seeds: 1,3,...,2N-1. At N=0 the frequency is 0. -/
noncomputable def failureCount (φ : Correction) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun n => FailsAt φ (2 * n + 1))).card

noncomputable def failureFrequency (φ : Correction) (N : ℕ) : ℝ :=
  (failureCount φ N : ℝ) / (N : ℝ)

def HasFailureDensity (φ : Correction) (d : ℝ) : Prop :=
  Tendsto (failureFrequency φ) atTop (nhds d)

/-- Source normalization, failures at odd seeds ≤ X divided by all odd seeds ≤ X. -/
noncomputable def sourceFrequency (φ : Correction) (X : ℕ) : ℝ := by
  classical
  exact
    (((Finset.range (X + 1)).filter (fun x => FailsAt φ x)).card : ℝ) /
    (((Finset.range (X + 1)).filter IsOddSeed).card : ℝ)

/-- Actual achieved literal natural densities; no existence theorem is built in. -/
def achievedDensities : Set ℝ := { d | ∃ φ : Correction, HasFailureDensity φ d }

noncomputable def failureInfimum : ℝ := sInf achievedDensities

noncomputable def ascendingGain (φ : Correction) (r : ℕ) : ℝ :=
  Real.log ((3 : ℝ) / 2) + φ (r - 1) - φ r

noncomputable def exitGain (φ : Correction) (k r : ℕ) : ℝ :=
  Real.log 3 - (k : ℝ) * Real.log 2 + φ r - φ 1

/-- Independent symbolic candidate law: r≥2 ascending edges have mass 2^-r. -/
noncomputable def ascendingMass (φ : Correction) (r : ℕ) : ℝ := by
  classical
  exact if 0 ≤ ascendingGain φ (r + 2) then (2 : ℝ) ^ (-(r + 2 : ℤ)) else 0

/-- k≥2 exit valuation and r≥1 next block length have joint mass 2^-(k+r). -/
noncomputable def exitMass (φ : Correction) (k r : ℕ) : ℝ := by
  classical
  exact if 0 ≤ exitGain φ (k + 2) (r + 1) then
    (2 : ℝ) ^ (-(k + 2 : ℤ) - (r + 1 : ℤ)) else 0

noncomputable def symbolicFailureDensity (φ : Correction) : ℝ :=
  (∑' r : ℕ, ascendingMass φ r) + ∑' k : ℕ, ∑' r : ℕ, exitMass φ k r

noncomputable def depthOneTerm (r : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(r : ℤ)) *
    ((1 : ℝ) / 2 - (2 : ℝ) ^
      (-Int.floor (1 + (r : ℝ) * (Real.log ((3 : ℝ) / 2) / Real.log 2))))

noncomputable def depthOneSeries : ℝ := ∑' r : ℕ, depthOneTerm (r + 1)

noncomputable def depthOnePartial (M : ℕ) : ℝ :=
  ∑ r ∈ Finset.range M, depthOneTerm (r + 1)

end ExternalO3Spec
