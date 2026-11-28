import RateDefinitions

/-! UNFROZEN proposed trusted statement types. No proofs or assumed hypotheses
standing in for the desired density/rate conclusions. -/
namespace ExternalO3RateDraft
open Filter
open scoped Topology BigOperators
open ExternalO3GeneralDraft

/-- Establishes that sInf is a genuine infimum of a nonempty bounded set. -/
def InfimumWellPosed : Prop := ∀ h : Depth,
  (∀ φ : Correction h, ∃! d : ℝ, HasFailureDensity h φ d) ∧
  (achievedDensities h).Nonempty ∧ BddBelow (achievedDensities h) ∧
  ∀ d ∈ achievedDensities h, 0 ≤ d ∧ d ≤ 1

def MarkerSelectorLaw : Prop := ∀ (h : Depth) (w : Window h), 2 ≤ h.val →
  0 < (firstFutureMax h w).val ∧
  (∀ i : Fin h.val, 0 < i.val → w i ≤ w (firstFutureMax h w)) ∧
  (∀ i : Fin h.val, 0 < i.val → i.val < (firstFutureMax h w).val →
    w i < w (firstFutureMax h w))

def MarkerUpperBound : Prop := ∀ h : Depth, 2 ≤ h.val →
  ∃ d : ℝ, HasFailureDensity h (markerCorrection h) d ∧
    d ≤ min (1 / 2 : ℝ) (1 / ((h.val : ℝ) - 1) + 1 / (2 * (h.val : ℝ)))

def HistoryWeightLaw : Prop := ∀ h : Depth,
  Summable (historyWeight h) ∧ (∑' r : History h, historyWeight h r) = 1

/-- This is the crucial block-to-odd-seed normalization: TWO and FOUR,
not a uniform average over the number of strides in a sampled block. -/
def CyclicNormalization : Prop := ∀ (h : Depth) (φ : Correction h),
  Summable (fun r : History h => historyWeight h r *
    (blockFailures h φ r 0 2 : ℝ)) ∧
  (∑' r : History h, historyWeight h r * (blockFailures h φ r 0 2 : ℝ)) =
    2 * ascendingMass h φ + 4 * exitMass h φ 0

def CyclicTelescoping : Prop := ∀ (h : Depth) (φ : Correction h) (r : History h),
  (∑ i : Fin (h.val + 1), blockGain h φ r i.val 2) = cycleGain h r

def CyclicForcing : Prop := ∀ (h : Depth) (φ : Correction h) (r : History h),
  (∀ i : Fin (h.val + 1), blockFailures h φ r i.val 2 ≤ cyclicLength h r i.val) ∧
  (0 < cycleGain h r → 1 ≤ cycleFailures h φ r)

def CyclicDensityLowerBound : Prop := ∀ (h : Depth) (φ : Correction h) (d : ℝ),
  HasFailureDensity h φ d → positiveCycleMass h / (4 * ((h.val : ℝ) + 1)) ≤ d

/-- Required finite-moment/Cantelli envelope with n=h+1. The older exponential
Chernoff envelope is retained in the review history, not required by this type. -/
def PositiveCycleMassLowerBound : Prop := ∀ h : Depth,
  ((h.val : ℝ) + 1) / ((h.val : ℝ) + 33) ≤ positiveCycleMass h

/-- Main proposed headline: all positive integer depths, unrestricted φ. -/
def ExplicitInverseDepthRate : Prop := ∀ h : Depth,
  (127 : ℝ) / (32768 * (h.val : ℝ)) ≤ failureInfimum h ∧
  failureInfimum h ≤ (5 : ℝ) / (2 * (h.val : ℝ))

def InfimumTendsToZero : Prop :=
  Tendsto (fun n : ℕ => failureInfimum (succDepth n)) atTop (nhds 0)

/-- OPTIONAL separate target. Eventual lower-bound formulation of liminf,
so no accidental extended-real or boundedness convention is hidden. -/
def StrongAsymptoticLowerBound : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in atTop,
    strongLowerConstant - ε ≤ ((n : ℝ) + 1) * failureInfimum (succDepth n)

end ExternalO3RateDraft
