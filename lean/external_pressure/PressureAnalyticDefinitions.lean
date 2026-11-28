import PressureWordExpectedTypes
import CompletePressureExpectedTypes

/-! UNFROZEN analytic helper data/predicates only. No proof modules, Challenges,
pressure limit assumptions or critical-law model are imported. Finite-volume
functions may be discontinuous. Candidate pressure is an actual infimum/supremum. -/
namespace ExternalBridgePressureAnalyticDraft
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureCompleteDraft
open Filter
open scoped Topology BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev FunctionSequence := ℕ → ℝ → ℝ

def intervalCount (a b : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun t : ℕ => a ≤ Int.fract ((t : ℝ)*slope) ∧
    Int.fract ((t : ℝ)*slope) < b)).card

def shiftedIntervalCount (x a b : ℝ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun t => a ≤ phaseShift x t ∧ phaseShift x t < b)).card

/-- Dense grid, with a harmless totalized m=0 value. Mesh claims require m>=1. -/
def gridPoint (m : ℕ) (i : Fin (m+1)) : ℝ := (i.val : ℝ)/(m : ℝ)

def UniformlyBoundedClosed (u : FunctionSequence) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, ClosedPhase x → |u n x| ≤ M

/-- Only eventual oscillation is required, never continuity of each u_n. -/
def EventuallyEquicontinuousClosed (u : FunctionSequence) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ x y : ℝ, ClosedPhase x → ClosedPhase y →
      |x-y| < delta → |u n x-u n y| < eps

def UniformCauchyClosed (u : FunctionSequence) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q →
    ∀ x : ℝ, ClosedPhase x → |u p x-u q x| < eps

def UniformClosedConvergence (u : FunctionSequence) (f : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ x : ℝ, ClosedPhase x → |u n x-f x| < eps

def UniformAlong (u : FunctionSequence) (q : ℕ → ℕ) (f : ℝ → ℝ) : Prop :=
  UniformClosedConvergence (fun n x => u (q n) x) f

def auxFamily (lam : ℝ) : FunctionSequence := fun n x => auxLogPressure x n lam
def physicalRewardFamily (lam : ℝ) : FunctionSequence := fun n x => rewardLogPressure x lam n
def physicalCostFamily (lam : ℝ) : FunctionSequence := fun n x => costLogPressure x lam n

/-- The infimum is over actual phases, not the auxiliary endpoint1. -/
def phaseValues (n : ℕ) (lam : ℝ) : Set ℝ :=
  {v | ∃ x : ℝ, ActualPhase x ∧ v = auxLogPartition x n lam}
def phaseInfimum (n : ℕ) (lam : ℝ) : ℝ := sInf (phaseValues n lam)
def pressureValues (lam : ℝ) : Set ℝ :=
  {v | ∃ L : ℕ, 1 ≤ L ∧ v = phaseInfimum L lam/(L : ℝ)}

/-- No pressure law is assumed or selected. Nonnegative-domain well-posedness
is a target; negative tilts receive an explicit irrelevant extension. -/
def candidatePressure (lam : ℝ) : ℝ := if 0 ≤ lam then sSup (pressureValues lam) else 0
def candidateCostPressure (lam : ℝ) : ℝ := candidatePressure lam-lam*meanReference

def CompactTiltClosedConvergence (u : ℝ → FunctionSequence) (P : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ x : ℝ, ClosedPhase x → ∀ lam : ℝ, 0 ≤ lam → lam ≤ L → |u lam n x-P lam| < eps

def CompactTiltActualConvergence (u : ℝ → FunctionSequence) (P : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ x : ℝ, ActualPhase x → ∀ lam : ℝ, 0 ≤ lam → lam ≤ L → |u lam n x-P lam| < eps

end
end ExternalBridgePressureAnalyticDraft
