import OptimizationDefinitions

/-! UNFROZEN required core statement types, not theorem implementations. -/
namespace ExternalO3OptimizationDraft
open scoped BigOperators Topology
open ExternalO3GeneralDraft Filter
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def GenericStrictCycleCriterion : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (g : FiniteGraph V E) (D : Finset E),
    (StrictFeasible g D ↔ CycleSafe g D) ∧ (CycleSafe g D ↔ HitsNonnegativeCycles g D)

def GenericElementaryReduction : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (g : FiniteGraph V E) (D : Finset E),
    (CycleSafe g D ↔ ∀ c : WalkData V E, IsCycle g c → IsElementary c →
      (∀ i, c.edge i ∉ D) → cycleGain g c < 0) ∧
    (∀ c : WalkData V E, IsCycle g c → IsElementary c → c.length ≤ Fintype.card V)

def GenericDeletionOptimum : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] (g : FiniteGraph V E), (∀ e, 0 ≤ g.weight e) →
    ({r | ∃ ψ : V → ℝ, r = failureCost g ψ}).Nonempty ∧
    BddBelow {r | ∃ ψ : V → ℝ, r = failureCost g ψ} ∧
    ({r | ∃ D : Finset E, CycleSafe g D ∧ r = deletionCost g D}).Nonempty ∧
    BddBelow {r | ∃ D : Finset E, CycleSafe g D ∧ r = deletionCost g D} ∧
    finitePotentialInfimum g = deletionInfimum g ∧
    ∃ (D : Finset E) (ψ : V → ℝ), CycleSafe g D ∧
      deletionCost g D = deletionInfimum g ∧ failureCost g ψ = finitePotentialInfimum g

def VertexEncodingAndExtension : Prop := ∀ (h : Depth) (M : ℕ), 2 ≤ M →
  Function.Injective (decodeVertex h M) ∧
  (∀ w : Window h, (∃ v : Vertex h M, decodeVertex h M v = w) ↔
    ∀ i, 1 ≤ w i ∧ w i ≤ M) ∧
  ∀ ψ : Vertex h M → ℝ, ∃ φ : Correction h, ∀ v, φ (decodeVertex h M v) = ψ v

def EdgeEncodingAndWeights : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  Function.Injective (edgeLabel h M J) ∧
  (∀ e : Edge h, Retained h M J e ↔ ∃ a, edgeLabel h M J a = e) ∧
  ∀ a : TruncatedEdge h M J,
    decodeVertex h M (edgeSource h M J a) = labelSource h (edgeLabel h M J a) ∧
    decodeVertex h M (edgeTarget h M J a) = labelTarget h (edgeLabel h M J a) ∧
    (rationalWeight h M J a : ℝ) = weight h (edgeLabel h M J a) ∧
    ∀ φ : Correction h,
      edgeGain (truncatedGraph h M J) (fun v => φ (decodeVertex h M v)) a =
        gain h φ (edgeLabel h M J a)

def NaturalCycleSigns : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  ∀ c : WalkData (Vertex h M) (TruncatedEdge h M J), IsCycle (truncatedGraph h M J) c →
    c.length ≤ ∑ i, halvingExponent h M J (c.edge i) ∧
    (3 : ℕ) ^ c.length ≠ 2 ^ (∑ i, halvingExponent h M J (c.edge i)) ∧
    (cycleGain (truncatedGraph h M J) c < 0 ↔
      (3 : ℕ) ^ c.length < 2 ^ (∑ i, halvingExponent h M J (c.edge i))) ∧
    (0 ≤ cycleGain (truncatedGraph h M J) c ↔
      (2 : ℕ) ^ (∑ i, halvingExponent h M J (c.edge i)) ≤ 3 ^ c.length)

def CommonDyadicDenominator : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  (∀ e : TruncatedEdge h M J, weightExponent h M J e ≤ commonExponent h M J ∧
    rationalWeight h M J e =
      ((2 : ℕ) ^ (commonExponent h M J - weightExponent h M J e) : ℚ) /
        ((2 : ℕ) ^ commonExponent h M J : ℚ)) ∧
  ∀ D : Finset (TruncatedEdge h M J), deletionCost (truncatedGraph h M J) D =
    (deletionUnits h M J D : ℝ) / ((2 : ℕ) ^ commonExponent h M J : ℝ)

def NumeratorMinimumWellPosed : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  (∃ D : Finset (TruncatedEdge h M J), CycleSafe (truncatedGraph h M J) D) ∧
  (∃ D : Finset (TruncatedEdge h M J), CycleSafe (truncatedGraph h M J) D ∧
    deletionUnits h M J D = optimalNumerator h M J) ∧
  ∀ D : Finset (TruncatedEdge h M J), CycleSafe (truncatedGraph h M J) D →
    optimalNumerator h M J ≤ deletionUnits h M J D

def FiniteOptimizationExact : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  (finiteOptimum h M J : ℝ) = finitePotentialInfimum (truncatedGraph h M J) ∧
  (∀ ψ : Vertex h M → ℝ, (finiteOptimum h M J : ℝ) ≤ failureCost (truncatedGraph h M J) ψ) ∧
  ∃ ψ : Vertex h M → ℝ, failureCost (truncatedGraph h M J) ψ = (finiteOptimum h M J : ℝ)

def TruncationMassIdentity : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  retainedMass h M J =
    ((1 / 2 : ℝ) - 2 ^ (-(M : ℤ))) * (1 - 2 ^ (-(M : ℤ))) ^ (h.val - 1) +
    ((1 / 2 : ℝ) - 2 ^ (-(J : ℤ))) * (1 - 2 ^ (-(M : ℤ))) ^ h.val ∧
  Summable (fun e : Edge h => if Retained h M J e then 0 else weight h e) ∧
  discardedMass h M J = 1 - retainedMass h M J

def DiscardedMassBound : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  0 ≤ discardedMass h M J ∧ discardedMass h M J ≤ tailAllowance h M J

def LiteralInfimumSandwich : Prop := ∀ (h : Depth) (M J : ℕ), 2 ≤ M → 2 ≤ J →
  (finiteOptimum h M J : ℝ) ≤ ExternalO3RateDraft.failureInfimum h ∧
  ExternalO3RateDraft.failureInfimum h ≤ (finiteOptimum h M J : ℝ) + tailAllowance h M J

def DiagonalConvergence : Prop := ∀ h : Depth,
  Tendsto (fun n : ℕ => (finiteOptimum h (n + 2) (n + 2) : ℝ)) atTop
    (nhds (ExternalO3RateDraft.failureInfimum h))

/-- OPTIONAL, not needed for certified approximation or convergence. -/
def MonotonicFiniteOptimum : Prop := ∀ (h : Depth) (M J M' J' : ℕ),
  2 ≤ M → 2 ≤ J → M ≤ M' → J ≤ J' → finiteOptimum h M J ≤ finiteOptimum h M' J'

end
end ExternalO3OptimizationDraft
