import RateDefinitions

/-! UNFROZEN finite optimization specification. Definitions only, not proofs.
The source infimum is imported literally from the frozen rate definitions.
-/
namespace ExternalO3OptimizationDraft
open scoped BigOperators
open ExternalO3GeneralDraft
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure FiniteGraph (V E : Type) where
  source : E → V
  target : E → V
  baseGain : E → ℝ
  weight : E → ℝ

structure WalkData (V E : Type) where
  length : ℕ
  vertex : Fin (length + 1) → V
  edge : Fin length → E

def IsCycle {V E : Type} (g : FiniteGraph V E) (c : WalkData V E) : Prop :=
  0 < c.length ∧
  (∀ i, g.source (c.edge i) = c.vertex i.castSucc ∧
    g.target (c.edge i) = c.vertex i.succ) ∧
  c.vertex (Fin.last c.length) = c.vertex 0

def IsElementary {V E : Type} (c : WalkData V E) : Prop :=
  Function.Injective (fun i : Fin c.length => c.vertex i.castSucc)

def cycleGain {V E : Type} (g : FiniteGraph V E) (c : WalkData V E) : ℝ :=
  ∑ i, g.baseGain (c.edge i)

def StrictFeasible {V E : Type} (g : FiniteGraph V E) (D : Finset E) : Prop :=
  ∃ ψ : V → ℝ, ∀ e, e ∉ D → g.baseGain e + ψ (g.target e) - ψ (g.source e) < 0

def CycleSafe {V E : Type} (g : FiniteGraph V E) (D : Finset E) : Prop :=
  ∀ c : WalkData V E, IsCycle g c → (∀ i, c.edge i ∉ D) → cycleGain g c < 0

def HitsNonnegativeCycles {V E : Type} (g : FiniteGraph V E) (D : Finset E) : Prop :=
  ∀ c : WalkData V E, IsCycle g c → 0 ≤ cycleGain g c → ∃ i, c.edge i ∈ D

def edgeGain {V E : Type} (g : FiniteGraph V E) (ψ : V → ℝ) (e : E) : ℝ :=
  g.baseGain e + ψ (g.target e) - ψ (g.source e)

def failureCost {V E : Type} [Fintype E] (g : FiniteGraph V E) (ψ : V → ℝ) : ℝ :=
  ∑ e, if 0 ≤ edgeGain g ψ e then g.weight e else 0

def deletionCost {V E : Type} (g : FiniteGraph V E) (D : Finset E) : ℝ :=
  ∑ e ∈ D, g.weight e

def finitePotentialInfimum {V E : Type} [Fintype E] (g : FiniteGraph V E) : ℝ :=
  sInf {r | ∃ ψ : V → ℝ, r = failureCost g ψ}

def deletionInfimum {V E : Type} (g : FiniteGraph V E) : ℝ :=
  sInf {r | ∃ D : Finset E, CycleSafe g D ∧ r = deletionCost g D}

abbrev Vertex (h : Depth) (M : ℕ) := Fin h.val → Fin M
abbrev AscendingEdge (h : Depth) (M : ℕ) :=
  {v : Vertex h M // 0 < (v (zeroIndex h)).val}
abbrev TruncatedEdge (h : Depth) (M J : ℕ) :=
  Sum (AscendingEdge h M) (Fin (J - 1) × Vertex h M)

def decodeVertex (h : Depth) (M : ℕ) (v : Vertex h M) : Window h := fun i => (v i).val + 1

def ascTarget (h : Depth) (M : ℕ) (v : Vertex h M) : Vertex h M :=
  fun i => if i.val = 0 then
    ⟨(v i).val - 1, lt_of_le_of_lt (Nat.sub_le _ _) (v i).isLt⟩ else v i

def exitSource (h : Depth) (M : ℕ) (v : Vertex h M) : Vertex h M :=
  fun i => if i.val = 0 then
    ⟨0, lt_of_le_of_lt (Nat.zero_le _) (v (zeroIndex h)).isLt⟩
  else v ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

def edgeSource (h : Depth) (M J : ℕ) : TruncatedEdge h M J → Vertex h M
  | .inl a => a.val
  | .inr (_, v) => exitSource h M v

def edgeTarget (h : Depth) (M J : ℕ) : TruncatedEdge h M J → Vertex h M
  | .inl a => ascTarget h M a.val
  | .inr (_, v) => v

def halvingExponent (h : Depth) (M J : ℕ) : TruncatedEdge h M J → ℕ
  | .inl _ => 1
  | .inr (k, _) => k.val + 2

def weightExponent (h : Depth) (M J : ℕ) : TruncatedEdge h M J → ℕ
  | .inl a => ∑ i, ((a.val i).val + 1)
  | .inr (k, v) => k.val + 2 + ∑ i, ((v i).val + 1)

def rationalWeight (h : Depth) (M J : ℕ) (e : TruncatedEdge h M J) : ℚ :=
  1 / ((2 : ℕ) ^ weightExponent h M J e : ℚ)

def truncatedGraph (h : Depth) (M J : ℕ) : FiniteGraph (Vertex h M) (TruncatedEdge h M J) where
  source := edgeSource h M J
  target := edgeTarget h M J
  baseGain e := Real.log 3 - (halvingExponent h M J e : ℝ) * Real.log 2
  weight e := (rationalWeight h M J e : ℝ)

def edgeLabel (h : Depth) (M J : ℕ) : TruncatedEdge h M J → Edge h
  | .inl a => .inl (fun i => if i.val = 0 then (a.val i).val - 1 else (a.val i).val)
  | .inr (k, v) => .inr (k.val, fun i => (v i).val)

def labelSource (h : Depth) : Edge h → Window h
  | .inl a => ascendingWindow h a
  | .inr (_, b) => prependOne h (positiveWindow h b)

def labelTarget (h : Depth) : Edge h → Window h
  | .inl a => decrementHead h (ascendingWindow h a)
  | .inr (_, b) => positiveWindow h b

def Retained (h : Depth) (M J : ℕ) : Edge h → Prop
  | .inl a => ∀ i, ascendingWindow h a i ≤ M
  | .inr (k, b) => k + 2 ≤ J ∧ ∀ i, positiveWindow h b i ≤ M

/-- One common denominator covers every retained edge, including parallel exits. -/
def commonExponent (h : Depth) (M J : ℕ) : ℕ := J + h.val * M

def deletionUnits (h : Depth) (M J : ℕ) (D : Finset (TruncatedEdge h M J)) : ℕ :=
  ∑ e ∈ D, 2 ^ (commonExponent h M J - weightExponent h M J e)

/-- This is a mathematical minimum candidate, NOT an executable algorithm.
Required well-posedness and computability statements are separate targets. -/
def optimalNumerator (h : Depth) (M J : ℕ) : ℕ :=
  sInf {u | ∃ D : Finset (TruncatedEdge h M J),
    CycleSafe (truncatedGraph h M J) D ∧ u = deletionUnits h M J D}

def finiteOptimum (h : Depth) (M J : ℕ) : ℚ :=
  (optimalNumerator h M J : ℚ) / ((2 : ℕ) ^ commonExponent h M J : ℚ)

def retainedMass (h : Depth) (M J : ℕ) : ℝ :=
  ∑ e : TruncatedEdge h M J, (rationalWeight h M J e : ℝ)

def discardedMass (h : Depth) (M J : ℕ) : ℝ :=
  ∑' e : Edge h, if Retained h M J e then 0 else weight h e

def tailAllowance (h : Depth) (M J : ℕ) : ℝ :=
  ((h.val : ℝ) + 1) * (2 : ℝ) ^ (-(M : ℤ)) + (2 : ℝ) ^ (-(J : ℤ))

end
end ExternalO3OptimizationDraft
