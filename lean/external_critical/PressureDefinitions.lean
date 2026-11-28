import BridgeExpectedTypes

/-! UNFROZEN pressure-model definitions only. No implementation, pressure,
entropy, differentiability or limit theorem is imported or assumed. -/
namespace ExternalBridgePressureDraft
open scoped BigOperators Topology
open Filter
open ExternalFiniteBridgeDraft
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact literal source partition, whose indexing subtype is finite by the
canonical finite-population theorem; finiteness/summability is also an explicit target. -/
def sourcePartition (r : ℕ) (lam : ℝ) : ℝ :=
  ∑' w : {w : Word r // SourceWord slope r w}, Real.exp (lam * reward r w.val)

def sourceLogPressure (lam : ℝ) (r : ℕ) : ℝ := Real.log (sourcePartition r lam) / (r : ℝ)

/-- Explicit nonvacuous limit along actual unbounded source rungs. -/
def HasRungLimit (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (∀ R : ℕ, ∃ r : ℕ, R < r ∧ StrictRung slope r) ∧
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ r : ℕ, N ≤ r → StrictRung slope r → |f r - a| < ε

def SourcePressureLaw (P : ℝ → ℝ) : Prop := ∀ lam : ℝ, 0 ≤ lam →
  (∀ r : ℕ, StrictRung slope r → 0 < sourcePartition r lam) ∧
  HasRungLimit (sourceLogPressure lam) (P lam)

/-- Real phases are represented in [0,1) in all uniform statements. The
subtracted initial floor makes the finite prefix start at zero even outside that interval. -/
def phaseFloor (x : ℝ) (t : ℕ) : ℤ := Int.floor (x + (t : ℝ) * slope) - Int.floor x

def phaseTick (x : ℝ) (t : ℕ) : ℝ := Int.fract (x + (t : ℝ) * slope)
def phaseShift (x : ℝ) (n : ℕ) : ℝ := phaseTick x n

def phaseIncrement (x : ℝ) (t : ℕ) : ℤ := phaseFloor x (t + 1) - phaseFloor x t

def phaseWeight (x : ℝ) (t : ℕ) : ℝ := Real.rpow 2 (-phaseTick x t)

/-- A finite exact enumeration, not a numerical depth cutoff. Completeness of
this n bound is a separate target, proved from upward increments at most one. -/
abbrev Path (n : ℕ) := Fin (n + 1) → Fin (n + 1)

def NaturalPathLegal (x : ℝ) (n : ℕ) (j : Fin (n + 1) → ℕ) : Prop :=
  j 0 = 0 ∧ j (Fin.last n) = 0 ∧
  ∀ i : Fin n, (j i.succ : ℤ) ≤ (j i.castSucc : ℤ) + phaseIncrement x i.val - 1

def PathLegal (x : ℝ) (n : ℕ) (j : Path n) : Prop := NaturalPathLegal x n (fun t => (j t).val)

def pathReward (x : ℝ) (n : ℕ) (j : Path n) : ℝ :=
  ∑ t : Fin n, phaseWeight x t.val * (2 : ℝ) ^ (-((j t.castSucc).val : ℤ))

def reference (x : ℝ) (n : ℕ) : ℝ := ∑ t : Fin n, phaseWeight x t.val

def pathCost (x : ℝ) (n : ℕ) (j : Path n) : ℝ :=
  ∑ t : Fin n, phaseWeight x t.val * (1 - (2 : ℝ) ^ (-((j t.castSucc).val : ℤ)))

def rewardPartition (x : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  ∑ j : Path n, if PathLegal x n j then Real.exp (lam * pathReward x n j) else 0

def costPartition (x : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  ∑ j : Path n, if PathLegal x n j then Real.exp (-lam * pathCost x n j) else 0

def rewardLogPressure (x : ℝ) (lam : ℝ) (n : ℕ) : ℝ := Real.log (rewardPartition x n lam) / (n : ℝ)
def costLogPressure (x : ℝ) (lam : ℝ) (n : ℕ) : ℝ := Real.log (costPartition x n lam) / (n : ℝ)

def meanReference : ℝ := 1 / (2 * Real.log 2)

def UniformPhaseLimit (f : ℝ → ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
    ∀ x : ℝ, 0 ≤ x → x < 1 → |f x n - a| < ε

def UniformRewardPressureLaw (P : ℝ → ℝ) : Prop := ∀ lam : ℝ, 0 ≤ lam →
  UniformPhaseLimit (fun x n => rewardLogPressure x lam n) (P lam)

def UniformCostPressureLaw (p : ℝ → ℝ) : Prop := ∀ lam : ℝ, 0 ≤ lam →
  UniformPhaseLimit (fun x n => costLogPressure x lam n) (p lam)

def CompactTiltPressureLaw (P : ℝ → ℝ) : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ x : ℝ, 0 ≤ x → x < 1 →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ L → |rewardLogPressure x lam n - P lam| < ε

def largeTiltQ (lam : ℝ) : ℝ := 4 * Real.exp (-lam / 4)
def largeTiltCutConstant (lam : ℝ) : ℝ := Real.log (1 + 4 * largeTiltQ lam / (1 - largeTiltQ lam) ^ 2)

def LargeTiltCostLaw (p : ℝ → ℝ) : Prop := ∀ lam : ℝ, 6 ≤ lam →
  UniformPhaseLimit (fun x n => costLogPressure x lam n) (p lam)

def baselineEntropy : ℝ := slope * Real.log slope - (slope - 1) * Real.log (slope - 1)

def CriticalGeometry (P : ℝ → ℝ) (lamc : ℝ) : Prop :=
  0 < lamc ∧ (∀ lam : ℝ, 0 ≤ lam → lam ≤ lamc → P lam = baselineEntropy) ∧
  (∀ lam : ℝ, lamc < lam → baselineEntropy < P lam)

/-- Total log at count zero is not used to certify entropy: the law below
explicitly requires positive rung counts on its declared c range. -/
def sourceLogCount (c : ℝ) (r : ℕ) : ℝ :=
  Real.log (sourceCount r (c * phaseZeroReference slope r) : ℝ) / ((r : ℝ) * Real.log 10)

def RungEntropyLaw (ρ : ℝ → ℝ) (c : ℝ) : Prop :=
  (∀ r : ℕ, StrictRung slope r → 1 ≤ sourceCount r (c * phaseZeroReference slope r)) ∧
  HasRungLimit (sourceLogCount c) (ρ c)

def NearOneRungEntropyLaw (ρ : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 2 * Real.log 2 / 10000 → RungEntropyLaw ρ (1 - ε)

def nearOneResidual (ρ : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (2 * Real.log 2 * Real.log 10 / (3 * ε)) * ρ (1 - ε) -
    (Real.log (1 / ε) - Real.log (Real.log (1 / ε)) + 1 + Real.log ((2 : ℝ) / 3))

end
end ExternalBridgePressureDraft
