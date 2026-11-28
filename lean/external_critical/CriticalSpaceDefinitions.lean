import PressureDefinitions
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Topology.Metrizable.Basic

/-! UNFROZEN critical-law model primitives only. No critical law, derivative,
stationary Gibbs measure, compactness theorem or accepted proof is assumed.
The auxiliary closed interval in the clamping proof is NOT this circle. -/
namespace ExternalCriticalSpaceDraft
open ExternalBridgePressureDraft ExternalFiniteBridgeDraft MeasureTheory
open scoped BigOperators Topology
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Phase := AddCircle (1 : ℝ)
abbrev Height := OnePoint ℕ

instance heightMeasurableSpace : MeasurableSpace Height := borel Height
instance heightBorelSpace : BorelSpace Height := ⟨rfl⟩

abbrev Config := Phase × (ℤ → Height)

instance configMeasurableSpace : MeasurableSpace Config := borel Config
instance configBorelSpace : BorelSpace Config := ⟨rfl⟩

def phaseRepresentative (x : Phase) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

def phaseRotation (x : Phase) : Phase := x + (slope : Phase)

def timeShift (s : ℤ) (w : Config) : Config :=
  (w.1 + (((s : ℝ) * slope : ℝ) : Phase), fun t => w.2 (t + s))

def heightWeight (h : Height) : ℝ :=
  h.elim 0 (fun j => (2 : ℝ) ^ (-(j : ℤ)))

def localReward (w : Config) : ℝ :=
  Real.rpow 2 (-phaseRepresentative w.1) * heightWeight (w.2 0)

def uniformPhase : Measure Phase := volume

def IsStationary (mu : Measure Config) : Prop :=
  Measure.map (timeShift 1) mu = mu

def HasUniformPhase (mu : Measure Config) : Prop :=
  Measure.map Prod.fst mu = uniformPhase

def allFinite : Set Config := {w | ∀ t : ℤ, ∃ a : ℕ, w.2 t = OnePoint.some a}
def allInfinite : Set Config := {w | ∀ t : ℤ, w.2 t = OnePoint.infty}

def finiteHeightSet (H : ℕ) : Set Height := {h | ∃ a : ℕ, a ≤ H ∧ h = OnePoint.some a}
def lowEvent (H : ℕ) (t : ℤ) : Set Config := {w | w.2 t ∈ finiteHeightSet H}

def forbiddenUpwardCylinder (a : ℕ) : Set Config :=
  {w | w.2 0 = OnePoint.some a ∧ w.2 1 ∉ finiteHeightSet (a+1)}

/-- Positive gaps only. The half-open shifted copies contain time zero. -/
def successiveGap (H m : ℕ) : Set Config :=
  {w | 0 < m ∧ w ∈ lowEvent H 0 ∧ w ∈ lowEvent H (m : ℤ) ∧
    ∀ t : ℕ, 0 < t → t < m → w ∉ lowEvent H (t : ℤ)}

def shiftedGap (H m k : ℕ) : Set Config :=
  (timeShift (-(k : ℤ))) ⁻¹' successiveGap H m

def longExcursion (H L n : ℕ) : Set Config :=
  {w | w ∈ lowEvent H 0 ∧ w ∈ lowEvent H (n : ℤ) ∧
    ∀ t : ℕ, L ≤ t → t < n → w ∉ lowEvent H (t : ℤ)}

/-- Extend the finite zero-endpoint path by finite zeros outside [0,n].
The phase at root i is the physical circle phase advanced by i*theta. -/
def rootedConfig (n : ℕ) (x : Phase) (j : Path n) (i : Fin n) : Config :=
  (x + (((i.val : ℝ)*slope : ℝ) : Phase), fun t =>
    let s := t + (i.val : ℤ)
    if hs : 0 ≤ s ∧ s ≤ (n : ℤ) then
      OnePoint.some ((j ⟨s.toNat, by omega⟩).val)
    else OnePoint.some 0)

/-- Raw finite rooted measure. Normalization for n>0 is a theorem target.
At n=0 the root sum is empty; no probability-law fallback is inserted. -/
def rootedMeasure (n : ℕ) (lam : ℝ) : Measure Config :=
  uniformPhase.bind (fun x =>
    ∑ i : Fin n, ∑ j : Path n,
      if PathLegal (phaseRepresentative x) n j then
        ENNReal.ofReal (Real.exp (lam * pathReward (phaseRepresentative x) n j) /
          rewardPartition (phaseRepresentative x) n lam / (n : ℝ)) •
            Measure.dirac (rootedConfig n x j i)
      else 0)

end
end ExternalCriticalSpaceDraft
