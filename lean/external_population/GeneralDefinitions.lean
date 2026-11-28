import Definitions

/-!
UNFROZEN arbitrary-finite-depth specification draft. No headline proof here.
The imported Definitions module is the unchanged canonical literal Syracuse map
from the frozen h=1 specification. Only its arithmetic model is reused.
-/
namespace ExternalO3GeneralDraft

open Filter
open scoped Topology BigOperators

/-- The source information depth is a positive integer h, fixed before the limit. -/
abbrev Depth := {h : ℕ // 0 < h}

abbrev Window (h : Depth) := Fin h.val → ℕ
abbrev Correction (h : Depth) := Window h → ℝ

def ValidWindow (h : Depth) (w : Window h) : Prop := ∀ i, 0 < w i

def zeroIndex (h : Depth) : Fin h.val := ⟨0, h.property⟩

def futureBlockSeed (x i : ℕ) : ℕ := (Nat.iterate ExternalO3Spec.nextBlock i) x

/-- Current remaining block, followed by h-1 actual complete future blocks. -/
def window (h : Depth) (x : ℕ) : Window h :=
  fun i => ExternalO3Spec.blockLength (futureBlockSeed x i.val)

def decrementHead (h : Depth) (w : Window h) : Window h :=
  fun i => if i.val = 0 then w i - 1 else w i

/-- Prefix a remaining block of length one and discard the last entry. -/
def prependOne (h : Depth) (w : Window h) : Window h :=
  fun i => if hi : i.val = 0 then 1 else
    w ⟨i.val - 1, by have ht := i.isLt; omega⟩

noncomputable def rawPotential (h : Depth) (φ : Correction h) (x : ℕ) : ℝ :=
  Real.log (x : ℝ) + φ (window h x)

noncomputable def potential (h : Depth) (φ : Correction h) (x : ExternalO3Spec.OddSeed) : ℝ :=
  rawPotential h φ x.val

/-- Equality is failure; zero and all other non-source inputs are excluded. -/
def FailsAt (h : Depth) (φ : Correction h) (x : ℕ) : Prop :=
  ExternalO3Spec.IsOddSeed x ∧
    rawPotential h φ (ExternalO3Spec.stride x) ≥ rawPotential h φ x

noncomputable def populationFrequency (P : ℕ → Prop) (N : ℕ) : ℝ := by
  classical
  exact (((Finset.range N).filter P).card : ℝ) / (N : ℝ)

noncomputable def failureCount (h : Depth) (φ : Correction h) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun n => FailsAt h φ (2 * n + 1))).card

noncomputable def failureFrequency (h : Depth) (φ : Correction h) (N : ℕ) : ℝ :=
  (failureCount h φ N : ℝ) / (N : ℝ)

def HasFailureDensity (h : Depth) (φ : Correction h) (d : ℝ) : Prop :=
  Tendsto (failureFrequency h φ) atTop (nhds d)

noncomputable def sourceFrequency (h : Depth) (φ : Correction h) (X : ℕ) : ℝ := by
  classical
  exact (((Finset.range (X + 1)).filter (fun x => FailsAt h φ x)).card : ℝ) /
    (((Finset.range (X + 1)).filter ExternalO3Spec.IsOddSeed).card : ℝ)

abbrev AscendingIndex (h : Depth) := Fin h.val → ℕ
abbrev ExitIndex (h : Depth) := ℕ × (Fin h.val → ℕ)
abbrev Edge (h : Depth) := Sum (AscendingIndex h) (ExitIndex h)

/-- Head offset starts at two; each subsequent complete-block offset starts at one. -/
def ascendingWindow (h : Depth) (a : AscendingIndex h) : Window h :=
  fun i => if i.val = 0 then a i + 2 else a i + 1

def positiveWindow (h : Depth) (b : Fin h.val → ℕ) : Window h := fun i => b i + 1

def ascendingOffsets (h : Depth) (w : Window h) : AscendingIndex h :=
  fun i => if i.val = 0 then w i - 2 else w i - 1

def positiveOffsets (h : Depth) (w : Window h) : Fin h.val → ℕ := fun i => w i - 1

def windowSum (h : Depth) (w : Window h) : ℕ := ∑ i : Fin h.val, w i

/-- The exit index includes the newly revealed h+1st block; the correction at
its old input still reads only the first h blocks. -/
def label (h : Depth) (n : ℕ) : Edge h :=
  if 2 ≤ ExternalO3Spec.blockLength (2 * n + 1) then
    .inl (ascendingOffsets h (window h (2 * n + 1)))
  else
    .inr (ExternalO3Spec.strideValuation (2 * n + 1) - 2,
      positiveOffsets h (window h (ExternalO3Spec.stride (2 * n + 1))))

noncomputable def gain (h : Depth) (φ : Correction h) : Edge h → ℝ
  | .inl a => Real.log ((3 : ℝ) / 2) +
      φ (decrementHead h (ascendingWindow h a)) - φ (ascendingWindow h a)
  | .inr (k, b) => Real.log 3 - ((k + 2 : ℕ) : ℝ) * Real.log 2 +
      φ (positiveWindow h b) - φ (prependOne h (positiveWindow h b))

noncomputable def weight (h : Depth) : Edge h → ℝ
  | .inl a => (2 : ℝ) ^ (-((windowSum h (ascendingWindow h a) : ℕ) : ℤ))
  | .inr (k, b) =>
      (2 : ℝ) ^ (-((k + 2 + windowSum h (positiveWindow h b) : ℕ) : ℤ))

def Bad (h : Depth) (φ : Correction h) (e : Edge h) : Prop := 0 ≤ gain h φ e

noncomputable def selectedWeight (h : Depth) (φ : Correction h) (e : Edge h) : ℝ := by
  classical
  exact if Bad h φ e then weight h e else 0

/-- A candidate symbolic series, not a density theorem or an assumed limit. -/
noncomputable def symbolicFailureDensity (h : Depth) (φ : Correction h) : ℝ :=
  ∑' e : Edge h, selectedWeight h φ e

/-- m completed blocks, with their exact exit valuations, plus one terminal
remaining block. No infinite-path probability measure is used. -/
def RefinedCell (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ) (x : ℕ) : Prop :=
  ExternalO3Spec.IsOddSeed x ∧
    (∀ i, ExternalO3Spec.blockLength (futureBlockSeed x i.val) = lengths i) ∧
    (∀ i, ExternalO3Spec.strideValuation
      ((Nat.iterate ExternalO3Spec.stride (lengths i.castSucc - 1))
        (futureBlockSeed x i.val)) = exits i)

def ValidBlockData (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ) : Prop :=
  (∀ i, 0 < lengths i) ∧ (∀ i, 2 ≤ exits i)

def refinedExponent (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ) : ℕ :=
  (∑ i : Fin m, (lengths i.castSucc - 1 + exits i)) + lengths (Fin.last m)

abbrev RefinedIndex (m : ℕ) := (Fin (m + 1) → ℕ) × (Fin m → ℕ)

def decodedLengths (m : ℕ) (data : RefinedIndex m) : Fin (m + 1) → ℕ :=
  fun i => data.1 i + 1

def decodedExits (m : ℕ) (data : RefinedIndex m) : Fin m → ℕ :=
  fun i => data.2 i + 2

/-- Actual finite block data of each starting seed, not independently sampled symbols. -/
def refinedLabel (m n : ℕ) : RefinedIndex m :=
  (fun i => ExternalO3Spec.blockLength (futureBlockSeed (2 * n + 1) i.val) - 1,
   fun i =>
     let y := futureBlockSeed (2 * n + 1) i.val
     ExternalO3Spec.strideValuation
       ((Nat.iterate ExternalO3Spec.stride (ExternalO3Spec.blockLength y - 1)) y) - 2)

noncomputable def refinedWeight (m : ℕ) (data : RefinedIndex m) : ℝ :=
  (2 : ℝ) ^ (-((refinedExponent m (decodedLengths m data) (decodedExits m data) : ℕ) : ℤ))

/-- h completed blocks plus one terminal length suffice for both failure branches. -/
def refinementProjection (h : Depth) (data : RefinedIndex h.val) : Edge h :=
  let lengths := decodedLengths h.val data
  if 2 ≤ lengths ⟨0, by have hp := h.property; omega⟩ then
    .inl (ascendingOffsets h (fun i => lengths i.castSucc))
  else
    .inr (data.2 (zeroIndex h), positiveOffsets h (fun i => lengths i.succ))

noncomputable def refinedFiberWeight (h : Depth) (e : Edge h)
    (data : RefinedIndex h.val) : ℝ := by
  classical
  exact if refinementProjection h data = e then refinedWeight h.val data else 0

def depthOne : Depth := ⟨1, by decide⟩

noncomputable def liftOne (φ : ExternalO3Spec.Correction) : Correction depthOne :=
  fun w => φ (w (zeroIndex depthOne))

noncomputable def scalarizeOne (φ : Correction depthOne) : ExternalO3Spec.Correction :=
  fun r => φ (fun _ => r)

end ExternalO3GeneralDraft
