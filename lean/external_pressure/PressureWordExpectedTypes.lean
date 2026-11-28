import PressureWordDefinitions

/-! UNFROZEN finite helper propositions only: no theorem bodies, Challenge holes,
limit, discrepancy-convergence, entropy or differentiability premise. -/
namespace ExternalBridgePressureWordDraft
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def ZeroVolumeConvention : Prop := ∀ x lam,
  (∀ w : Word 0, ¬ AuxWord x 0 w ∧ auxReward x 0 w = 0) ∧
  auxPartition x 0 lam = 1 ∧ auxFinitePartition x 0 lam = 1 ∧
  auxLogPartition x 0 lam = 0 ∧ auxLogPressure x 0 lam = 0

def AuxiliaryEndpointWitness : Prop :=
  (∀ w : Word 1, (AuxWord 0 1 w ↔ w 0 = 1) ∧ (AuxWord 1 1 w ↔ w 0 = 2)) ∧
  ∀ lam : ℝ, auxPartition 0 1 lam = Real.exp lam ∧
    auxPartition 1 1 lam = Real.exp (lam / 2) ∧
    auxLogPartition 0 1 lam = lam ∧ auxLogPartition 1 1 lam = lam / 2 ∧
    rewardPartition 1 1 lam = Real.exp lam

def CapIncrementBounds : Prop := ∀ x : ℝ, ClosedPhase x →
  (∀ t : ℕ, auxCap x (t + 1) - auxCap x t = 1 ∨
    auxCap x (t + 1) - auxCap x t = 2) ∧
  ∀ n : ℕ, 1 ≤ n → auxCap x n ≤ (2 * n : ℕ)

def CanonicalWordLaw : Prop := ∀ x n, ClosedPhase x →
  PositivePrefix n (canonicalProfile x n) ∧
  wordPrefix n (canonicalWord x n) = canonicalProfile x n ∧
  (0 < n → AuxWord x n (canonicalWord x n))

def FiniteWordPopulation : Prop := ∀ x n, ClosedPhase x →
  Finite (AuxWords x n) ∧ Nat.card (AuxWords x n) ≤ 4 ^ n ∧
  (0 < n → Nonempty (AuxWords x n)) ∧
  ∀ w : Word n, AuxWord x n w → ∀ i : Fin n, 1 ≤ w i ∧ w i ≤ 2 * n

def BoundedWordEnumeration : Prop :=
  (∀ n, Function.Injective (decodeBoundedWord n)) ∧
  ∀ x n, ClosedPhase x → ∀ w : Word n, AuxWord x n w →
    ∃ a : BoundedWord n, decodeBoundedWord n a = w

def NormalizedRewardLaw : Prop := ∀ x n (w : Word n), ClosedPhase x → AuxWord x n w →
  auxReward x n w = Real.rpow 2 (-x) * reward n w ∧
  (∀ t : Fin n, auxTerm x n w t =
    Real.rpow 2 ((wordPrefix n w t.castSucc : ℝ) - x - (t.val : ℝ) * slope) ∧
    0 < auxTerm x n w t ∧ auxTerm x n w t ≤ 1) ∧
  0 ≤ auxReward x n w ∧ auxReward x n w ≤ (n : ℝ)

def AuxPartitionFiniteSum : Prop := ∀ x n lam, ClosedPhase x →
  Summable (fun w : AuxWords x n => Real.exp (lam * auxReward x n w.val)) ∧
  auxPartition x n lam = auxFinitePartition x n lam ∧
  (0 < n → auxPartition x n lam = ∑' w : AuxWords x n, Real.exp (lam * auxReward x n w.val))

def FinitePartitionBounds : Prop := ∀ x n lam, ClosedPhase x →
  0 < auxPartition x n lam ∧
  (0 ≤ lam → 0 ≤ auxLogPartition x n lam ∧
    auxLogPartition x n lam ≤ (n : ℝ) * (Real.log 4 + lam))

def CapDifferenceGeometry : Prop := ∀ x y n, OrderedPhases x y →
  (∀ t : ℕ, auxCap y t - auxCap x t = 0 ∨ auxCap y t - auxCap x t = 1) ∧
  Dcount x y n ≤ n ∧
  (∀ t : ℕ, (auxCap x t < auxCap y t ↔
    1 - y ≤ Int.fract ((t : ℝ) * slope) ∧ Int.fract ((t : ℝ) * slope) < 1 - x))

def PhaseUpTransport : Prop := ∀ x y n, OrderedPhases x y → 1 ≤ n →
  ((auxCap y n - auxCap x n).toNat : ℤ) = auxCap y n - auxCap x n ∧
  ∀ w : Word n, AuxWord x n w → AuxWord y n (phaseUp x y n w) ∧
    ∀ t : Fin n, wordPrefix n (phaseUp x y n w) t.castSucc = wordPrefix n w t.castSucc

def PhaseUpInjectionReward : Prop := ∀ x y n, OrderedPhases x y → 1 ≤ n →
  Function.Injective (phaseUp x y n) ∧
  ∀ w : Word n, AuxWord x n w → reward n (phaseUp x y n w) = reward n w ∧
    auxReward y n (phaseUp x y n w) = Real.rpow 2 (-(y - x)) * auxReward x n w

def ClampWordTransport : Prop := ∀ x y n, OrderedPhases x y → 1 ≤ n →
  ∀ w : Word n, AuxWord y n w →
    PositivePrefix n (clampProfile x n w) ∧
    wordPrefix n (clampWord x n w) = clampProfile x n w ∧ AuxWord x n (clampWord x n w)

def ClampFiberEncoding : Prop := ∀ x y n, OrderedPhases x y → 1 ≤ n →
  Function.Injective (fun w : AuxWords y n => clampCode x y n w.val) ∧
  ∀ w : Word n, AuxWord y n w →
    recoverClampProfile x y n (clampWord x n w) (clampBits x y n w) = wordPrefix n w ∧
    recoverClampWord x y n (clampWord x n w) (clampBits x y n w) = w ∧
    (∀ t : CapDifference x y n, t.val.val = 0 → clampBits x y n w t = false)

def ClampFiberCount : Prop := ∀ x y n, OrderedPhases x y → 1 ≤ n →
  Nat.card (CapDifference x y n → Bool) = 2 ^ Dcount x y n ∧
  ∀ v : Word n, Finite {w : AuxWords y n // clampWord x n w.val = v} ∧
    Nat.card {w : AuxWords y n // clampWord x n w.val = v} ≤ 2 ^ Dcount x y n

def ClampRewardBound : Prop := ∀ x y n, OrderedPhases x y → 1 ≤ n →
  ∀ w : Word n, AuxWord y n w →
    auxReward y n w ≤ auxReward x n (clampWord x n w) + (Dcount x y n : ℝ)

def PhaseLogComparison : Prop := ∀ (x y : ℝ) (n : ℕ) (lam : ℝ), OrderedPhases x y → 1 ≤ n → 0 ≤ lam →
  Real.exp (-lam * Real.log 2 * (y - x) * (n : ℝ)) * auxPartition x n lam ≤ auxPartition y n lam ∧
  auxPartition y n lam ≤ (2 : ℝ) ^ Dcount x y n * Real.exp (lam * (Dcount x y n : ℝ)) * auxPartition x n lam ∧
  auxLogPartition x n lam - lam * Real.log 2 * (y - x) * (n : ℝ) ≤ auxLogPartition y n lam ∧
  auxLogPartition y n lam ≤ auxLogPartition x n lam + (Real.log 2 + lam) * (Dcount x y n : ℝ)

def CompletionTransport : Prop := ∀ x n m, ClosedPhase x → 1 ≤ n →
  Function.Injective (fun w : AuxWords x n => completeWord x n m w.val) ∧
  ∀ w : Word n, AuxWord x n w → PositivePrefix (n + m) (completeProfile x n m w) ∧
    wordPrefix (n + m) (completeWord x n m w) = completeProfile x n m w ∧
    AuxWord x (n + m) (completeWord x n m w) ∧
    (∀ t : Fin n, auxTerm x (n + m) (completeWord x n m w) (firstIndex n m t) = auxTerm x n w t) ∧
    auxReward x n w ≤ auxReward x (n + m) (completeWord x n m w)

def TruncationTransport : Prop := ∀ x n m, ClosedPhase x → 1 ≤ n →
  ∀ w : Word (n + m), AuxWord x (n + m) w → PositivePrefix n (truncateProfile x n m w) ∧
    wordPrefix n (truncateWord x n m w) = truncateProfile x n m w ∧ AuxWord x n (truncateWord x n m w) ∧
    (∀ t : Fin n, auxTerm x n (truncateWord x n m w) t = auxTerm x (n + m) w (firstIndex n m t)) ∧
    auxReward x n (truncateWord x n m w) ≤ auxReward x (n + m) w ∧
    auxReward x (n + m) w ≤ auxReward x n (truncateWord x n m w) + (m : ℝ)

def TruncationFiberEncoding : Prop := ∀ x n m, ClosedPhase x → 1 ≤ n →
  Function.Injective (fun w : AuxWords x (n + m) => truncationCode x n m w.val) ∧
  ∀ w : Word (n + m), AuxWord x (n + m) w →
    recoverLongWord n m (truncateWord x n m w) (tailRecord n m w) = w ∧
    ∀ i : Fin (m + 1), n - 1 + i.val < n + m ∧
      1 ≤ tailRecord n m w i ∧ tailRecord n m w i ≤ 2 * (n + m) ∧
      (boundedTailRecord n m w i).val = tailRecord n m w i

def TruncationFiberCount : Prop := ∀ x n m, ClosedPhase x → 1 ≤ n →
  Nat.card (Fin (m + 1) → Fin (2 * (n + m) + 1)) = (2 * (n + m) + 1) ^ (m + 1) ∧
  ∀ v : Word n, Finite {w : AuxWords x (n + m) // truncateWord x n m w.val = v} ∧
    Nat.card {w : AuxWords x (n + m) // truncateWord x n m w.val = v} ≤ (2 * (n + m) + 1) ^ (m + 1)

def FixedShiftComparison : Prop := ∀ x n m lam, ClosedPhase x → 1 ≤ n → 0 ≤ lam →
  auxPartition x n lam ≤ auxPartition x (n + m) lam ∧
  auxPartition x (n + m) lam ≤ ((2 * (n + m) + 1 : ℕ) : ℝ) ^ (m + 1) *
    Real.exp (lam * (m : ℝ)) * auxPartition x n lam ∧
  0 ≤ auxLogPartition x (n + m) lam - auxLogPartition x n lam ∧
  auxLogPartition x (n + m) lam - auxLogPartition x n lam ≤
    lam * (m : ℝ) + ((m + 1 : ℕ) : ℝ) * Real.log ((2 * (n + m) + 1 : ℕ) : ℝ)

def NaturalDepthCompleteness : Prop := ∀ x n, ActualPhase x →
  ∀ j : Fin (n + 1) → ℕ, NaturalPathLegal x n j → ∀ t, j t ≤ n

def WordDepthDictionary : Prop := ∀ x n, ActualPhase x → 1 ≤ n →
  (∀ w : Word n, AuxWord x n w →
    (∀ t : Fin (n + 1), 0 ≤ auxDepth x n w t ∧ auxDepth x n w t ≤ (n : ℤ) ∧
      ((wordToPath x n w t).val : ℤ) = auxDepth x n w t) ∧
    PathLegal x n (wordToPath x n w) ∧ pathToWord x n (wordToPath x n w) = w ∧
    auxReward x n w = pathReward x n (wordToPath x n w)) ∧
  (∀ j : Path n, PathLegal x n j → AuxWord x n (pathToWord x n j) ∧ wordToPath x n (pathToWord x n j) = j) ∧
  ∃ e : AuxWords x n ≃ {j : Path n // PathLegal x n j},
    (∀ w, (e w).val = wordToPath x n w.val) ∧ (∀ j, (e.symm j).val = pathToWord x n j.val)

def WordPathPartitionEquality : Prop := ∀ x n lam, ActualPhase x →
  auxPartition x n lam = rewardPartition x n lam

def ConcatenationTransport : Prop := ∀ x m n, ActualPhase x → 1 ≤ m → 1 ≤ n →
  Function.Injective (fun p : AuxWords x m × AuxWords (phaseShift x m) n => concatenate m n p.1.val p.2.val) ∧
  ∀ u : Word m, AuxWord x m u → ∀ v : Word n, AuxWord (phaseShift x m) n v →
    AuxWord x (m + n) (concatenate m n u v) ∧
    auxReward x (m + n) (concatenate m n u v) = auxReward x m u + auxReward (phaseShift x m) n v

def PartitionCocycle : Prop := ∀ x m n lam, ActualPhase x → 0 ≤ lam →
  auxLogPartition x m lam + auxLogPartition (phaseShift x m) n lam ≤ auxLogPartition x (m + n) lam

def FiniteTiltLipschitz : Prop := ∀ x n lam mu, ClosedPhase x → 0 ≤ lam → 0 ≤ mu →
  |auxLogPartition x n lam - auxLogPartition x n mu| ≤ (n : ℝ) * |lam - mu|

def ClosingPhaseTransport : Prop := ∀ r lam, 0 < r →
  sourcePartition r lam = auxPartition (defect slope r) r (lam * Real.rpow 2 (defect slope r))

def RungWordTransport : Prop := ∀ r lam, StrictRung slope r →
  sourcePartition r lam = auxPartition 0 r lam

end
end ExternalBridgePressureWordDraft
