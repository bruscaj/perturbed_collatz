import UnrestrictedDefinitions

/-! UNFROZEN unproved proposed targets. No theorem implementations or holes. -/
namespace ExternalM4UnrestrictedDraft
open ExternalFiniteBridgeDraft
open Filter
open scoped Topology BigOperators

def SlopeBounds : Prop := (3 / 2 : ℝ) < slope ∧ slope < (5 / 3 : ℝ)

def TripleRotationHighLow : Prop := ∀ β y : ℝ,
  1 / 2 < β → β < 2 / 3 → 0 ≤ y → y < 1 →
  (∃ j : Fin 3, 1 / 2 ≤ Int.fract (y + (j.val : ℝ) * β)) ∧
  (∃ j : Fin 3, Int.fract (y + (j.val : ℝ) * β) < 1 / 2)

def HighPhaseCountLower : Prop := ∀ r : ℕ, r / 3 ≤ highPhaseCount r

def LargeDefectsUnbounded : Prop := ∀ R : ℕ, ∃ r : ℕ,
  R < r ∧ (1 / 2 : ℝ) ≤ defect slope r

def CanonicalPrefixLaw : Prop := ∀ r : ℕ,
  wordPrefix r (canonicalWord r) = canonicalPrefix r ∧
  canonicalPrefix r 0 = 0 ∧
  canonicalPrefix r (Fin.last r) = Int.ceil ((r : ℝ) * slope)

def CanonicalAllLengthWord : Prop := ∀ r : ℕ, 0 < r →
  SourceWord slope r (canonicalWord r) ∧
  phaseZeroReference slope r ≤ reward r (canonicalWord r)

def CanonicalAlphabetAndSites : Prop := ∀ r : ℕ, 0 < r →
  (∀ i : Fin r, canonicalWord r i = 1 ∨ canonicalWord r i = 2) ∧
  (∀ i : Fin r, ∀ hi : i.val + 1 < r,
    ¬ (canonicalWord r i = 1 ∧ canonicalWord r ⟨i.val + 1, hi⟩ = 1)) ∧
  Nat.card {i : Fin r // canonicalWord r i = 1} =
    2 * r - (Int.ceil ((r : ℝ) * slope)).toNat ∧
  r / 3 - 1 ≤ Nat.card {i : Fin r // TwentyOneSite r (canonicalWord r) i}

def ManyDisjointCanonicalSites : Prop := ∀ r : ℕ, 8 ≤ r →
  ∃ S : Finset (Fin r), AdmissibleSites r (canonicalWord r) S ∧ S.card = r / 8

def SwapPrefixLaw : Prop := ∀ r (w : Word r) (S : Finset (Fin r)),
  AdmissibleSites r w S → ∀ t : Fin (r + 1),
    wordPrefix r (applySwaps r w S) t = wordPrefix r w t -
      (if ∃ i ∈ S, i.val + 1 = t.val then (1 : ℤ) else 0)

def SwapPreservesSource : Prop := ∀ r (w : Word r) (S : Finset (Fin r)),
  SourceWord slope r w → AdmissibleSites r w S →
    PositiveWord r (applySwaps r w S) ∧
    wordPrefix r (applySwaps r w S) (Fin.last r) = wordPrefix r w (Fin.last r) ∧
    (∀ t : Fin r, wordPrefix r (applySwaps r w S) t.castSucc ≤ literalCap slope r t.val) ∧
    SourceWord slope r (applySwaps r w S)

def SwapFamilyInjective : Prop := ∀ r (w : Word r) (S : Finset (Fin r)),
  AdmissibleSites r w S → Function.Injective (swapFamily r w S)

def SwapCubeCard : Prop := ∀ r (S : Finset (Fin r)),
  Nat.card (SwapCube r S) = 2 ^ S.card

def SwapRewardIdentity : Prop := ∀ r (w : Word r) (S : Finset (Fin r)),
  AdmissibleSites r w S →
  reward r w - reward r (applySwaps r w S) = swapLoss r w S

def CanonicalRewardBudget : Prop := ∀ r : ℕ, (1 / 2 : ℝ) ≤ defect slope r →
  ((r / 3 : ℕ) : ℝ) / 2 ≤ reward r (canonicalWord r) - phaseZeroReference slope r

def CanonicalSwapLossBound : Prop := ∀ r (S : Finset (Fin r)),
  AdmissibleSites r (canonicalWord r) S →
  0 ≤ swapLoss r (canonicalWord r) S ∧
  swapLoss r (canonicalWord r) S ≤ (S.card : ℝ) ∧
  (0 < S.card → swapLoss r (canonicalWord r) S < (S.card : ℝ))

def LargeDefectWitnessInjection : Prop := ∀ r : ℕ, 8 ≤ r →
  (1 / 2 : ℝ) ≤ defect slope r →
  ∃ S : Finset (Fin r), AdmissibleSites r (canonicalWord r) S ∧ S.card = r / 8 ∧
    Function.Injective (swapFamily r (canonicalWord r) S) ∧
    ∀ T : SwapCube r S,
      SourceWord slope r (swapFamily r (canonicalWord r) S T) ∧
      phaseZeroReference slope r ≤ reward r (swapFamily r (canonicalWord r) S T)

def ExponentialCountLower : Prop := ∀ r : ℕ, 8 ≤ r →
  (1 / 2 : ℝ) ≤ defect slope r → 2 ^ (r / 8) ≤ count r

def RungCountOne : Prop := ∀ r : ℕ, StrictRung slope r → count r = 1

def AllLengthCountBounds : Prop :=
  (∀ r, Finite {w : Word r // SourceWord slope r w ∧
    phaseZeroReference slope r ≤ reward r w}) ∧
  count 0 = 0 ∧ ∀ r : ℕ, 0 < r → 1 ≤ count r ∧ count r ≤ 2 ^ (2 * r)

def NormalizedLogBounds : Prop := normalizedLogCount 0 = 0 ∧
  ∀ r : ℕ, 0 ≤ normalizedLogCount r ∧
    normalizedLogCount r ≤ 2 * (Real.log 2 / Real.log 10)

def NormalizedLogLiminf : Prop :=
  Filter.liminf normalizedLogCount atTop = 0

def NormalizedLogLimsup : Prop :=
  (Real.log 2 / Real.log 10) / 8 ≤ Filter.limsup normalizedLogCount atTop

def NoAllLengthLimit : Prop :=
  ¬ ∃ L : ℝ, Tendsto normalizedLogCount atTop (nhds L)

end ExternalM4UnrestrictedDraft
