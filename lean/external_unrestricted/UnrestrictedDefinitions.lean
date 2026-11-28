import BridgeExpectedTypes
import Mathlib.Topology.Order.LiminfLimsup

/-! UNFROZEN statement/model draft, prepared after an exploratory written argument.
No Challenge, implementation, desired injection, pressure, or limit is imported.
The count is the original ordered source-word count at the fixed B_r. -/
namespace ExternalM4UnrestrictedDraft
open ExternalFiniteBridgeDraft
open scoped BigOperators

noncomputable def beta : ℝ := slope - 1
noncomputable def canonicalPrefix (r : ℕ) : Prefix r :=
  fun t => literalCap slope r t.val
noncomputable def canonicalWord (r : ℕ) : Word r :=
  prefixLetters r (canonicalPrefix r)

/-- Fixed phase-zero threshold at every length, without phase adaptation. -/
noncomputable def count (r : ℕ) : ℕ :=
  sourceCount r (phaseZeroReference slope r)
noncomputable def highPhaseCount (r : ℕ) : ℕ :=
  Nat.card {t : Fin r // (1 / 2 : ℝ) ≤ Int.fract ((t.val : ℝ) * slope)}

/-- A start index of an actual adjacent 21, necessarily before the last letter. -/
def TwentyOneSite (r : ℕ) (w : Word r) (i : Fin r) : Prop :=
  ∃ hi : i.val + 1 < r, w i = 2 ∧ w ⟨i.val + 1, hi⟩ = 1

def DisjointSites (r : ℕ) (S : Finset (Fin r)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → i.val + 1 < j.val ∨ j.val + 1 < i.val

def AdmissibleSites (r : ℕ) (w : Word r) (S : Finset (Fin r)) : Prop :=
  (∀ i ∈ S, TwentyOneSite r w i) ∧ DisjointSites r S

/-- Total data operation. Its source/prefix/reward properties are unproved targets.
At a selected start put 1; at its successor put 2; preserve all other letters. -/
noncomputable def applySwaps (r : ℕ) (w : Word r) (S : Finset (Fin r)) : Word r :=
  fun i => if i ∈ S then 1 else if ∃ j ∈ S, j.val + 1 = i.val then 2 else w i

abbrev SwapCube (r : ℕ) (S : Finset (Fin r)) :=
  {T : Finset (Fin r) // T ⊆ S}
noncomputable def swapFamily (r : ℕ) (w : Word r) (S : Finset (Fin r))
    (T : SwapCube r S) : Word r := applySwaps r w T.val

/-- i.succ is the intermediate prefix i+1; a valid site has i+1<r. -/
noncomputable def swapLoss (r : ℕ) (w : Word r) (S : Finset (Fin r)) : ℝ :=
  ∑ i ∈ S, (2 : ℝ) ^ wordPrefix r w i.succ / (3 : ℝ) ^ (i.val + 1) / 2

/-- Real.log 0=0 and division by zero is totalized; intended normalization is r>0. -/
noncomputable def normalizedLogCount (r : ℕ) : ℝ :=
  (Real.log (count r : ℝ) / Real.log 10) / (r : ℝ)

end ExternalM4UnrestrictedDraft
