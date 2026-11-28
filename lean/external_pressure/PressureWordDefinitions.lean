import PressureDefinitions
import BridgeDefinitions

/-! UNFROZEN auxiliary finite-word definitions only. No theorem implementation
or pressure/entropy/limit hypothesis. Aux phase1 is not periodic phase0. -/
namespace ExternalBridgePressureWordDraft
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def ClosedPhase (x : ℝ) : Prop := 0 ≤ x ∧ x ≤ 1
def ActualPhase (x : ℝ) : Prop := 0 ≤ x ∧ x < 1
def OrderedPhases (x y : ℝ) : Prop := ClosedPhase x ∧ ClosedPhase y ∧ x ≤ y

/-- Raw cap: no subtraction of floor x, including at auxiliary x=1. -/
def auxCap (x : ℝ) (t : ℕ) : ℤ := Int.floor (x + (t : ℝ) * slope)
def AuxWord (x : ℝ) (n : ℕ) (w : Word n) : Prop :=
  0 < n ∧ PositiveWord n w ∧ wordPrefix n w (Fin.last n) = auxCap x n ∧
  ∀ t : Fin n, wordPrefix n w t.castSucc ≤ auxCap x t.val
abbrev AuxWords (x : ℝ) (n : ℕ) := {w : Word n // AuxWord x n w}

/-- The initial zero overrides C_0(1)=1. -/
def canonicalProfile (x : ℝ) (n : ℕ) : Prefix n :=
  fun t => if t.val = 0 then 0 else auxCap x t.val
def canonicalWord (x : ℝ) (n : ℕ) : Word n := prefixLetters n (canonicalProfile x n)

def auxTerm (x : ℝ) (n : ℕ) (w : Word n) (t : Fin n) : ℝ :=
  Real.rpow 2 (-x) * ((2 : ℝ) ^ wordPrefix n w t.castSucc / (3 : ℝ) ^ t.val)
def auxReward (x : ℝ) (n : ℕ) (w : Word n) : ℝ := ∑ t : Fin n, auxTerm x n w t

/-- The n=0 partition is assigned1 separately; AuxWords x0 remains empty. -/
def auxPartition (x : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  if n = 0 then 1 else ∑' w : AuxWords x n, Real.exp (lam * auxReward x n w.val)
def auxLogPartition (x : ℝ) (n : ℕ) (lam : ℝ) : ℝ := Real.log (auxPartition x n lam)
def auxLogPressure (x : ℝ) (n : ℕ) (lam : ℝ) : ℝ := auxLogPartition x n lam / (n : ℝ)

/-- Independent literal finite enumeration; its 2n letter bound is a target. -/
abbrev BoundedWord (n : ℕ) := Fin n → Fin (2 * n + 1)
def decodeBoundedWord (n : ℕ) (w : BoundedWord n) : Word n := fun i => (w i).val
def auxFinitePartition (x : ℝ) (n : ℕ) (lam : ℝ) : ℝ :=
  if n = 0 then 1 else ∑ w : BoundedWord n,
    if AuxWord x n (decodeBoundedWord n w) then
      Real.exp (lam * auxReward x n (decodeBoundedWord n w)) else 0

/-- Only the last letter changes. Nonnegative-cap subtraction is unproved here. -/
def phaseUp (x y : ℝ) (n : ℕ) (w : Word n) : Word n :=
  fun i => if i.val + 1 = n then w i + (auxCap y n - auxCap x n).toNat else w i

abbrev CapDifference (x y : ℝ) (n : ℕ) :=
  {t : Fin n // auxCap x t.val < auxCap y t.val}
def Dcount (x y : ℝ) (n : ℕ) : ℕ := Nat.card (CapDifference x y n)
def clampProfile (x : ℝ) (n : ℕ) (w : Word n) : Prefix n :=
  fun t => min (wordPrefix n w t) (auxCap x t.val)
def clampWord (x : ℝ) (n : ℕ) (w : Word n) : Word n := prefixLetters n (clampProfile x n w)
def clampBits (x y : ℝ) (n : ℕ) (w : Word n) : CapDifference x y n → Bool :=
  fun t => decide (auxCap x t.val.val < wordPrefix n w t.val.castSucc)
def clampCode (x y : ℝ) (n : ℕ) (w : Word n) :=
  (clampWord x n w, clampBits x y n w)

/-- Bits only before n; closing prefix is the known old endpoint. -/
def recoverClampProfile (x y : ℝ) (n : ℕ) (v : Word n)
    (bits : CapDifference x y n → Bool) : Prefix n := fun t =>
  if ht : t.val < n then
    if hd : auxCap x t.val < auxCap y t.val then
      if bits ⟨⟨t.val, ht⟩, hd⟩ then auxCap x t.val + 1 else wordPrefix n v t
    else wordPrefix n v t
  else auxCap y n
def recoverClampWord (x y : ℝ) (n : ℕ) (v : Word n)
    (bits : CapDifference x y n → Bool) : Word n :=
  prefixLetters n (recoverClampProfile x y n v bits)

/-- Total finite data maps. Positivity and exact toNat recovery are targets. -/
def completeProfile (x : ℝ) (n m : ℕ) (w : Word n) : Prefix (n + m) := fun t =>
  if ht : t.val ≤ n then wordPrefix n w ⟨t.val, by omega⟩ else auxCap x t.val
def completeWord (x : ℝ) (n m : ℕ) (w : Word n) : Word (n + m) :=
  prefixLetters (n + m) (completeProfile x n m w)
def truncateProfile (x : ℝ) (n m : ℕ) (w : Word (n + m)) : Prefix n := fun t =>
  if t.val < n then wordPrefix (n + m) w ⟨t.val, by omega⟩ else auxCap x n
def truncateWord (x : ℝ) (n m : ℕ) (w : Word (n + m)) : Word n :=
  prefixLetters n (truncateProfile x n m w)
def letterAt (n : ℕ) (w : Word n) (i : ℕ) : ℕ := if hi : i < n then w ⟨i,hi⟩ else 0
/-- At n>=1 these are exactly the old letters n-1,...,n+m-1. -/
def tailRecord (n m : ℕ) (w : Word (n + m)) : Fin (m + 1) → ℕ :=
  fun i => letterAt (n + m) w (n - 1 + i.val)
def boundedTailRecord (n m : ℕ) (w : Word (n + m)) : Fin (m + 1) → Fin (2 * (n + m) + 1) :=
  fun i => ⟨tailRecord n m w i % (2 * (n + m) + 1), Nat.mod_lt _ (by omega)⟩
def truncationCode (x : ℝ) (n m : ℕ) (w : Word (n + m)) :=
  (truncateWord x n m w, boundedTailRecord n m w)
def recoverLongWord (n m : ℕ) (v : Word n) (a : Fin (m + 1) → ℕ) : Word (n + m) := fun i =>
  if hi : i.val + 1 < n then v ⟨i.val, by omega⟩
  else a ⟨i.val - (n - 1), by omega⟩

def auxDepth (x : ℝ) (n : ℕ) (w : Word n) : Depth n :=
  fun t => auxCap x t.val - wordPrefix n w t
/-- Modulo totalization is harmless only after the explicit depth-bound target. -/
def wordToPath (x : ℝ) (n : ℕ) (w : Word n) : Path n :=
  fun t => ⟨(auxDepth x n w t).toNat % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
def pathToWord (x : ℝ) (n : ℕ) (j : Path n) : Word n :=
  prefixLetters n (fun t => auxCap x t.val - ((j t).val : ℤ))

def firstIndex (n m : ℕ) (t : Fin n) : Fin (n + m) := ⟨t.val, by omega⟩

def concatenate (m n : ℕ) (u : Word m) (v : Word n) : Word (m + n) := fun i =>
  if hi : i.val < m then u ⟨i.val,hi⟩ else v ⟨i.val-m,by omega⟩

end
end ExternalBridgePressureWordDraft
