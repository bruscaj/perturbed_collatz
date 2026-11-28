import PrefixDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Fintype.Card

/-! UNFROZEN finite source bridge specification. No implementation imported.
Words, prefixes and depths have finite domains; irrelevant infinite tails are
never counted. This module specifies no pressure, entropy or asymptotic limit. -/
namespace ExternalFiniteBridgeDraft
open scoped BigOperators

abbrev Word (r : ℕ) := Fin r → ℕ
abbrev Prefix (r : ℕ) := Fin (r + 1) → ℤ
abbrev Depth (r : ℕ) := Fin (r + 1) → ℤ

def PositiveWord (r : ℕ) (w : Word r) : Prop := ∀ i, 1 ≤ w i

def wordPrefix (r : ℕ) (w : Word r) : Prefix r := fun t =>
  ∑ i : Fin r, if i.val < t.val then (w i : ℤ) else 0

def PositivePrefix (r : ℕ) (K : Prefix r) : Prop :=
  K 0 = 0 ∧ ∀ i : Fin r, K i.castSucc + 1 ≤ K i.succ

def prefixLetters (r : ℕ) (K : Prefix r) : Word r :=
  fun i => (K i.succ - K i.castSucc).toNat

/-- Canonical zero extension only for comparison with the prior abstract model. -/
def extendPrefix (r : ℕ) (K : Prefix r) : ExternalPrefixSpec.Profile :=
  fun t => if ht : t ≤ r then K ⟨t, by omega⟩ else 0

noncomputable def slope : ℝ := Real.log 3 / Real.log 2
noncomputable def defect (θ : ℝ) (r : ℕ) : ℝ :=
  (Int.ceil ((r : ℝ) * θ) : ℝ) - (r : ℝ) * θ
noncomputable def floorAt (θ : ℝ) (t : ℕ) : ℤ := Int.floor ((t : ℝ) * θ)
noncomputable def floorPrefix (θ : ℝ) (r : ℕ) : Prefix r := fun t => floorAt θ t.val
noncomputable def literalCap (θ : ℝ) (r t : ℕ) : ℤ :=
  Int.floor ((t : ℝ) * θ + defect θ r)

def NonIntegralAt (θ : ℝ) (r : ℕ) : Prop :=
  ¬ ∃ z : ℤ, (r : ℝ) * θ = (z : ℝ)

def StrictRung (θ : ℝ) (r : ℕ) : Prop :=
  0 < r ∧ ∀ t : ℕ, 0 < t → t < r → defect θ r < defect θ t

/-- Source caps include redundant t=0 but exclude the closing endpoint. -/
def SourceWord (θ : ℝ) (r : ℕ) (w : Word r) : Prop :=
  0 < r ∧ PositiveWord r w ∧
  wordPrefix r w (Fin.last r) = Int.ceil ((r : ℝ) * θ) ∧
  ∀ t : Fin r, wordPrefix r w t.castSucc ≤ literalCap θ r t.val

def FloorWord (θ : ℝ) (r : ℕ) (w : Word r) : Prop :=
  0 < r ∧ PositiveWord r w ∧
  wordPrefix r w (Fin.last r) = floorAt θ r ∧
  ∀ t : Fin (r + 1), wordPrefix r w t ≤ floorAt θ t.val

/-- Natural subtraction is total; positivity after lowering is a theorem target. -/
def lowerLast (r : ℕ) (w : Word r) : Word r :=
  fun i => if i.val + 1 = r then w i - 1 else w i

def raiseLast (r : ℕ) (w : Word r) : Word r :=
  fun i => if i.val + 1 = r then w i + 1 else w i

noncomputable def wordDepth (θ : ℝ) (r : ℕ) (w : Word r) : Depth r :=
  fun t => floorAt θ t.val - wordPrefix r w t

noncomputable def sourceBridgeDepth (θ : ℝ) (r : ℕ) (w : Word r) : Depth r :=
  wordDepth θ r (lowerLast r w)

noncomputable def depthLetters (θ : ℝ) (r : ℕ) (J : Depth r) : Word r :=
  prefixLetters r (fun t => floorAt θ t.val - J t)

/-- Zero-endpoint floor bridge, obtained from source words only after lowering. -/
def DepthBridge (θ : ℝ) (r : ℕ) (J : Depth r) : Prop :=
  J 0 = 0 ∧ J (Fin.last r) = 0 ∧ (∀ t, 0 ≤ J t) ∧
  ∀ i : Fin r,
    J i.succ ≤ J i.castSucc + floorAt θ (i.val + 1) - floorAt θ i.val - 1

/-- The literal source reward, with no phase or closing-defect rescaling. -/
noncomputable def reward (r : ℕ) (w : Word r) : ℝ :=
  ∑ t : Fin r, (2 : ℝ) ^ wordPrefix r w t.castSucc / (3 : ℝ) ^ t.val

noncomputable def powerReward (θ : ℝ) (r : ℕ) (w : Word r) : ℝ :=
  ∑ t : Fin r, Real.rpow 2 ((wordPrefix r w t.castSucc : ℝ) - (t.val : ℝ) * θ)

noncomputable def phaseZeroReference (θ : ℝ) (r : ℕ) : ℝ :=
  ∑ t : Fin r, Real.rpow 2 ((floorAt θ t.val : ℝ) - (t.val : ℝ) * θ)

noncomputable def literalReference (θ : ℝ) (r : ℕ) : ℝ :=
  ∑ t : Fin r, Real.rpow 2 ((literalCap θ r t.val : ℝ) - (t.val : ℝ) * θ)

noncomputable def depthReward (θ : ℝ) (r : ℕ) (J : Depth r) : ℝ :=
  ∑ t : Fin r, Real.rpow 2 ((floorAt θ t.val : ℝ) - (t.val : ℝ) * θ) *
    (2 : ℝ) ^ (-J t.castSucc)

noncomputable def mechanicalWord (θ : ℝ) (r : ℕ) : Word r :=
  raiseLast r (prefixLetters r (floorPrefix θ r))

noncomputable def sourceCount (r : ℕ) (q : ℝ) : ℕ :=
  Nat.card {w : Word r // SourceWord slope r w ∧ q ≤ reward r w}
noncomputable def floorCount (r : ℕ) (q : ℝ) : ℕ :=
  Nat.card {w : Word r // FloorWord slope r w ∧ q ≤ reward r w}
noncomputable def depthCount (r : ℕ) (q : ℝ) : ℕ :=
  Nat.card {J : Depth r // DepthBridge slope r J ∧ q ≤ depthReward slope r J}

end ExternalFiniteBridgeDraft
