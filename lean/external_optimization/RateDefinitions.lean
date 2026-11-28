import GeneralDefinitions

/-! UNFROZEN rate specification draft. Definitions only; no headline proofs.
The only imported project module is the canonical literal general model.
-/
namespace ExternalO3RateDraft
open Filter
open scoped Topology BigOperators
open ExternalO3GeneralDraft

noncomputable def achievedDensities (h : Depth) : Set ℝ :=
  {d | ∃ φ : Correction h, HasFailureDensity h φ d}

noncomputable def failureInfimum (h : Depth) : ℝ := sInf (achievedDensities h)

def succDepth (n : ℕ) : Depth := ⟨n + 1, Nat.zero_lt_succ n⟩

/-- Replace the candidate only on a STRICT improvement: ties retain the FIRST.
The depth-one fallback is totalization, not a future marker. -/
def firstFutureMax (h : Depth) (w : Window h) : Fin h.val :=
  ((List.finRange h.val).filter (fun i => 0 < i.val)).foldl
    (fun best i => match best with
      | none => some i
      | some j => if w j < w i then some i else some j)
    none |>.getD (zeroIndex h)

def markerDistance (h : Depth) (w : Window h) : ℕ :=
  ∑ i : Fin h.val, if i.val < (firstFutureMax h w).val then w i else 0

noncomputable def markerCorrection (h : Depth) : Correction h :=
  fun w => (markerDistance h w : ℝ) * Real.log 2

noncomputable def ascendingMass (h : Depth) (φ : Correction h) : ℝ :=
  ∑' a : AscendingIndex h, selectedWeight h φ (.inl a)

/-- k is an OFFSET: k=0 is terminating valuation K=2. -/
noncomputable def exitMass (h : Depth) (φ : Correction h) (k : ℕ) : ℝ :=
  ∑' b : Fin h.val → ℕ, selectedWeight h φ (.inr (k, b))

/-- Histories are finite offset vectors, decoded as strictly positive lengths.
There are h+1 independent slots. Repeating them cyclically does NOT assert
periodicity of any integer orbit. -/
abbrev History (h : Depth) := Fin (h.val + 1) → ℕ

def cyclicLength (h : Depth) (r : History h) (t : ℕ) : ℕ :=
  r (Fin.ofNat (h.val + 1) t) + 1

def cyclicWindow (h : Depth) (r : History h) (i s : ℕ) : Window h :=
  fun j => if j.val = 0 then s else cyclicLength h r (i + j.val)

noncomputable def historyWeight (h : Depth) (r : History h) : ℝ :=
  ∏ i : Fin (h.val + 1), (2 : ℝ) ^ (-((r i + 1 : ℕ) : ℤ))

noncomputable def ascentGain (h : Depth) (φ : Correction h)
    (r : History h) (i s : ℕ) : ℝ :=
  Real.log ((3 : ℝ) / 2) + φ (cyclicWindow h r i (s - 1)) -
    φ (cyclicWindow h r i s)

noncomputable def exitGain (h : Depth) (φ : Correction h)
    (r : History h) (i k : ℕ) : ℝ :=
  Real.log 3 - (k : ℝ) * Real.log 2 +
    φ (cyclicWindow h r (i + 1) (cyclicLength h r (i + 1))) -
    φ (cyclicWindow h r i 1)

noncomputable def failed (g : ℝ) : ℕ :=
  @ite ℕ (0 ≤ g) (Classical.propDecidable _) 1 0

noncomputable def blockFailures (h : Depth) (φ : Correction h)
    (r : History h) (i k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (cyclicLength h r i - 1),
    failed (ascentGain h φ r i (j + 2))) + failed (exitGain h φ r i k)

noncomputable def blockGain (h : Depth) (φ : Correction h)
    (r : History h) (i k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (cyclicLength h r i - 1),
    ascentGain h φ r i (j + 2)) + exitGain h φ r i k

noncomputable def cycleFailures (h : Depth) (φ : Correction h)
    (r : History h) : ℕ :=
  ∑ i : Fin (h.val + 1), blockFailures h φ r i.val 2

noncomputable def cycleGain (h : Depth) (r : History h) : ℝ :=
  ∑ i : Fin (h.val + 1),
    ((cyclicLength h r i.val : ℝ) * Real.log ((3 : ℝ) / 2) - Real.log 2)

noncomputable def positiveCycleMass (h : Depth) : ℝ :=
  ∑' r : History h, @ite ℝ (0 < cycleGain h r)
    (Classical.propDecidable _) (historyWeight h r) 0

/-- Optional stronger asymptotic constant, NOT needed by the rational rate. -/
noncomputable def strongLowerConstant : ℝ :=
  1 / (8 * (Real.log ((4 : ℝ) / 3) / Real.log 2))

end ExternalO3RateDraft
