import PressureExpectedTypes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Computability.Partrec

/-! UNFROZEN completion proposal. Data and predicates only, no theorem proofs.
The original twenty propositions remain in the imported partial draft. -/
namespace ExternalBridgePressureCompleteDraft
open ExternalBridgePressureDraft ExternalFiniteBridgeDraft Filter
open scoped BigOperators Topology
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Functions are data, not limits chosen by assuming their existence. -/
structure Model where
  P : ℝ → ℝ
  p : ℝ → ℝ
  rho : ℝ → ℝ
  criticalTilt : ℝ

def CorePressureLaw (M : Model) : Prop :=
  SourcePressureLaw M.P ∧ UniformRewardPressureLaw M.P ∧
  UniformCostPressureLaw M.p ∧ CompactTiltPressureLaw M.P ∧
  ∀ lam : ℝ, 0 ≤ lam → M.P lam = lam * meanReference + M.p lam

def AllThresholdEntropyLaw (M : Model) : Prop :=
  (∀ c : ℝ, 0 ≤ c → c ≤ 1 → RungEntropyLaw M.rho c) ∧
  M.rho 0 = baselineEntropy / Real.log 10 ∧ M.rho 1 = 0

def defectObjective (M : Model) (c lam : ℝ) : ℝ :=
  M.p lam + lam * (1 - c) * meanReference
def sourceObjective (M : Model) (c lam : ℝ) : ℝ :=
  M.P lam - lam * c * meanReference
def objectiveValues (M : Model) (c : ℝ) : Set ℝ :=
  {v | ∃ lam : ℝ, 0 ≤ lam ∧ v = defectObjective M c lam}
def sourceObjectiveValues (M : Model) (c : ℝ) : Set ℝ :=
  {v | ∃ lam : ℝ, 0 ≤ lam ∧ v = sourceObjective M c lam}

def LegendreLaw (M : Model) : Prop := ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
  (objectiveValues M c).Nonempty ∧ BddBelow (objectiveValues M c) ∧
  objectiveValues M c = sourceObjectiveValues M c ∧
  M.rho c = sInf (objectiveValues M c) / Real.log 10

def ConvexNonnegative (f : ℝ → ℝ) : Prop :=
  ∀ x y t : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ t → t ≤ 1 →
    f ((1-t)*x+t*y) ≤ (1-t)*f x+t*f y

def PressureBounds (M : Model) : Prop :=
  M.P 0 = baselineEntropy ∧ M.p 0 = baselineEntropy ∧
  (∀ lam : ℝ, 0 ≤ lam → 0 ≤ M.p lam ∧ M.p lam ≤ baselineEntropy) ∧
  ConvexNonnegative M.P ∧ ConvexNonnegative M.p ∧
  (∀ a b : ℝ, 0 ≤ a → a ≤ b → M.p b ≤ M.p a ∧ M.P a ≤ M.P b) ∧
  (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |M.p a-M.p b| ≤ |a-b| ∧ |M.P a-M.P b| ≤ |a-b|) ∧
  Tendsto M.p atTop (𝓝 0)

def C1Nonnegative (M : Model) : Prop :=
  ContDiffOn ℝ 1 M.P (Set.Ici 0) ∧
  HasDerivWithinAt M.P 0 (Set.Ici 0) 0 ∧
  ContinuousOn (fun lam => derivWithin M.P (Set.Ici 0) lam) (Set.Ici 0)

def LocalizedDerivativeLipschitz (M : Model) : Prop :=
  ∀ a b : ℝ, M.criticalTilt < a → a < b → ∃ L : ℝ, 0 ≤ L ∧
    ∀ x y : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b →
      |deriv M.P x-deriv M.P y| ≤ L*|x-y|

def LocalizedStrongConvexity (M : Model) : Prop :=
  ∀ a b : ℝ, M.criticalTilt < a → a < b → ∃ kappa : ℝ, 0 < kappa ∧
    ∀ x y t : ℝ, x ∈ Set.Icc a b → y ∈ Set.Icc a b → 0 ≤ t → t ≤ 1 →
      M.P ((1-t)*x+t*y) ≤ (1-t)*M.P x+t*M.P y-
        (kappa/2)*t*(1-t)*(x-y)^2

def StrongR8Law (M : Model) : Prop :=
  CriticalGeometry M.P M.criticalTilt ∧ C1Nonnegative M ∧
  HasDerivAt M.P 0 M.criticalTilt ∧
  LocalizedDerivativeLipschitz M ∧ LocalizedStrongConvexity M

/-- A common positive denominator: ((lower numerator, upper numerator), denominator-1)
is represented using the standard right-associated natural triple. -/
abbrev BracketCode := ℕ × ℕ × ℕ
def lowerQ (q : BracketCode) : ℚ := (q.1 : ℚ) / ((q.2.2 + 1 : ℕ) : ℚ)
def upperQ (q : BracketCode) : ℚ := (q.2.1 : ℚ) / ((q.2.2 + 1 : ℕ) : ℚ)
def Contains (q : BracketCode) (x : ℝ) : Prop := (lowerQ q : ℝ) ≤ x ∧ x ≤ (upperQ q : ℝ)
/-- Exact decidable rational width check; ordering precedes Nat subtraction. -/
def Narrow (bits : ℕ) (q : BracketCode) : Prop :=
  q.1 ≤ q.2.1 ∧ (q.2.1-q.1)*2^bits ≤ q.2.2+1
def Certified (x : ℝ) (bits : ℕ) (q : BracketCode) : Prop := Contains q x ∧ Narrow bits q
def rationalInput (a d : ℕ) : ℚ := (a : ℚ) / ((d+1 : ℕ) : ℚ)
def realInput (a d : ℕ) : ℝ := (rationalInput a d : ℝ)
def zeroBracket : BracketCode := (0,0,0)

def ComputablePressureBrackets (M : Model) : Prop :=
  ∃ A : (ℕ × ℕ × ℕ) → BracketCode × BracketCode, Computable A ∧
    ∀ a d bits : ℕ,
      Certified (M.P (realInput a d)) bits (A (a,d,bits)).1 ∧
      Certified (M.p (realInput a d)) bits (A (a,d,bits)).2

def ComputableEntropyBrackets (M : Model) : Prop :=
  ∃ A : (ℕ × ℕ × ℕ) → BracketCode, Computable A ∧
    (∀ a d bits : ℕ, a ≤ d+1 → Certified (M.rho (realInput a d)) bits (A (a,d,bits))) ∧
    (∀ d bits : ℕ, A (d+1,d,bits) = zeroBracket)

/-- Together with rational brackets, a total computable modulus gives a
standard fast-Cauchy representation on all of [0,1], without coding Real as Nat. -/
def ComputableEntropyModulus (M : Model) : Prop :=
  ∃ modulus : ℕ → ℕ, Computable modulus ∧
    ∀ bits : ℕ, ∀ c d : ℝ, c ∈ Set.Icc 0 1 → d ∈ Set.Icc 0 1 →
      |c-d| ≤ (2 : ℝ)^(-((modulus bits : ℕ) : ℤ)) →
        |M.rho c-M.rho d| ≤ (2 : ℝ)^(-(bits : ℤ))

/-- Fully specified finite open-survival kernel for the pressure upper route.
The cap a+n is a completeness target, not an arbitrary truncation assumption. -/
abbrev OpenPath (n a : ℕ) := Fin (n+1) → Fin (a+n+1)
def NaturalOpenLegal (x : ℝ) (n a : ℕ) (j : Fin (n+1) → ℕ) : Prop :=
  j 0 = a ∧ ∀ i : Fin n,
    (j i.succ : ℤ) ≤ (j i.castSucc : ℤ)+phaseIncrement x i.val-1
def OpenLegal (x : ℝ) (n a : ℕ) (j : OpenPath n a) : Prop :=
  NaturalOpenLegal x n a (fun t => (j t).val)
def openLetter (x : ℝ) (n a : ℕ) (j : OpenPath n a) (i : Fin n) : ℕ :=
  (phaseIncrement x i.val+(j i.castSucc).val-(j i.succ).val : ℤ).toNat
def geometricP : ℝ := 1/slope
def geometricQ : ℝ := 1-geometricP
def letterProbability (k : ℕ) : ℝ := geometricP*geometricQ^(k-1)
def openReward (x : ℝ) (n a : ℕ) (j : OpenPath n a) : ℝ :=
  ∑ i : Fin n, phaseWeight x i.val*(2 : ℝ)^(-((j i.castSucc).val : ℤ))
def openKernel (x : ℝ) (n a : ℕ) (lam : ℝ) : ℝ :=
  ∑ j : OpenPath n a, if OpenLegal x n a j then
    (∏ i : Fin n, letterProbability (openLetter x n a j i))*Real.exp (lam*openReward x n a j) else 0
def freeKernelValues (n : ℕ) (lam : ℝ) : Set ℝ :=
  {v | ∃ x : ℝ, ∃ a : ℕ, 0 ≤ x ∧ x < 1 ∧ v = openKernel x n a lam}
def freeKernelSup (n : ℕ) (lam : ℝ) : ℝ := sSup (freeKernelValues n lam)
def blockLower (L : ℕ) (lam : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, Real.log (rewardPartition x L lam))/(L : ℝ)
def phaseCellPoint (n : ℕ) (i : Fin (n+1)) : ℝ := Int.fract (-((i.val : ℝ)*slope))
def finiteInitialMax (n J : ℕ) (lam : ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (n+1) × Fin (J+1))).sup'
    ⟨(0,0), Finset.mem_univ _⟩ (fun p => openKernel (phaseCellPoint n p.1) n p.2.val lam)
def chernoffTilt : ℝ := -(Real.log geometricQ)/2
def initialTailEnvelope (n J : ℕ) (lam : ℝ) : ℝ :=
  Real.exp (lam*(n : ℝ)*(2 : ℝ)^(-((J/2 : ℕ) : ℤ))) +
  Real.exp (lam*(n : ℝ)-chernoffTilt*((J-J/2 : ℕ) : ℝ))*
    (geometricP*Real.exp chernoffTilt/(1-geometricQ*Real.exp chernoffTilt))^n
def finiteUpper (n J : ℕ) (lam : ℝ) : ℝ :=
  baselineEntropy+Real.log (max (finiteInitialMax n J lam) (initialTailEnvelope n J lam))/(n : ℝ)

abbrev FiniteEvaluationInput := (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)
def ComputableFiniteEvaluators : Prop :=
  ∃ E : FiniteEvaluationInput → BracketCode × BracketCode, Computable E ∧
    ∀ L0 n0 J a d bits : ℕ,
      Certified (blockLower (L0+1) (realInput a d)) (bits+8) (E ((L0,n0,J),(a,d,bits))).1 ∧
      Certified (finiteUpper (n0+1) J (realInput a d)) (bits+8) (E ((L0,n0,J),(a,d,bits))).2

abbrev PressureCertificateCode := (ℕ × ℕ × ℕ) × (BracketCode × BracketCode)
/-- This validity predicate refers ONLY to explicit finite expressions, not
to an unknown pressure or to its desired approximation theorem. -/
def FinitePressureCertificate (a d bits : ℕ) (C : PressureCertificateCode) : Prop :=
  Certified (blockLower (C.1.1+1) (realInput a d)) (bits+8) C.2.1 ∧
  Certified (finiteUpper (C.1.2.1+1) C.1.2.2 (realInput a d)) (bits+8) C.2.2 ∧
  (upperQ C.2.2-lowerQ C.2.1 : ℚ) ≤ (1 : ℚ)/(2 : ℚ)^bits
def ComputablePressureCertificates : Prop :=
  ∃ A : (ℕ × ℕ × ℕ) → PressureCertificateCode, Computable A ∧
    ∀ a d bits : ℕ, FinitePressureCertificate a d bits (A (a,d,bits))

def tiltCap (c : ℝ) : ℝ := 4/(1-c)
def gridTilt (c : ℝ) (N : ℕ) (i : Fin (N+1)) : ℝ := ((i.val : ℝ)/(N : ℝ))*tiltCap c
def gridMinimum (M : Model) (c : ℝ) (N : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (N+1))).inf' ⟨0, Finset.mem_univ _⟩
    (fun i => defectObjective M c (gridTilt c N i))
def gridError (c : ℝ) (N : ℕ) : ℝ :=
  (1+(1-c)*meanReference)*tiltCap c/(N : ℝ)
def entropyErrorBudget (c : ℝ) (N : ℕ) (dp db dscale : ℝ) : ℝ :=
  (1/Real.log 10+dscale)*(dp+(1-c)*tiltCap c*db+gridError c N)+baselineEntropy*dscale
def rationalGridTilt (c : ℚ) (N : ℕ) (i : Fin (N+1)) : ℚ :=
  ((i.val : ℚ)/(N : ℚ))*(4/(1-c))
def rationalGridEstimate (c : ℚ) (N : ℕ) (values : Fin (N+1) → ℚ) (bApprox scaleApprox : ℚ) : ℚ :=
  scaleApprox*((Finset.univ : Finset (Fin (N+1))).inf' ⟨0, Finset.mem_univ _⟩
    (fun i => values i+rationalGridTilt c N i*(1-c)*bApprox))

/-- Explicit conservative budget proposal. Decode the first component as N-1;
the other three are dyadic exponents for dp, db and dscale. No real oracle. -/
def budgetChoice (input : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((input.2.1+1)*2^(input.2.2+20),input.2.2+20,input.2.2+20,input.2.2+20)

def normalizationBits (input : ℕ × ℕ × ℕ) : ℕ := input.2.2+input.1+8

/-- PROPOSED rows only. No numerical bound/certificate has been supplied.
Each pair encodes c=a/(d+1); the last row is the exact endpoint c=1. -/
def tableRows : Fin 6 → (ℕ × ℕ) × ℕ :=
  ![((3,3),20),((9,9),20),((99,99),20),((999,999),20),((9999,9999),20),((1,0),0)]
def ProposedTableValid (M : Model) (entries : Fin 6 → BracketCode) : Prop :=
  (∀ i, Certified (M.rho (realInput (tableRows i).1.1 (tableRows i).1.2))
    (tableRows i).2 (entries i)) ∧ entries 5 = zeroBracket

def fullLengthNormalizedLogCount (c : ℝ) (r : ℕ) : ℝ :=
  Real.log (sourceCount r (c*literalReference slope r) : ℝ)/((r : ℝ)*Real.log 10)
def UnrestrictedLiteralM4LimitCandidate : Prop :=
  ∃ rho : ℝ → ℝ, ∀ c : ℝ, (3 : ℝ)/4 ≤ c → c ≤ 1 →
    (∀ r : ℕ, 0 < r → 1 ≤ sourceCount r (c*phaseZeroReference slope r)) ∧
    Tendsto (sourceLogCount c) atTop (𝓝 (rho c))
def FullLengthNormalizedEntropyLaw (M : Model) : Prop :=
  ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
    (∀ r : ℕ, 0 < r → 1 ≤ sourceCount r (c*literalReference slope r)) ∧
    Tendsto (fullLengthNormalizedLogCount c) atTop (𝓝 (M.rho c))
def FixedThresholdRefutationWitness (M : Model) : Prop :=
  (∀ r : ℕ, 0 < r → 1 ≤ sourceCount r (phaseZeroReference slope r)) ∧
  ∃ u v : ℕ → ℕ, StrictMono u ∧ StrictMono v ∧
    Tendsto (fun n => sourceLogCount 1 (u n)) atTop (𝓝 (M.rho 1)) ∧
    Tendsto (fun n => sourceLogCount 1 (v n)) atTop (𝓝 (M.rho ((1 : ℝ)/2))) ∧
    M.rho 1 < M.rho ((1 : ℝ)/2) ∧
    ¬ ∃ a : ℝ, Tendsto (sourceLogCount 1) atTop (𝓝 a)

end
end ExternalBridgePressureCompleteDraft
