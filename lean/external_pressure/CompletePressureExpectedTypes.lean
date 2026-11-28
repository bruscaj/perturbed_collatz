import CompletePressureDefinitions

/-! UNFROZEN accepted-claim completion goals, not proofs or a freeze register.
Actual table entries and the eight critical-law internals remain separate. -/
namespace ExternalBridgePressureCompleteDraft
open ExternalBridgePressureDraft ExternalFiniteBridgeDraft Filter
open scoped BigOperators Topology
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def RationalBracketSemantics : Prop := ∀ q : BracketCode, ∀ bits : ℕ,
  0 < ((q.2.2+1 : ℕ) : ℚ) ∧
  (Narrow bits q ↔ lowerQ q ≤ upperQ q ∧ upperQ q-lowerQ q ≤ (1 : ℚ)/(2 : ℚ)^bits)

def OpenPathCompleteness : Prop := ∀ x : ℝ, 0 ≤ x → x < 1 → ∀ n a : ℕ,
  (∀ j : Fin (n+1) → ℕ, NaturalOpenLegal x n a j → ∀ t, j t ≤ a+t.val) ∧
  (∀ j : Fin (n+1) → ℕ, NaturalOpenLegal x n a j ↔
    ∃ k : OpenPath n a, OpenLegal x n a k ∧ ∀ t, (k t).val = j t) ∧
  (∀ j : OpenPath n a, OpenLegal x n a j → ∀ i, 1 ≤ openLetter x n a j i)

def FreeKernelWellPosed : Prop := ∀ lam : ℝ, 0 ≤ lam → ∀ n : ℕ,
  (freeKernelValues n lam).Nonempty ∧ BddAbove (freeKernelValues n lam) ∧
  1 ≤ freeKernelSup n lam ∧ freeKernelSup n lam ≤ Real.exp (lam*(n : ℝ))

def ExactPhaseCellMaximum : Prop := ∀ lam : ℝ, 0 ≤ lam → ∀ n J : ℕ,
  (∀ x : ℝ, 0 ≤ x → x < 1 → ∀ a : ℕ, a ≤ J →
    openKernel x n a lam ≤ finiteInitialMax n J lam) ∧
  freeKernelSup n lam ≤ max (finiteInitialMax n J lam) (initialTailEnvelope n J lam)

def FinitePressureBrackets : Prop := ∃ M : Model, CorePressureLaw M ∧ PressureBounds M ∧
  ∀ lam : ℝ, 0 ≤ lam → ∀ L n J : ℕ, 0 < L → 0 < n →
    blockLower L lam ≤ M.P lam ∧ M.P lam ≤ finiteUpper n J lam

def FinitePressureCofinality : Prop := ∀ lam : ℝ, 0 ≤ lam → ∀ eps : ℝ, 0 < eps →
  ∃ L n J : ℕ, 0 < L ∧ 0 < n ∧ 0 ≤ finiteUpper n J lam-blockLower L lam ∧
    finiteUpper n J lam-blockLower L lam < eps

def ElementaryConstantEvaluation : Prop :=
  ∃ A : ℕ → BracketCode × BracketCode × BracketCode × BracketCode, Computable A ∧
    ∀ bits : ℕ,
      Certified slope (bits+8) (A bits).1 ∧
      Certified meanReference (bits+8) (A bits).2.1 ∧
      Certified baselineEntropy (bits+8) (A bits).2.2.1 ∧
      Certified (1/Real.log 10) (bits+8) (A bits).2.2.2

def FiniteEvaluationProgram : Prop := ComputableFiniteEvaluators
def FinitePressureCertificateSearch : Prop := ComputablePressureCertificates

def PressureCertificateSoundness : Prop := ∃ M : Model, CorePressureLaw M ∧ PressureBounds M ∧
  ∀ a d bits : ℕ, ∀ C : PressureCertificateCode, FinitePressureCertificate a d bits C →
    (lowerQ C.2.1 : ℝ) ≤ M.P (realInput a d) ∧
    M.P (realInput a d) ≤ (upperQ C.2.2 : ℝ) ∧
    (upperQ C.2.2 : ℝ)-(lowerQ C.2.1 : ℝ) ≤ (2 : ℝ)^(-(bits : ℤ))

def EffectiveAllTiltPressure : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ ComputablePressureBrackets M

def DefectNormalizationErrorBudget : Prop := ∃ M : Model, CorePressureLaw M ∧
  ∀ lam : ℝ, 0 ≤ lam → ∀ pressureApprox bApprox dp db : ℝ,
    0 ≤ dp → 0 ≤ db → |pressureApprox-M.P lam| ≤ dp → |bApprox-meanReference| ≤ db →
    |(pressureApprox-lam*bApprox)-M.p lam| ≤ dp+lam*db

def NormalizationBudgetProgram : Prop := Computable normalizationBits ∧
  ∀ a d bits : ℕ,
    (2 : ℝ)^(-((bits+8 : ℕ) : ℤ))+
      realInput a d*(2 : ℝ)^(-((normalizationBits (a,d,bits) : ℕ) : ℤ)) ≤
        (2 : ℝ)^(-((bits+6 : ℕ) : ℤ))

def AllThresholdRungEntropy : Prop := ∃ M : Model,
  CorePressureLaw M ∧ AllThresholdEntropyLaw M

def ExactSharedLegendre : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M

def EntropyContinuityAndStrictness : Prop := ∃ M : Model,
  CorePressureLaw M ∧ AllThresholdEntropyLaw M ∧
  ContinuousOn M.rho (Set.Icc 0 1) ∧
  ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → M.rho d < M.rho c

def CompactTiltMinimization : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  ∀ c : ℝ, 0 ≤ c → c < 1 → ∃ lam : ℝ,
    0 ≤ lam ∧ lam ≤ tiltCap c ∧ defectObjective M c lam = sInf (objectiveValues M c)

def FiniteTiltGridBudget : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  ∀ c : ℝ, 0 ≤ c → c < 1 → ∀ N : ℕ, 1 ≤ N →
    0 ≤ gridMinimum M c N-sInf (objectiveValues M c) ∧
    gridMinimum M c N-sInf (objectiveValues M c) ≤ gridError c N

def RationalEntropyErrorBudget : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  ∀ a d N : ℕ, a < d+1 → 1 ≤ N →
  ∀ values : Fin (N+1) → ℚ, ∀ bApprox scaleApprox : ℚ, ∀ dp db dscale : ℝ,
    0 ≤ dp → 0 ≤ db → 0 ≤ dscale →
    (∀ i, |(values i : ℝ)-M.p (gridTilt (realInput a d) N i)| ≤ dp) →
    |(bApprox : ℝ)-meanReference| ≤ db →
    |(scaleApprox : ℝ)-1/Real.log 10| ≤ dscale →
    |(rationalGridEstimate (rationalInput a d) N values bApprox scaleApprox : ℝ)-M.rho (realInput a d)| ≤
      entropyErrorBudget (realInput a d) N dp db dscale

def ExplicitBudgetProgram : Prop := Computable budgetChoice ∧
  ∀ a d bits : ℕ, a < d+1 →
    let B := budgetChoice (a,d,bits)
    entropyErrorBudget (realInput a d) (B.1+1)
      ((2 : ℝ)^(-(B.2.1 : ℤ))) ((2 : ℝ)^(-(B.2.2.1 : ℤ))) ((2 : ℝ)^(-(B.2.2.2 : ℤ))) ≤
        (2 : ℝ)^(-((bits+4 : ℕ) : ℤ))

def EffectiveAllThresholdEntropy : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  ComputablePressureBrackets M ∧ ComputableEntropyBrackets M ∧ ComputableEntropyModulus M

def UniformComputableEntropyModulus : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  ComputablePressureBrackets M ∧ ComputableEntropyModulus M

def StrongR8Regularity : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ StrongR8Law M

def SharedR9Expansion : Prop := ∃ M : Model,
  CorePressureLaw M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  Tendsto (nearOneResidual M.rho) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)

def SharedR9LeadingTerm : Prop := ∃ M : Model,
  CorePressureLaw M ∧ AllThresholdEntropyLaw M ∧
  Tendsto (fun eps : ℝ => M.rho (1-eps)/(eps*Real.log (1/eps)))
    (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (3/(2*Real.log 2*Real.log 10)))

/-- Joint one-model analytic/effective target. The actual executed table and
the still-untyped critical-law internals are NOT claimed delivered by this type. -/
def JointAcceptedCandidatePackage : Prop := ∃ M : Model,
  CorePressureLaw M ∧ PressureBounds M ∧ AllThresholdEntropyLaw M ∧ LegendreLaw M ∧
  StrongR8Law M ∧ ComputablePressureBrackets M ∧ ComputableEntropyBrackets M ∧
  ComputableEntropyModulus M ∧
  Tendsto (nearOneResidual M.rho) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)

-- Separate unresolved source-scope candidates. Neither is silently assumed.
def CorrectedAllLengthNormalization : Prop := ∃ M : Model,
  CorePressureLaw M ∧ AllThresholdEntropyLaw M ∧ FullLengthNormalizedEntropyLaw M
def OriginalFixedThresholdRefutation : Prop := ∃ M : Model,
  CorePressureLaw M ∧ AllThresholdEntropyLaw M ∧ FixedThresholdRefutationWitness M

end
end ExternalBridgePressureCompleteDraft
