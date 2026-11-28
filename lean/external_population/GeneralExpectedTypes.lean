import GeneralDefinitions

/-! UNFROZEN expected theorem types only. No values, axioms or proof holes. -/
namespace ExternalO3GeneralDraft
open Filter
open scoped Topology BigOperators

/-- Finite block endpoints are actual odd Syracuse states, without termination. -/
def BlocksWellDefined : Prop :=
  ∀ x : ℕ, ExternalO3Spec.IsOddSeed x →
    ∀ i : ℕ,
      let y := futureBlockSeed x i
      let r := ExternalO3Spec.blockLength y
      ExternalO3Spec.IsOddSeed y ∧ 0 < r ∧
      (∀ t : ℕ, t + 1 < r →
        ExternalO3Spec.strideValuation ((Nat.iterate ExternalO3Spec.stride t) y) = 1) ∧
      2 ≤ ExternalO3Spec.strideValuation
        ((Nat.iterate ExternalO3Spec.stride (r - 1)) y)

def WindowValidity : Prop :=
  ∀ (h : Depth) (x : ℕ), ExternalO3Spec.IsOddSeed x → ValidWindow h (window h x)

/-- An ascending step changes only the remaining current run; an exit shifts. -/
def WindowTransport : Prop :=
  ∀ (h : Depth) (x : ℕ), ExternalO3Spec.IsOddSeed x →
    (2 ≤ ExternalO3Spec.blockLength x →
      window h (ExternalO3Spec.stride x) = decrementHead h (window h x)) ∧
    (ExternalO3Spec.blockLength x = 1 →
      window h x = prependOne h (window h (ExternalO3Spec.stride x)))

/-- Extending arbitrary source corrections off positive windows is immaterial. -/
def CorrectionRestriction : Prop :=
  ∀ (h : Depth) (φ ψ : Correction h),
    (∀ w : Window h, ValidWindow h w → φ w = ψ w) →
    ∀ x : ℕ, ExternalO3Spec.IsOddSeed x → (FailsAt h φ x ↔ FailsAt h ψ x)

/-- One is not stopped or made absorbing by a different map; its blocks persist. -/
def FixedPointAndZero : Prop :=
  ExternalO3Spec.stride 1 = 1 ∧
    (∀ h : Depth, window h 1 = (fun _ => 1)) ∧
    (∀ (h : Depth) (φ : Correction h), FailsAt h φ 1 ∧ ¬FailsAt h φ 0)

/-- Exact finite arithmetic realization before any countable marginalization. -/
def RefinedCylinderClasses : Prop :=
  ∀ (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ),
    ValidBlockData m lengths exits →
    ∃! d : ℕ, d < 2 ^ refinedExponent m lengths exits ∧
      ∀ n : ℕ,
        (RefinedCell m lengths exits (2 * n + 1) ↔
          n % 2 ^ refinedExponent m lengths exits = d)

/-- Relative odd-seed density of every exact finite refinement. -/
def RefinedCylinderDensities : Prop :=
  ∀ (m : ℕ) (lengths : Fin (m + 1) → ℕ) (exits : Fin m → ℕ),
    ValidBlockData m lengths exits →
    Tendsto (populationFrequency (fun n => RefinedCell m lengths exits (2 * n + 1)))
      atTop (nhds ((2 : ℝ) ^ (-((refinedExponent m lengths exits : ℕ) : ℤ))))

/-- The exact refinement is a genuine seed partition, including all hidden exits. -/
def RefinedLabelCell : Prop :=
  ∀ (m : ℕ) (data : RefinedIndex m) (n : ℕ),
    refinedLabel m n = data ↔
      RefinedCell m (decodedLengths m data) (decodedExits m data) (2 * n + 1)

def RefinedWeightLaw : Prop :=
  ∀ m : ℕ, Summable (refinedWeight m) ∧
    (∑' data : RefinedIndex m, refinedWeight m data) = 1 ∧
    ∀ data : RefinedIndex m, 0 < refinedWeight m data

def RefinementProjectionLaw : Prop :=
  ∀ (h : Depth) (n : ℕ), refinementProjection h (refinedLabel h.val n) = label h n

/-- Geometric marginalization; it is not assumed natural-density additivity. -/
def CoarseMarginalLaw : Prop :=
  ∀ (h : Depth) (e : Edge h), Summable (refinedFiberWeight h e) ∧
    (∑' data : RefinedIndex h.val, refinedFiberWeight h e data) = weight h e

/-- Positive cell masses and total one are unconditional geometric identities. -/
def WeightLaw : Prop :=
  ∀ h : Depth, Summable (weight h) ∧ (∑' e : Edge h, weight h e) = 1 ∧
    ∀ e : Edge h, 0 < weight h e

/-- Each coarse finite-information label has the advertised literal density. -/
def CoordinateLaw : Prop :=
  ∀ (h : Depth) (e : Edge h),
    Tendsto (populationFrequency (fun n => label h n = e)) atTop (nhds (weight h e))

/-- Explicit realizability, rather than a definition with impossible data. -/
def LabelRealizable : Prop := ∀ (h : Depth) (e : Edge h), ∃ n : ℕ, label h n = e

/-- Exact finite-seed error. Limiting gain zero is therefore still failure. -/
def LiteralGainIdentity : Prop :=
  ∀ (h : Depth) (φ : Correction h) (n : ℕ),
    rawPotential h φ (ExternalO3Spec.stride (2 * n + 1)) - rawPotential h φ (2 * n + 1) =
      gain h φ (label h n) + Real.log (1 + 1 / (3 * ((2 * n + 1 : ℕ) : ℝ)))

/-- Thresholds may depend on the cell and on the arbitrary correction. -/
def CellStabilization : Prop :=
  ∀ (h : Depth) (φ : Correction h) (e : Edge h),
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → label h n = e →
      (FailsAt h φ (2 * n + 1) ↔ Bad h φ e)

def SelectedMassSummable : Prop :=
  ∀ (h : Depth) (φ : Correction h), Summable (selectedWeight h φ)

/-- Actual natural density for every unrestricted correction at every fixed h. -/
def DensityExists : Prop :=
  ∀ (h : Depth) (φ : Correction h),
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ HasFailureDensity h φ d

/-- No density or product law premise is built into the unconditional target. -/
def DensityEqualsSymbolic : Prop :=
  ∀ (h : Depth) (φ : Correction h),
    Summable (selectedWeight h φ) ∧
    0 ≤ symbolicFailureDensity h φ ∧ symbolicFailureDensity h φ ≤ 1 ∧
    HasFailureDensity h φ (symbolicFailureDensity h φ)

def DensityUnique : Prop :=
  ∀ (h : Depth) (φ : Correction h) (d e : ℝ),
    HasFailureDensity h φ d → HasFailureDensity h φ e → d = e

def SourceDensityEquivalence : Prop :=
  ∀ (h : Depth) (φ : Correction h) (d : ℝ),
    HasFailureDensity h φ d ↔ Tendsto (sourceFrequency h φ) atTop (nhds d)

/-- The all-window correction parameterization reduces to the whole frozen h=1 class. -/
def DepthOneCompatibility : Prop :=
  (∀ φ : ExternalO3Spec.Correction, scalarizeOne (liftOne φ) = φ) ∧
  (∀ φ : Correction depthOne, liftOne (scalarizeOne φ) = φ) ∧
  (∀ (φ : ExternalO3Spec.Correction) (N : ℕ),
    failureFrequency depthOne (liftOne φ) N = ExternalO3Spec.failureFrequency φ N) ∧
  (∀ (φ : ExternalO3Spec.Correction) (X : ℕ),
    sourceFrequency depthOne (liftOne φ) X = ExternalO3Spec.sourceFrequency φ X) ∧
  (∀ φ : ExternalO3Spec.Correction,
    symbolicFailureDensity depthOne (liftOne φ) = ExternalO3Spec.symbolicFailureDensity φ)

end ExternalO3GeneralDraft
