import PrefixDefinitions
import Mathlib.NumberTheory.Real.Irrational

/-! Source-faithful draft specification; not yet independently frozen. -/
namespace ExternalRungSpec
open ExternalPrefixSpec

noncomputable def defect (θ : ℝ) (r : ℕ) : ℝ :=
  (⌈(r : ℝ) * θ⌉ : ℤ) - (r : ℝ) * θ

def IsRung (θ : ℝ) (r : ℕ) : Prop :=
  0 < r ∧ ∀ t : ℕ, 0 < t → t < r → defect θ r < defect θ t

noncomputable def floorProfile (θ : ℝ) : Profile := fun t => ⌊(t : ℝ) * θ⌋

def SourceAdmissible (θ : ℝ) (K : Profile) (r : ℕ) : Prop :=
  K 0 = 0 ∧ K r = ⌈(r : ℝ) * θ⌉ ∧
  (∀ t : ℕ, t < r → K t + 1 ≤ K (t + 1)) ∧
  (∀ t : ℕ, t < r → K t ≤ ⌊(t : ℝ) * θ + defect θ r⌋)

end ExternalRungSpec
