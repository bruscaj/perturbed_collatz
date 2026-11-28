import GeneralBlockWords
import Progressions

/-! Natural densities of the exact refined literal seed cylinders. -/
namespace ExternalO3GeneralCylinderDensity
open ExternalO3GeneralDraft ExternalO3GeneralBlockWords Filter
open scoped Topology

theorem refined_cylinder_densities : RefinedCylinderDensities := by
  classical
  intro m lengths exits hdata
  obtain ⟨d, ⟨hd, hevent⟩, _⟩ := refined_cylinder_classes m lengths exits hdata
  have hp : (fun n => RefinedCell m lengths exits (2 * n + 1)) =
      (fun n => n % 2 ^ refinedExponent m lengths exits = d) := by
    funext n
    exact propext (hevent n)
  rw [hp]
  have hh := ExternalO3Progressions.dyadicClass_density
    (refinedExponent m lengths exits) d hd
  have hfreq : populationFrequency
      (fun n => n % 2 ^ refinedExponent m lengths exits = d) =
      (fun N : ℕ => (((Finset.range N).filter
        (fun n => n % 2 ^ refinedExponent m lengths exits = d)).card : ℝ) / (N : ℝ)) := by
    funext N
    unfold populationFrequency
    congr
  rw [hfreq]
  simpa only [zpow_neg, zpow_natCast, one_div] using hh

end ExternalO3GeneralCylinderDensity
