import DensityBounds

/-! Exact equivalence of first-N odd seeds and the source's cutoff normalization. -/
namespace ExternalO3SourceDensity
open ExternalO3Spec Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem odd_range_image (X : ℕ) :
    (Finset.range ((X + 1) / 2)).image (fun n => 2 * n + 1) =
      (Finset.range (X + 1)).filter IsOddSeed := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, IsOddSeed]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · rintro ⟨hx, hpos, hodd⟩
    exact ⟨x / 2, by omega, by omega⟩

theorem failure_range_image (φ : Correction) (X : ℕ) :
    ((Finset.range ((X + 1) / 2)).filter (fun n => FailsAt φ (2 * n + 1))).image
        (fun n => 2 * n + 1) =
      (Finset.range (X + 1)).filter (FailsAt φ) := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨n, ⟨hn, hf⟩, rfl⟩
    exact ⟨by omega, hf⟩
  · rintro ⟨hx, hf⟩
    have hpos := hf.1.1
    have hodd := hf.1.2
    have heq : 2 * (x / 2) + 1 = x := by omega
    exact ⟨x / 2, ⟨by omega, by simpa only [heq] using hf⟩, heq⟩

theorem source_frequency_eq (φ : Correction) (X : ℕ) :
    sourceFrequency φ X = failureFrequency φ ((X + 1) / 2) := by
  classical
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    change 2 * a + 1 = 2 * b + 1 at h
    omega
  unfold sourceFrequency failureFrequency failureCount
  rw [← failure_range_image φ X, ← odd_range_image X,
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj,
    Finset.card_range]

theorem source_density_equivalence : SourceDensityEquivalence := by
  intro φ d
  have hcut : Tendsto (fun X : ℕ => (X + 1) / 2) atTop atTop :=
    tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨2 * b, fun X hX => by omega⟩)
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨b, fun N hN => by omega⟩)
  have heq (N : ℕ) : sourceFrequency φ (2 * N) = failureFrequency φ N := by
    rw [source_frequency_eq]
    congr 1
    omega
  constructor
  · intro hd
    have h := hd.comp hcut
    change Tendsto (fun X : ℕ => sourceFrequency φ X) atTop (𝓝 d)
    simpa only [Function.comp_def, source_frequency_eq] using h
  · intro hd
    have h := hd.comp hdouble
    change Tendsto (failureFrequency φ) atTop (𝓝 d)
    simpa only [Function.comp_def, heq] using h

end ExternalO3SourceDensity
