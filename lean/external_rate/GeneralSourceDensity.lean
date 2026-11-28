import GeneralExpectedTypes
import SourceDensity

/-! Literal cutoff normalization and uniqueness at every fixed positive depth.
No existence of a density or symbolic population law is assumed. -/
namespace ExternalO3GeneralSourceDensity
open ExternalO3GeneralDraft Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem failure_range_image (h : Depth) (φ : Correction h) (X : ℕ) :
    ((Finset.range ((X + 1) / 2)).filter (fun n => FailsAt h φ (2 * n + 1))).image
        (fun n => 2 * n + 1) =
      (Finset.range (X + 1)).filter (FailsAt h φ) := by
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

theorem source_frequency_eq (h : Depth) (φ : Correction h) (X : ℕ) :
    sourceFrequency h φ X = failureFrequency h φ ((X + 1) / 2) := by
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega
  unfold sourceFrequency failureFrequency failureCount
  rw [← failure_range_image h φ X, ← ExternalO3SourceDensity.odd_range_image X,
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj,
    Finset.card_range]

theorem source_density_equivalence : SourceDensityEquivalence := by
  intro h φ d
  have hcut : Tendsto (fun X : ℕ => (X + 1) / 2) atTop atTop :=
    tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨2 * b, fun X hX => by omega⟩)
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨b, fun N hN => by omega⟩)
  have heq (N : ℕ) : sourceFrequency h φ (2 * N) = failureFrequency h φ N := by
    rw [source_frequency_eq]
    congr 1
    omega
  constructor
  · intro hd
    have hlim := hd.comp hcut
    change Tendsto (fun X : ℕ => sourceFrequency h φ X) atTop (𝓝 d)
    simpa only [Function.comp_def, source_frequency_eq] using hlim
  · intro hd
    have hlim := hd.comp hdouble
    change Tendsto (failureFrequency h φ) atTop (𝓝 d)
    simpa only [Function.comp_def, heq] using hlim

theorem density_unique : DensityUnique := by
  intro h φ d e hd he
  exact tendsto_nhds_unique hd he

theorem failure_count_le (h : Depth) (φ : Correction h) (N : ℕ) : failureCount h φ N ≤ N := by
  unfold failureCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

theorem frequency_nonneg (h : Depth) (φ : Correction h) (N : ℕ) :
    0 ≤ failureFrequency h φ N := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem frequency_le_one (h : Depth) (φ : Correction h) (N : ℕ) :
    failureFrequency h φ N ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [failureFrequency, failureCount]
  · have hpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    exact (div_le_one hpos).mpr (Nat.cast_le.mpr (failure_count_le h φ N))

theorem density_bounds (h : Depth) (φ : Correction h) (d : ℝ)
    (hd : HasFailureDensity h φ d) : 0 ≤ d ∧ d ≤ 1 := by
  exact ⟨ge_of_tendsto hd (Eventually.of_forall (frequency_nonneg h φ)),
    le_of_tendsto hd (Eventually.of_forall (frequency_le_one h φ))⟩

end ExternalO3GeneralSourceDensity
