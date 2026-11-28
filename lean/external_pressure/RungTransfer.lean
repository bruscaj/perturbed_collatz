import RungDefinitions
import Mathlib.Tactic.Linarith

namespace ExternalRungTransfer
open ExternalRungSpec ExternalPrefixSpec

theorem defect_nonneg (θ : ℝ) (r : ℕ) : 0 ≤ defect θ r := by
  exact sub_nonneg.mpr (Int.le_ceil _)

theorem defect_lt_one (θ : ℝ) (r : ℕ) : defect θ r < 1 := by
  have := Int.ceil_lt_add_one ((r : ℝ) * θ)
  unfold defect
  linarith

theorem rung_cap (θ : ℝ) (r t : ℕ) (hr : IsRung θ r) (ht : t < r) :
    ⌊(t : ℝ) * θ + defect θ r⌋ = ⌊(t : ℝ) * θ⌋ := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact le_trans (Int.floor_le _) (le_add_of_nonneg_right (defect_nonneg θ r))
  · by_cases ht0 : t = 0
    · subst t
      simpa using defect_lt_one θ r
    · have hrec := hr.2 t (Nat.pos_of_ne_zero ht0) ht
      have hceil : (⌈(t : ℝ) * θ⌉ : ℝ) ≤ (⌊(t : ℝ) * θ⌋ : ℝ) + 1 := by
        exact_mod_cast Int.ceil_le_floor_add_one ((t : ℝ) * θ)
      unfold defect at hrec ⊢
      linarith

theorem endpoint (θ : ℝ) (hθ : Irrational θ) (r : ℕ) (hr : 0 < r) :
    ⌈(r : ℝ) * θ⌉ = ⌊(r : ℝ) * θ⌋ + 1 := by
  apply (Int.ceil_eq_floor_add_one_iff_notMem _).mpr
  rintro ⟨z, hz⟩
  exact (hθ.natCast_mul (Nat.ne_of_gt hr)).ne_int z hz.symm

theorem floor_increments (θ : ℝ) (hθ : 1 ≤ θ) (t : ℕ) :
    floorProfile θ t + 1 ≤ floorProfile θ (t + 1) := by
  apply Int.le_floor.mpr
  have := Int.floor_le ((t : ℝ) * θ)
  simp only [floorProfile, Int.cast_add, Int.cast_one, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem source_closing_iff (θ : ℝ) (hθ : Irrational θ) (r : ℕ)
    (hr : IsRung θ r) (K : Profile) :
    SourceAdmissible θ K r ↔ ClosingAdmissible (floorProfile θ) K r := by
  unfold SourceAdmissible ClosingAdmissible
  simp only [endpoint θ hθ r hr.1, floorProfile]
  have hc : (∀ t : ℕ, t < r → K t ≤ ⌊(t : ℝ) * θ + defect θ r⌋) ↔
      (∀ t : ℕ, t < r → K t ≤ ⌊(t : ℝ) * θ⌋) := by
    constructor <;> intro h t ht <;> simpa only [rung_cap θ r t hr ht] using h t ht
  rw [hc]

end ExternalRungTransfer
