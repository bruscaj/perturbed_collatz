import AnalyticRotation
import Mathlib.Order.Interval.Finset.Nat

/-! Finite, half-open grid counts. No limit or distribution premise. -/
namespace ExternalBridgePressureAnalyticRotationGrid
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def gridCount (δ : ℝ) (T : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range T).filter (fun j : ℕ => a ≤ (j : ℝ)*δ ∧ (j : ℝ)*δ < b)).card

theorem grid_count_exact (δ : ℝ) (hδ : 0 < δ) (T : ℕ)
    (hcover : 1 ≤ (T : ℝ)*δ) (a b : ℝ) (_hab : a ≤ b) (hb : b ≤ 1) :
    gridCount δ T a b = ⌈b/δ⌉₊ - ⌈a/δ⌉₊ := by
  unfold gridCount
  have heq : ((Finset.range T).filter (fun j : ℕ => a ≤ (j : ℝ)*δ ∧ (j : ℝ)*δ < b)) =
      Finset.Ico ⌈a/δ⌉₊ ⌈b/δ⌉₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rw [Nat.ceil_le, Nat.lt_ceil]
    constructor
    · rintro ⟨_, hlo, hhi⟩
      exact ⟨(div_le_iff₀ hδ).mpr hlo, (lt_div_iff₀ hδ).mpr hhi⟩
    · rintro ⟨hlo, hhi⟩
      have hi : (j : ℝ)*δ < b := (lt_div_iff₀ hδ).mp hhi
      have hjT : (j : ℝ) < T := by nlinarith
      exact ⟨by exact_mod_cast hjT, (div_le_iff₀ hδ).mp hlo, hi⟩
  rw [heq, Nat.card_Ico]

/-- The unnormalized count differs from interval length divided by mesh by less than two. -/
theorem grid_count_error (δ : ℝ) (hδ : 0 < δ) (T : ℕ)
    (hcover : 1 ≤ (T : ℝ)*δ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(gridCount δ T a b : ℝ) - (b-a)/δ| < 2 := by
  rw [grid_count_exact δ hδ T hcover a b hab hb,
    Nat.cast_sub (Nat.ceil_mono (div_le_div_of_nonneg_right hab hδ.le))]
  have hloa := Nat.le_ceil (a/δ)
  have hlob := Nat.le_ceil (b/δ)
  have hhia := Nat.ceil_lt_add_one (show 0 ≤ a/δ by positivity)
  have hbnonneg : 0 ≤ b := le_trans ha hab
  have hhib := Nat.ceil_lt_add_one (show 0 ≤ b/δ by positivity)
  rw [abs_lt]
  constructor <;> (rw [sub_div]; linarith)

/-- Normalized finite-grid discrepancy, before taking any orbit averages. -/
theorem grid_normalized_error (δ : ℝ) (hδ : 0 < δ) (T : ℕ) (hT : 0 < T)
    (hcover : 1 ≤ (T : ℝ)*δ) (hover : (T : ℝ)*δ < 1+δ)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |(gridCount δ T a b : ℝ)/(T : ℝ) - (b-a)| < 2/(T : ℝ)+δ := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have herr := grid_count_error δ hδ T hcover a b ha hab hb
  have hscale : |(gridCount δ T a b : ℝ)/(T : ℝ) - (b-a)/((T : ℝ)*δ)| < 2/(T : ℝ) := by
    have hid : (gridCount δ T a b : ℝ)/(T : ℝ) - (b-a)/((T : ℝ)*δ) =
        ((gridCount δ T a b : ℝ)-(b-a)/δ)/(T : ℝ) := by field_simp
    rw [hid, abs_div, abs_of_pos hTp]
    exact (div_lt_div_iff_of_pos_right hTp).mpr herr
  have hlength : 0 ≤ b-a ∧ b-a ≤ 1 := by constructor <;> linarith
  have hdist : |(b-a)/((T : ℝ)*δ) - (b-a)| < δ := by
    rw [abs_of_nonpos (by exact sub_nonpos.mpr (div_le_self hlength.1 hcover))]
    have hden : 0 < (T : ℝ)*δ := by positivity
    have hfrac : (b-a)*((T : ℝ)*δ-1) < δ*((T : ℝ)*δ) := by
      nlinarith
    have hid : -((b-a)/((T : ℝ)*δ)-(b-a)) =
        ((b-a)*((T : ℝ)*δ-1))/((T : ℝ)*δ) := by field_simp; ring
    rw [hid]
    exact (div_lt_iff₀ hden).mpr hfrac
  calc
    |(gridCount δ T a b : ℝ)/(T : ℝ) - (b-a)| ≤
      |(gridCount δ T a b : ℝ)/(T : ℝ) - (b-a)/((T : ℝ)*δ)| +
        |(b-a)/((T : ℝ)*δ)-(b-a)| := abs_sub_le _ _ _
    _ < 2/(T : ℝ)+δ := add_lt_add hscale hdist

end
end ExternalBridgePressureAnalyticRotationGrid
