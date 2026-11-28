import AnalyticRotationGrid

/-! Uniform translated-grid counts, retaining both half-open endpoints. -/
namespace ExternalBridgePressureAnalyticCircleGrid
open ExternalBridgePressureAnalyticRotationGrid
open scoped BigOperators
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def chi (a b u : ℝ) : ℝ := if a ≤ u ∧ u < b then 1 else 0

theorem grid_count_sum (δ : ℝ) (T : ℕ) (a b : ℝ) :
    (gridCount δ T a b : ℝ) = ∑ j ∈ Finset.range T, chi a b ((j : ℝ)*δ) := by
  unfold gridCount chi
  simp

theorem fract_add_small (x u : ℝ) (hx : 0 ≤ x ∧ x < 1) (hu : 0 ≤ u ∧ u < 1) :
    Int.fract (x+u) = if x+u < 1 then x+u else x+u-1 := by
  split_ifs with h
  · exact Int.fract_eq_self.mpr ⟨by linarith, h⟩
  · have hs : Int.fract (x+u-1) = x+u-1 := Int.fract_eq_self.mpr
      ⟨by linarith, by linarith [hx.2,hu.2]⟩
    calc
      Int.fract (x+u) = Int.fract (x+u-(1 : ℤ)) := (Int.fract_sub_intCast (x+u) 1).symm
      _ = x+u-1 := by simpa using hs

theorem chi_rotate_left (x u a b : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) (ha : x ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    chi a b (Int.fract (x+u)) = chi (a-x) (b-x) u := by
  rw [fract_add_small x u hx hu]
  unfold chi
  split_ifs <;> (first | rfl | exfalso; simp_all only [not_and_or, not_le, not_lt]; rcases hx with ⟨hx0,hx1⟩; rcases hu with ⟨hu0,hu1⟩; (repeat' first | cases_type Or | cases_type And) <;> linarith)

theorem chi_rotate_right (x u a b : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ x) :
    chi a b (Int.fract (x+u)) = chi (a+1-x) (b+1-x) u := by
  rw [fract_add_small x u hx hu]
  unfold chi
  split_ifs <;> (first | rfl | exfalso; simp_all only [not_and_or, not_le, not_lt]; rcases hx with ⟨hx0,hx1⟩; rcases hu with ⟨hu0,hu1⟩; (repeat' first | cases_type Or | cases_type And) <;> linarith)

theorem chi_rotate_split (x u a b : ℝ) (hx : 0 ≤ x ∧ x < 1)
    (hu : 0 ≤ u ∧ u < 1) (ha : 0 ≤ a) (hax : a < x) (hxb : x < b) (hb : b ≤ 1) :
    chi a b (Int.fract (x+u)) = chi 0 (b-x) u + chi (a+1-x) 1 u := by
  rw [fract_add_small x u hx hu]
  unfold chi
  split_ifs <;> norm_num <;> (exfalso; simp_all only [not_and_or, not_le, not_lt, not_true_eq_false]; rcases hx with ⟨hx0,hx1⟩; rcases hu with ⟨hu0,hu1⟩; (repeat' first | cases_type Or | cases_type And) <;> (first | contradiction | linarith))


def circleGridAverage (x δ : ℝ) (T : ℕ) (a b : ℝ) : ℝ :=
  (∑ j ∈ Finset.range T, chi a b (Int.fract (x+(j : ℝ)*δ)))/(T : ℝ)

theorem translated_grid_error (δ : ℝ) (hδ : 0 < δ) (T : ℕ) (hT : 0 < T)
    (hcover : 1 ≤ (T : ℝ)*δ) (hover : (T : ℝ)*δ < 1+δ)
    (hinside : ∀ j : ℕ, j < T → (j : ℝ)*δ < 1)
    (x a b : ℝ) (hx : 0 ≤ x ∧ x < 1) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |circleGridAverage x δ T a b - (b-a)| < 4/(T : ℝ)+2*δ := by
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hsplit : 4/(T : ℝ) = 2/(T : ℝ)+2/(T : ℝ) := by ring
  have hbudget : 2/(T : ℝ)+δ < 4/(T : ℝ)+2*δ := by
    rw [hsplit]
    have : 0 < 2/(T : ℝ) := by positivity
    linarith
  have hu (j : ℕ) (hj : j ∈ Finset.range T) : 0 ≤ (j : ℝ)*δ ∧ (j : ℝ)*δ < 1 :=
    ⟨by positivity, hinside j (Finset.mem_range.mp hj)⟩
  by_cases hleft : x ≤ a
  · have hsum : circleGridAverage x δ T a b = (gridCount δ T (a-x) (b-x) : ℝ)/T := by
      unfold circleGridAverage
      rw [grid_count_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => chi_rotate_left x _ a b hx (hu j hj) hleft hab hb)
    rw [hsum]
    have he := grid_normalized_error δ hδ T hT hcover hover (a-x) (b-x)
      (by linarith) (by linarith) (by linarith [hx.1])
    have hlen : (b-x)-(a-x) = b-a := by ring
    rw [hlen] at he
    exact lt_trans he hbudget
  · by_cases hright : b ≤ x
    · have hsum : circleGridAverage x δ T a b = (gridCount δ T (a+1-x) (b+1-x) : ℝ)/T := by
        unfold circleGridAverage
        rw [grid_count_sum]
        congr 1
        exact Finset.sum_congr rfl (fun j hj => chi_rotate_right x _ a b hx (hu j hj) ha hab hright)
      rw [hsum]
      have he := grid_normalized_error δ hδ T hT hcover hover (a+1-x) (b+1-x)
        (by linarith [hx.2]) (by linarith) (by linarith)
      have hlen : (b+1-x)-(a+1-x) = b-a := by ring
      rw [hlen] at he
      exact lt_trans he hbudget
    · have hsum : circleGridAverage x δ T a b =
          (gridCount δ T 0 (b-x) : ℝ)/T + (gridCount δ T (a+1-x) 1 : ℝ)/T := by
        unfold circleGridAverage
        rw [grid_count_sum, grid_count_sum, ← add_div, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl (fun j hj => chi_rotate_split x _ a b hx (hu j hj) ha
          (lt_of_not_ge hleft) (lt_of_not_ge hright) hb)
      rw [hsum]
      have he1 := grid_normalized_error δ hδ T hT hcover hover 0 (b-x)
        le_rfl (by linarith) (by linarith [hx.1])
      have he2 := grid_normalized_error δ hδ T hT hcover hover (a+1-x) 1
        (by linarith [hx.2]) (by linarith) le_rfl
      have hid : (gridCount δ T 0 (b-x) : ℝ)/T + (gridCount δ T (a+1-x) 1 : ℝ)/T - (b-a) =
          ((gridCount δ T 0 (b-x) : ℝ)/T - ((b-x)-0)) +
          ((gridCount δ T (a+1-x) 1 : ℝ)/T - (1-(a+1-x))) := by ring
      rw [hid]
      calc
        _ ≤ |(gridCount δ T 0 (b-x) : ℝ)/T - ((b-x)-0)| +
            |(gridCount δ T (a+1-x) 1 : ℝ)/T - (1-(a+1-x))| := abs_add_le _ _
        _ < 4/(T : ℝ)+2*δ := by rw [hsplit]; linarith

end
end ExternalBridgePressureAnalyticCircleGrid
