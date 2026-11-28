import OptimizationExpectedTypes

/-! Exact arithmetic and natural minimum foundations. No cycle feasibility theorem. -/
namespace ExternalO3OptimizationArithmetic
open ExternalO3OptimizationDraft ExternalO3GeneralDraft
open scoped BigOperators

theorem halving_positive (h : Depth) (M J : ℕ) (e : TruncatedEdge h M J) :
    1 ≤ halvingExponent h M J e := by
  cases e with
  | inl a => simp [halvingExponent]
  | inr p => simp [halvingExponent]

theorem halving_sum_ge_length (h : Depth) (M J : ℕ)
    (c : WalkData (Vertex h M) (TruncatedEdge h M J)) :
    c.length ≤ ∑ i, halvingExponent h M J (c.edge i) := by
  calc
    _ = ∑ _i : Fin c.length, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => halving_positive h M J (c.edge i))

theorem cycle_log_gain (h : Depth) (M J : ℕ)
    (c : WalkData (Vertex h M) (TruncatedEdge h M J)) :
    cycleGain (truncatedGraph h M J) c = (c.length : ℝ) * Real.log 3 -
      ((∑ i, halvingExponent h M J (c.edge i) : ℕ) : ℝ) * Real.log 2 := by
  simp only [cycleGain, truncatedGraph, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Nat.cast_sum]

theorem three_pow_ne_two_pow (t k : ℕ) (hk : 0 < k) : (3 : ℕ) ^ t ≠ 2 ^ k := by
  have ho : Odd ((3 : ℕ) ^ t) := Odd.pow (n := t) (show Odd (3 : ℕ) from ⟨1, by omega⟩)
  have he : Even ((2 : ℕ) ^ k) := (by norm_num : Even (2 : ℕ)).pow_of_ne_zero (Nat.ne_of_gt hk)
  have hn := Nat.not_even_iff_odd.mpr ho
  intro hbad
  rw [hbad] at hn
  exact hn he

theorem log_gain_negative_iff (t k : ℕ) :
    (t : ℝ) * Real.log 3 - (k : ℝ) * Real.log 2 < 0 ↔ (3 : ℕ) ^ t < 2 ^ k := by
  have hh := Real.log_lt_log_iff (by positivity : (0 : ℝ) < ((3 : ℕ) ^ t : ℝ))
    (by positivity : (0 : ℝ) < ((2 : ℕ) ^ k : ℝ))
  simp only [Nat.cast_ofNat, Real.log_pow] at hh
  rw [sub_lt_zero]
  exact hh.trans (by exact_mod_cast (Iff.rfl : (3 : ℕ) ^ t < 2 ^ k ↔ (3 : ℕ) ^ t < 2 ^ k))

theorem natural_cycle_signs : NaturalCycleSigns := by
  intro h M J _hM _hJ c hc
  have hl := halving_sum_ge_length h M J c
  have hk : 0 < ∑ i, halvingExponent h M J (c.edge i) := lt_of_lt_of_le hc.1 hl
  have hs : cycleGain (truncatedGraph h M J) c < 0 ↔
      (3 : ℕ) ^ c.length < 2 ^ (∑ i, halvingExponent h M J (c.edge i)) := by
    rw [cycle_log_gain]
    exact log_gain_negative_iff _ _
  refine ⟨hl, three_pow_ne_two_pow _ _ hk, hs, ?_⟩
  simpa only [not_lt] using not_congr hs

theorem vertex_sum_bound (h : Depth) (M : ℕ) (v : Vertex h M) :
    (∑ i : Fin h.val, ((v i).val + 1)) ≤ h.val * M := by
  calc
    _ ≤ ∑ _i : Fin h.val, M := Finset.sum_le_sum (fun i _ => Nat.succ_le_of_lt (v i).isLt)
    _ = _ := by simp

theorem edge_weight_exponent_bound (h : Depth) (M J : ℕ) (hJ : 2 ≤ J)
    (e : TruncatedEdge h M J) : weightExponent h M J e ≤ commonExponent h M J := by
  cases e with
  | inl a =>
    have hs := vertex_sum_bound h M a.val
    simp only [weightExponent, commonExponent]
    omega
  | inr p =>
    rcases p with ⟨k, v⟩
    have hs := vertex_sum_bound h M v
    have hk := k.isLt
    simp only [weightExponent, commonExponent]
    omega

theorem dyadic_denominator (B E : ℕ) (hE : E ≤ B) :
    1 / ((2 : ℕ) ^ E : ℚ) = ((2 : ℕ) ^ (B - E) : ℚ) / ((2 : ℕ) ^ B : ℚ) := by
  have hp : (2 : ℕ) ^ B = 2 ^ (B - E) * 2 ^ E := by
    rw [← pow_add]
    congr 1
    omega
  have hq : ((2 : ℕ) ^ B : ℚ) = ((2 : ℕ) ^ (B - E) : ℚ) * ((2 : ℕ) ^ E : ℚ) := by
    exact_mod_cast hp
  have he : ((2 : ℕ) ^ E : ℚ) ≠ 0 := by positivity
  have hb : ((2 : ℕ) ^ (B - E) : ℚ) ≠ 0 := by positivity
  rw [hq]
  field_simp

theorem edge_dyadic_denominator (h : Depth) (M J : ℕ) (hJ : 2 ≤ J)
    (e : TruncatedEdge h M J) :
    rationalWeight h M J e =
      ((2 : ℕ) ^ (commonExponent h M J - weightExponent h M J e) : ℚ) /
        ((2 : ℕ) ^ commonExponent h M J : ℚ) :=
  dyadic_denominator _ _ (edge_weight_exponent_bound h M J hJ e)

theorem deletion_dyadic_denominator (h : Depth) (M J : ℕ) (hJ : 2 ≤ J)
    (D : Finset (TruncatedEdge h M J)) :
    deletionCost (truncatedGraph h M J) D =
      (deletionUnits h M J D : ℝ) / ((2 : ℕ) ^ commonExponent h M J : ℝ) := by
  unfold deletionCost deletionUnits
  simp only [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  change (rationalWeight h M J e : ℝ) = _
  have hh : (rationalWeight h M J e : ℝ) =
      ((2 : ℕ) ^ (commonExponent h M J - weightExponent h M J e) : ℝ) /
        ((2 : ℕ) ^ commonExponent h M J : ℝ) := by
    have hq := congrArg (fun q : ℚ => (q : ℝ)) (edge_dyadic_denominator h M J hJ e)
    push_cast at hq
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hq
  simpa only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using hh

theorem common_dyadic_denominator : CommonDyadicDenominator := by
  intro h M J _hM hJ
  exact ⟨fun e => ⟨edge_weight_exponent_bound h M J hJ e,
      edge_dyadic_denominator h M J hJ e⟩,
    fun D => deletion_dyadic_denominator h M J hJ D⟩

theorem delete_all_safe {V E : Type} [Fintype E] (g : FiniteGraph V E) :
    CycleSafe g Finset.univ := by
  classical
  intro c hc hkept
  exact False.elim (hkept ⟨0, hc.1⟩ (Finset.mem_univ _))

theorem numerator_minimum_well_posed : NumeratorMinimumWellPosed := by
  classical
  intro h M J _hM _hJ
  let g := truncatedGraph h M J
  have hall : CycleSafe g Finset.univ := delete_all_safe g
  let S : Set ℕ := {u | ∃ D : Finset (TruncatedEdge h M J),
    CycleSafe g D ∧ u = deletionUnits h M J D}
  have hS : S.Nonempty := ⟨deletionUnits h M J Finset.univ, Finset.univ, hall, rfl⟩
  obtain ⟨D, hD, hmin⟩ := Nat.sInf_mem hS
  refine ⟨⟨Finset.univ, hall⟩, ⟨D, hD, hmin.symm⟩, ?_⟩
  intro A hA
  exact Nat.sInf_le (show deletionUnits h M J A ∈ S from ⟨A, hA, rfl⟩)

end ExternalO3OptimizationArithmetic
