import Mathlib.Data.Nat.Count
import Mathlib.Analysis.SpecificLimits.Basic

/-! Literal residue-class counts and natural-density limits. No density law is assumed. -/
namespace ExternalO3Progressions
open Filter
open scoped Topology BigOperators

/-- Literal number of representatives below N in one residue class. -/
def residueCount (m a N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => n % m = a)).card

theorem residueCount_small (m a r : ℕ) (hr : r ≤ m) :
    residueCount m a r = if a < r then 1 else 0 := by
  unfold residueCount
  have heq : (Finset.range r).filter (fun n => n % m = a) =
      (Finset.range r).filter (fun n => n = a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, ha⟩
      exact ⟨hn, by simpa [Nat.mod_eq_of_lt (lt_of_lt_of_le hn hr)] using ha⟩
    · rintro ⟨hn, rfl⟩
      exact ⟨hn, Nat.mod_eq_of_lt (lt_of_lt_of_le hn hr)⟩
  rw [heq]
  by_cases h : a < r <;> simp [h]

theorem residueCount_blocks (m a q : ℕ) (ha : a < m) :
    residueCount m a (q * m) = q := by
  unfold residueCount
  rw [← Nat.count_eq_card_filter_range]
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add, ih]
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
    have hc : Nat.count (fun k => k % m = a) m = 1 := by
      rw [Nat.count_eq_card_filter_range]
      change residueCount m a m = 1
      simp [residueCount_small, ha]
    rw [hc]

theorem residueCount_exact (m a N : ℕ) (hm : 0 < m) (ha : a < m) :
    residueCount m a N = N / m + if a < N % m then 1 else 0 := by
  have hN : N = (N / m) * m + N % m := by simpa [Nat.mul_comm] using (Nat.div_add_mod N m).symm
  conv_lhs => rw [hN]
  unfold residueCount
  rw [← Nat.count_eq_card_filter_range]
  rw [Nat.count_add]
  have hb : Nat.count (fun n => n % m = a) (N / m * m) = N / m :=
    by
      rw [Nat.count_eq_card_filter_range]
      exact residueCount_blocks m a (N / m) ha
  rw [hb]
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
  congr 1
  rw [Nat.count_eq_card_filter_range]
  exact residueCount_small m a (N % m) (Nat.le_of_lt (Nat.mod_lt N hm))

/-- The scaled discrepancy from the uniform count is bounded independently of N. -/
theorem residueCount_scaled_error (m a N : ℕ) (hm : 0 < m) (ha : a < m) :
    -(m : ℝ) ≤ (m : ℝ) * (residueCount m a N : ℝ) - (N : ℝ) ∧
    (m : ℝ) * (residueCount m a N : ℝ) - (N : ℝ) ≤ (m : ℝ) := by
  have hrel : (m : ℝ) * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N m
  have hr0 : (0 : ℝ) ≤ ((N % m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr1 : ((N % m : ℕ) : ℝ) < (m : ℝ) := Nat.cast_lt.mpr (Nat.mod_lt N hm)
  rw [residueCount_exact m a N hm ha]
  by_cases h : a < N % m
  · rw [ite_eq_left h, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith
  · rw [ite_eq_right h, Nat.add_zero]
    constructor <;> nlinarith

/-- Natural density of an actual residue class in the first N naturals. -/
theorem residueClass_density (m a : ℕ) (hm : 0 < m) (ha : a < m) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => n % m = a)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (m : ℝ))) := by
  let error : ℕ → ℝ := fun N => (m : ℝ) * (residueCount m a N : ℝ) - (N : ℝ)
  have herror : Tendsto (fun N : ℕ => error N / (N : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (Eventually.of_forall (fun N => (residueCount_scaled_error m a N hm ha).1))
      (Eventually.of_forall (fun N => (residueCount_scaled_error m a N hm ha).2))
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => 1 / (m : ℝ) + (error N / (N : ℝ)) / (m : ℝ))
      atTop (𝓝 (1 / (m : ℝ))) := by
    simpa using tendsto_const_nhds.add (herror.div_const (m : ℝ))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hmn : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hNn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  change 1 / (m : ℝ) +
    (((m : ℝ) * (residueCount m a N : ℝ) - (N : ℝ)) / (N : ℝ)) / (m : ℝ) =
      (residueCount m a N : ℝ) / (N : ℝ)
  field_simp
  ring

/-- In particular, the literal density of a dyadic class is 2^(-k). -/
theorem dyadicClass_density (k a : ℕ) (ha : a < 2 ^ k) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => n % (2 ^ k) = a)).card : ℝ) / (N : ℝ))
      atTop (𝓝 (1 / (2 : ℝ) ^ k)) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    residueClass_density (2 ^ k) a (by positivity) ha

/-- A finite union of distinct classes has the sum of their literal counts. -/
theorem residueUnion_count (m N : ℕ) (A : Finset ℕ) :
    ((Finset.range N).filter (fun n => n % m ∈ A)).card =
      ∑ a ∈ A, residueCount m a N := by
  exact (Finset.sum_card_fiberwise_eq_card_filter (Finset.range N) A (fun n => n % m)).symm

/-- Literal natural density of a finite union of distinct residue classes. -/
theorem residueUnion_density (m : ℕ) (A : Finset ℕ) (hm : 0 < m)
    (hA : ∀ a ∈ A, a < m) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => n % m ∈ A)).card : ℝ) / (N : ℝ))
      atTop (𝓝 ((A.card : ℝ) / (m : ℝ))) := by
  have hs := tendsto_finsetSum A (fun a ha => residueClass_density m a hm (hA a ha))
  simpa [residueUnion_count, residueCount, Nat.cast_sum, div_eq_mul_inv,
    Finset.sum_mul] using hs

/-- Finite seed sets have zero literal natural density. -/
theorem finiteSet_density (E : Finset ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => n ∈ E)).card : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := (E.card : ℝ))
    (Eventually.of_forall (fun N => Nat.cast_nonneg _))
    (Eventually.of_forall (fun N => ?_)) tendsto_natCast_atTop_atTop
  exact Nat.cast_le.mpr (Finset.card_le_card (by
    intro n hn
    exact (Finset.mem_filter.mp hn).2))

/-- Agreement outside a fixed finite prefix preserves the literal density limit. -/
theorem density_congr_after (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (B : ℕ) (hagree : ∀ n, B ≤ n → (p n ↔ q n)) (d : ℝ)
    (hp : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter p).card : ℝ) / (N : ℝ)) atTop (𝓝 d)) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter q).card : ℝ) / (N : ℝ)) atTop (𝓝 d) := by
  let C : ℝ := (Nat.count q B : ℝ) - (Nat.count p B : ℝ)
  have hlim : Tendsto (fun N : ℕ =>
      (((Finset.range N).filter p).card : ℝ) / (N : ℝ) + C / (N : ℝ))
      atTop (𝓝 d) := by
    simpa using hp.add (tendsto_const_div_atTop_nhds_zero_nat C)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop B] with N hN
  have hshift : (fun k => p (B + k)) = (fun k => q (B + k)) := by
    funext k
    exact propext (hagree (B + k) (by omega))
  have hcount : Nat.count p N + Nat.count q B = Nat.count q N + Nat.count p B := by
    have hNB : N = B + (N - B) := by omega
    conv_lhs => lhs; rw [hNB, Nat.count_add]
    conv_rhs => lhs; rw [hNB, Nat.count_add]
    simp only [hshift]
    omega
  have hreal : (Nat.count p N : ℝ) + (Nat.count q B : ℝ) =
      (Nat.count q N : ℝ) + (Nat.count p B : ℝ) := by exact_mod_cast hcount
  have hdiff : (Nat.count q N : ℝ) = (Nat.count p N : ℝ) + C := by
    dsimp [C]
    linarith
  simp only [← Nat.count_eq_card_filter_range]
  rw [hdiff, add_div]

end ExternalO3Progressions
