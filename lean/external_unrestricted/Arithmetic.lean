import ExpectedTypes
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Initial arithmetic implementation against the literal O3 source definitions.
This does not prove density existence, the infimum formula, or nonattainment.
-/
namespace ExternalO3Arithmetic
open ExternalO3Spec

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem stride_output (x : ℕ) : IsOddSeed (stride x) := by
  have hd : 2 ^ strideValuation x ∣ 3 * x + 1 := pow_padicValNat_dvd
  have hnum : 0 < 3 * x + 1 := by omega
  have hden : 0 < 2 ^ strideValuation x := pow_pos (by decide) _
  have hpos : 0 < stride x := Nat.div_pos (Nat.le_of_dvd hnum hd) hden
  have hval : padicValNat 2 (stride x) = 0 := by
    dsimp [stride]
    rw [padicValNat.div_pow hd]
    simp [strideValuation]
  have hnot : ¬2 ∣ stride x := by
    rcases padicValNat.eq_zero_iff.mp hval with h | h | h
    · omega
    · omega
    · exact h
  have hmod : stride x % 2 ≠ 0 := by
    intro hz
    exact hnot (Nat.dvd_of_mod_eq_zero hz)
  exact ⟨hpos, by omega⟩

theorem valuation_foundation : ValuationFoundation := by
  intro x hx
  have hnum : 3 * x + 1 ≠ 0 := by omega
  have hdiv : 2 ∣ 3 * x + 1 := Nat.dvd_of_mod_eq_zero (by
    have := hx.2
    omega)
  have hval : 0 < strideValuation x :=
    one_le_padicValNat_of_dvd hnum hdiv
  exact ⟨hval, pow_padicValNat_dvd,
    pow_succ_padicValNat_not_dvd hnum, stride_output x⟩

theorem block_length_positive (x : ℕ) (hx : IsOddSeed x) :
    0 < blockLength x := by
  have hd : 2 ∣ x + 1 := Nat.dvd_of_mod_eq_zero (by
    have := hx.2
    omega)
  exact one_le_padicValNat_of_dvd (by omega) hd

theorem valuation_one_of_long_block (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) : strideValuation x = 1 := by
  have hfour : 4 ∣ x + 1 := by
    have h := (padicValNat_dvd_iff_le (p := 2) (by omega : x + 1 ≠ 0)).mpr hr
    simpa using h
  have hm : (x + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hfour
  have hnot : ¬4 ∣ 3 * x + 1 := by
    intro hd
    have hn := Nat.mod_eq_zero_of_dvd hd
    omega
  have hp := (valuation_foundation x hx).1
  have hlt : strideValuation x < 2 := by
    by_contra hn
    have hd := (padicValNat_dvd_iff_le (p := 2)
      (by omega : 3 * x + 1 ≠ 0)).mpr (show 2 ≤ strideValuation x by omega)
    exact hnot (by simpa using hd)
  omega

theorem block_decrements (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) : blockLength (stride x) + 1 = blockLength x := by
  have hk := valuation_one_of_long_block x hx hr
  have hrelation : 2 * (stride x + 1) = 3 * (x + 1) := by
    simp only [stride, hk, pow_one]
    have := hx.2
    omega
  have hthree : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  change padicValNat 2 (stride x + 1) + 1 = padicValNat 2 (x + 1)
  calc
    padicValNat 2 (stride x + 1) + 1 =
        padicValNat 2 (2 * (stride x + 1)) := by
      rw [padicValNat.mul (by decide) (by omega)]
      simp [Nat.add_comm]
    _ = padicValNat 2 (3 * (x + 1)) := congrArg (padicValNat 2) hrelation
    _ = padicValNat 2 (x + 1) := by
      rw [padicValNat.mul (by decide) (by omega), hthree, Nat.zero_add]

theorem exit_valuation_of_short_block (x : ℕ) (hx : IsOddSeed x)
    (hr : blockLength x = 1) : 2 ≤ strideValuation x := by
  have hnot : ¬4 ∣ x + 1 := by
    have h := pow_succ_padicValNat_not_dvd (p := 2) (by omega : x + 1 ≠ 0)
    change ¬2 ^ (blockLength x + 1) ∣ x + 1 at h
    simpa [hr] using h
  have hm : (x + 1) % 4 ≠ 0 := by
    intro hz
    exact hnot (Nat.dvd_of_mod_eq_zero hz)
  have hd : 4 ∣ 3 * x + 1 := Nat.dvd_of_mod_eq_zero (by
    have := hx.2
    omega)
  exact (padicValNat_dvd_iff_le (p := 2) (by omega : 3 * x + 1 ≠ 0)).mp hd

theorem block_after_steps (x : ℕ) (hx : IsOddSeed x) :
    ∀ i : ℕ, i < blockLength x →
      IsOddSeed ((Nat.iterate stride i) x) ∧
      blockLength ((Nat.iterate stride i) x) + i = blockLength x := by
  intro i
  induction i with
  | zero =>
    intro _
    simpa using And.intro hx (rfl : blockLength x = blockLength x)
  | succ i ih =>
    intro hi
    have hs := ih (by omega)
    have hlong : 2 ≤ blockLength ((Nat.iterate stride i) x) := by omega
    have hdec := block_decrements _ hs.1 hlong
    simp only [Function.iterate_succ_apply']
    exact ⟨stride_output _, by omega⟩

theorem block_length_law : BlockLengthLaw := by
  intro x hx
  have hpos := block_length_positive x hx
  refine ⟨hpos, ?_, ?_⟩
  · intro i hi
    have hs := block_after_steps x hx i (by omega)
    exact valuation_one_of_long_block _ hs.1 (by omega)
  · have hs := block_after_steps x hx (blockLength x - 1) (by omega)
    have hlen : blockLength ((Nat.iterate stride (blockLength x - 1)) x) = 1 := by
      omega
    exact exit_valuation_of_short_block _ hs.1 hlen

theorem fixed_point_convention : FixedPointConvention := by
  have hfour : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2 ^ 2) = 2
    exact padicValNat.prime_pow 2
  constructor
  · simp [stride, strideValuation, hfour]
  · simp [blockLength]

theorem correction_zero_irrelevant : CorrectionZeroIrrelevant := by
  intro φ ψ hagree x hx
  have hcur := hagree (blockLength x) (block_length_positive x hx)
  have hnext := hagree (blockLength (stride x))
    (block_length_positive (stride x) (stride_output x))
  simp only [FailsAt, rawPotential, hcur, hnext]

end ExternalO3Arithmetic
