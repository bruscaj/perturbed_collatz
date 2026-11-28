import GeneralPreimage

/-! Literal finite stride-valuation words, with a terminal remaining-block event. -/
namespace ExternalO3GeneralStrideWords
open ExternalO3Spec ExternalO3Arithmetic ExternalO3Cylinders ExternalO3GeneralPreimage

/-- A finite arithmetic constraint, not a probability law along a trajectory. -/
def StrideWordCell (r : ℕ) : List ℕ → ℕ → Prop
  | [], x => blockLength x = r
  | k :: ks, x => strideValuation x = k ∧ StrideWordCell r ks (stride x)

theorem block_residue_lt (r : ℕ) : 2 ^ (r - 1) - 1 < 2 ^ r := by
  have hp : 0 < 2 ^ (r - 1) := pow_pos (by decide) _
  have hle : 2 ^ (r - 1) ≤ 2 ^ r :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le r 1)
  omega

theorem block_length_residue (r n : ℕ) (hr : 1 ≤ r) :
    blockLength (2 * n + 1) = r ↔ n % 2 ^ r = 2 ^ (r - 1) - 1 := by
  let P := 2 ^ (r - 1)
  have hP : 0 < P := pow_pos (by decide) _
  have hsub : P - 1 + 1 = P := by omega
  have hR : 2 ^ r = 2 * P := by
    have hh := pow_succ (2 : ℕ) (r - 1)
    rw [Nat.sub_add_cancel hr] at hh
    simpa [P, Nat.mul_comm] using hh
  constructor
  · intro h
    obtain ⟨q, hq⟩ := (valuation_odd_form ((2 * n + 1) + 1) r (by omega)).mp h
    have hn : n = P - 1 + 2 ^ r * q := by rw [hR] at hq ⊢; nlinarith
    rw [hn, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (block_residue_lt r)
  · intro h
    let q := n / 2 ^ r
    have hn : n = P - 1 + 2 ^ r * q := by
      have hh := Nat.mod_add_div n (2 ^ r)
      rw [h] at hh
      exact hh.symm
    apply (valuation_odd_form _ _ (by omega)).mpr
    refine ⟨q, ?_⟩
    rw [hn, hR]
    nlinarith

/-- Every positive finite word, with its terminal block constraint, is one class. -/
theorem stride_word_unique_class (ks : List ℕ) (r : ℕ)
    (hk : ∀ k ∈ ks, 1 ≤ k) (hr : 1 ≤ r) :
    ∃! d : ℕ, d < 2 ^ (ks.sum + r) ∧ ∀ n : ℕ,
      StrideWordCell r ks (2 * n + 1) ↔ n % 2 ^ (ks.sum + r) = d := by
  induction ks with
  | nil =>
    refine ⟨2 ^ (r - 1) - 1, ?_, ?_⟩
    · exact ⟨by simpa using block_residue_lt r, fun n => by simpa [StrideWordCell] using block_length_residue r n hr⟩
    · rintro d ⟨hd, hevent⟩
      have hb := (block_length_residue r d hr).mp ((hevent d).mpr (by simpa using Nat.mod_eq_of_lt hd))
      simpa [Nat.mod_eq_of_lt (by simpa using hd : d < 2 ^ r)] using hb
  | cons k ks ih =>
    obtain ⟨d, ⟨hd, hevent⟩, _⟩ := ih (fun j hj => hk j (by simp [hj]))
    obtain ⟨c, ⟨hc, hpre⟩, _⟩ := stride_preimage_unique_class k (ks.sum + r) d
      (hk k (by simp)) hd
    have he : ∀ n : ℕ, StrideWordCell r (k :: ks) (2 * n + 1) ↔
        n % 2 ^ (k + (ks.sum + r)) = c := by
      intro n
      rw [← hpre n]
      constructor
      · rintro ⟨hv, ht⟩
        let y := stride (2 * n + 1)
        have hy : y = 2 * (y / 2) + 1 := by
          have ho := (stride_output (2 * n + 1)).2
          have hm := Nat.mod_add_div y 2
          change y % 2 = 1 at ho
          omega
        refine ⟨y / 2, hv, hy, ?_⟩
        apply (hevent (y / 2)).mp
        simpa only [← hy] using ht
      · rintro ⟨m, hv, hs, hm⟩
        refine ⟨hv, ?_⟩
        rw [hs]
        exact (hevent m).mpr hm
    refine ⟨c, ?_, ?_⟩
    · exact ⟨by simpa [List.sum_cons, Nat.add_assoc] using hc,
        fun n => by simpa [List.sum_cons, Nat.add_assoc] using he n⟩
    · rintro c' ⟨hc', he'⟩
      have hh := (he c').mp ((he' c').mpr (Nat.mod_eq_of_lt hc'))
      have hc'' : c' < 2 ^ (k + (ks.sum + r)) := by
        simpa [List.sum_cons, Nat.add_assoc] using hc'
      simpa only [Nat.mod_eq_of_lt hc''] using hh

end ExternalO3GeneralStrideWords
