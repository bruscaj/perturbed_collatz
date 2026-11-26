import Std

namespace TernaryPump

def geomSum (A : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => geomSum A n + A ^ n

theorem geomSum_add (A t h : Nat) :
    geomSum A (t + h) = geomSum A t + A ^ t * geomSum A h := by
  induction h with
  | zero => simp [geomSum]
  | succ h ih =>
    change geomSum A (t + h) + A ^ (t + h) =
      geomSum A t + A ^ t * (geomSum A h + A ^ h)
    rw [ih, Nat.pow_add, Nat.mul_add, Nat.add_assoc]

theorem geomSum_triple (A h : Nat) :
    geomSum A (h * 3) = geomSum A h * (1 + A ^ h + A ^ h * A ^ h) := by
  have hlen : h * 3 = h + h + h := by omega
  rw [hlen, geomSum_add A (h + h) h, geomSum_add A h h, Nat.pow_add]
  simp only [Nat.mul_add, Nat.mul_one]
  ac_rfl

private theorem pow_mod_three {A : Nat} (hA : A % 3 = 1) (t : Nat) :
    A ^ t % 3 = 1 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Nat.pow_succ, Nat.mul_mod, ih, hA]

private theorem mul_unit_factor {x y : Nat} (hx : x % 3 = 1) (hy : y % 3 = 1) :
    ∃ c, x * y = 1 + 3 * c := by
  have hxy : x * y % 3 = 1 := by rw [Nat.mul_mod, hx, hy]
  exact ⟨x * y / 3, by omega⟩

private theorem triple_unit_factor {x : Nat} (hx : x % 3 = 1) :
    ∃ c, 1 + x + x * x = 3 * (1 + 3 * c) := by
  obtain ⟨b, rfl⟩ : ∃ b, x = 1 + 3 * b := ⟨x / 3, by omega⟩
  have hsq : 3 * b * (3 * b) = 9 * (b * b) := by
    change 3 * b * (3 * b) = (3 * 3) * (b * b)
    ac_rfl
  refine ⟨b + b * b, ?_⟩
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, hsq]
  omega

theorem geomSum_pow_three {A : Nat} (hA : A % 3 = 1) (e : Nat) :
    ∃ c, geomSum A (3 ^ e) = 3 ^ e * (1 + 3 * c) := by
  induction e with
  | zero => exact ⟨0, by simp [geomSum]⟩
  | succ e ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨c, hc⟩ := triple_unit_factor (pow_mod_three hA (3 ^ e))
    obtain ⟨d, hd⟩ := mul_unit_factor (x := 1 + 3 * b) (y := 1 + 3 * c)
      (by omega) (by omega)
    refine ⟨d, ?_⟩
    rw [Nat.pow_succ, geomSum_triple, hb, hc, ← hd]
    ac_rfl

theorem geomSum_add_pow_three {A : Nat} (hA : A % 3 = 1) (t e : Nat) :
    ∃ c, geomSum A (t + 3 ^ e) = geomSum A t + 3 ^ e * (1 + 3 * c) := by
  obtain ⟨b, hb⟩ := geomSum_pow_three hA e
  obtain ⟨c, hc⟩ := mul_unit_factor (y := 1 + 3 * b) (pow_mod_three hA t) (by omega)
  refine ⟨c, ?_⟩
  rw [geomSum_add, hb, ← hc]
  ac_rfl

theorem geomSum_step_mod {A : Nat} (hA : A % 3 = 1) (t e : Nat) :
    (geomSum A (t + 3 ^ e) - geomSum A t) % (3 ^ (e + 1)) = 3 ^ e := by
  obtain ⟨c, hc⟩ := geomSum_add_pow_three hA t e
  have hunit : (1 + 3 * c) % 3 = 1 := by omega
  rw [hc, Nat.add_sub_cancel_left, Nat.pow_succ, Nat.mul_mod_mul_left, hunit, Nat.mul_one]

theorem geomSum_lift {A : Nat} (hA : A % 3 = 1) (e t u : Nat)
    (he : geomSum A t % 3 ^ e = u % 3 ^ e) :
    ∃ digit < 3, geomSum A (t + digit * 3 ^ e) % 3 ^ (e + 1) = u % 3 ^ (e + 1) := by
  let h := 3 ^ e
  let residue := u % h
  let source := geomSum A t / h
  let target := u / h
  have start : geomSum A t = residue + h * source :=
    (Nat.mod_add_div (geomSum A t) h).symm.trans (congrArg (fun rem => rem + h * source) he)
  have advance {index quotient : Nat} (hindex : geomSum A index = residue + h * quotient) :
      ∃ c, geomSum A (index + h) = residue + h * (quotient + 1 + 3 * c) := by
    obtain ⟨c, hc⟩ := geomSum_add_pow_three hA index e
    refine ⟨c, ?_⟩
    calc
      geomSum A (index + h) = geomSum A index + h * (1 + 3 * c) := hc
      _ = _ := by rw [hindex]; simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
  have hit {index quotient : Nat} (hindex : geomSum A index = residue + h * quotient)
      (hdigit : quotient % 3 = target % 3) :
      geomSum A index % 3 ^ (e + 1) = u % 3 ^ (e + 1) := by
    rw [Nat.pow_succ, hindex]
    calc
      (residue + h * quotient) % (h * 3) = (residue + h * target) % (h * 3) := by
        rw [Nat.add_mod residue (h * quotient), Nat.add_mod residue (h * target)]
        simp only [Nat.mul_mod_mul_left, hdigit]
      _ = _ := congrArg (fun value => value % (h * 3)) (Nat.mod_add_div u h)
  by_cases hzero : source % 3 = target % 3
  · exact ⟨0, by decide, by simpa only [Nat.zero_mul, Nat.add_zero] using hit start hzero⟩
  obtain ⟨carry, hnext⟩ := advance start
  by_cases hone : (source + 1 + 3 * carry) % 3 = target % 3
  · exact ⟨1, by decide, by simpa only [Nat.one_mul] using hit hnext hone⟩
  obtain ⟨lastCarry, hlast⟩ := advance hnext
  have htwo : (source + 1 + 3 * carry + 1 + 3 * lastCarry) % 3 = target % 3 := by omega
  exact ⟨2, by decide, by simpa only [Nat.two_mul, Nat.add_assoc] using hit hlast htwo⟩

theorem exists_ge_geomSum_mod {A : Nat} (hA : A % 3 = 1) (e u N : Nat) :
    ∃ t ≥ N, geomSum A t % 3 ^ e = u % 3 ^ e := by
  induction e with
  | zero => exact ⟨N, Nat.le_refl _, by simp only [Nat.pow_zero, Nat.mod_one]⟩
  | succ e ih =>
    obtain ⟨t, hNt, ht⟩ := ih
    obtain ⟨digit, _, hdigit⟩ := geomSum_lift hA e t u ht
    exact ⟨t + digit * 3 ^ e, by omega, hdigit⟩

end TernaryPump