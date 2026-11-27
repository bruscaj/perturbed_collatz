import Collatz.SevenStepCertificate.B1FinalObligation

/-! A whole arithmetic progression outside the current sufficient B1 guards.
This is complement membership only, not a statement of noncapture. -/
namespace Collatz.SevenStepCertificate

private theorem positive_binary_parameter_even (k q : Nat) (hk : 0 < k) :
    (2^k*q) % 2 = 0 := by
  cases k with
  | zero => omega
  | succ k => simp [Nat.pow_succ, Nat.mul_mod]

/-- Every B1 parameter congruent to 19 modulo 128 is outside all five
currently certified guard types. Its capture remains a separate question. -/
theorem b1_residue_19_not_self_certified (t : Nat) (residue : t % 128 = 19) :
    ¬ B1SelfCertified t := by
  intro certified
  rcases certified with ⟨div,k,q,eq,guard⟩ | ⟨div,h,q,eq,terminal⟩ |
    ⟨v,eq⟩ | direct | repayment
  · have properties := b1_guard_properties (k%14) (q%4) guard
    have positive : 0 < k := by omega
    have even := positive_binary_parameter_even k q positive
    rw [← eq] at even
    omega
  · have even := positive_binary_parameter_even (14*h+6) q (by omega)
    rw [← eq] at even
    omega
  · omega
  · unfold B1DirectGuard at direct
    omega
  · have source := b1_repayment_source_residue t repayment
    omega

/-- An explicit infinite progression retained by the final B1 obligation. -/
theorem b1_complement_witness_19 (v : Nat) :
    ¬ B1SelfCertified (128*v+19) :=
  b1_residue_19_not_self_certified (128*v+19) (by omega)

end Collatz.SevenStepCertificate
