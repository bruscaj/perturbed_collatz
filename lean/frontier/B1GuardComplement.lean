import Std

/-!
Guard-only audit, independent of capture claims. Definitions are extracted
verbatim from the local unmerged B1FinalObligation continuation; hashes and
source text are in source_manifest.json and snapshot/. This file does NOT
assert that the five guards are capture or descent certificates. It proves
noncoverage properties of their explicit arithmetic disjunction.
-/
namespace GuardAudit

def B1ElementaryGuard (r c : Nat) : Prop :=
  (r = 1 ∧ c = 1) ∨ (r = 2 ∧ c = 3) ∨ (r = 4 ∧ c = 1) ∨
  (r = 5 ∧ c = 3) ∨ (r = 6 ∧ c = 1) ∨ (r = 8 ∧ c = 3) ∨
  (r = 9 ∧ c = 1) ∨ (r = 11 ∧ c = 3) ∨ (r = 12 ∧ c = 1) ∨
  (r = 13 ∧ c = 3)

def B1DirectGuard (t : Nat) : Prop :=
  t % 128 = 9 ∨ t % 128 = 11 ∨ t % 128 = 12 ∨ t % 128 = 13 ∨
  t % 128 = 25 ∨ t % 128 = 27 ∨ t % 128 = 28 ∨ t % 128 = 31 ∨
  t % 128 = 36 ∨ t % 128 = 45 ∨ t % 128 = 47 ∨ t % 128 = 51 ∨
  t % 128 = 52 ∨ t % 128 = 55 ∨ t % 128 = 61 ∨ t % 128 = 66 ∨
  t % 128 = 69 ∨ t % 128 = 71 ∨ t % 128 = 82 ∨ t % 128 = 83 ∨
  t % 128 = 85 ∨ t % 128 = 99 ∨ t % 128 = 104 ∨ t % 128 = 107 ∨
  t % 128 = 108 ∨ t % 128 = 120 ∨ t % 128 = 123 ∨ t % 128 = 127

def B1RepaymentGuard (t : Nat) : Prop :=
  ∃ h q r, 0 < h ∧ 0 < r ∧ 601*t+151 = 128^h*q ∧
    729^h*q = 601*(1+131072*128^h*r)+151

def B1SelfCertified (t : Nat) : Prop :=
  (t % 3 = 0 ∧ ∃ k q, t = 2^k*q ∧ B1ElementaryGuard (k%14) (q%4)) ∨
  (t % 3 = 0 ∧ ∃ h q, t = 2^(14*h+6)*q ∧ (59049^h*q) % 32 = 15) ∨
  (∃ v, t = 16777216*v+1) ∨ B1DirectGuard t ∨ B1RepaymentGuard t

theorem odd_power_exponent_zero (t k q : Nat) (odd : t % 2 = 1)
    (eq : t = 2^k*q) : k = 0 := by
  cases k with
  | zero => rfl
  | succ j =>
    have factor : 2^(j+1)*q = 2*(2^j*q) := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [factor] at eq
    omega

theorem repayment_residue (t : Nat) (guard : B1RepaymentGuard t) :
    t % 128 = 17 := by
  obtain ⟨h,q,r,hh,_,source,_⟩ := guard
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  subst h
  rw [Nat.pow_succ] at source
  have fact : 128^k*128*q = 128*(128^k*q) := by ac_rfl
  rw [fact] at source
  omega

theorem rejected_odd (t : Nat) (odd : t % 2 = 1)
    (not_shadow : t % 128 ≠ 1) (not_repay : t % 128 ≠ 17)
    (not_direct : ¬ B1DirectGuard t) : ¬ B1SelfCertified t := by
  intro guard
  rcases guard with ⟨_,k,q,eq,hg⟩ | ⟨_,h,q,eq,_⟩ | ⟨v,eq⟩ | hd | hr
  · have hk := odd_power_exponent_zero t k q odd eq
    subst k
    unfold B1ElementaryGuard at hg
    omega
  · have impossible := odd_power_exponent_zero t (14*h+6) q odd eq
    omega
  · omega
  · exact not_direct hd
  · exact not_repay (repayment_residue t hr)

def RejectedOddResidue (r : Nat) : Prop :=
  r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 15 ∨ r = 19 ∨ r = 21 ∨ r = 23 ∨
  r = 29 ∨ r = 33 ∨ r = 35 ∨ r = 37 ∨ r = 39 ∨ r = 41 ∨ r = 43 ∨
  r = 49 ∨ r = 53 ∨ r = 57 ∨ r = 59 ∨ r = 63 ∨ r = 65 ∨ r = 67 ∨
  r = 73 ∨ r = 75 ∨ r = 77 ∨ r = 79 ∨ r = 81 ∨ r = 87 ∨ r = 89 ∨
  r = 91 ∨ r = 93 ∨ r = 95 ∨ r = 97 ∨ r = 101 ∨ r = 103 ∨
  r = 105 ∨ r = 109 ∨ r = 111 ∨ r = 113 ∨ r = 115 ∨ r = 117 ∨
  r = 119 ∨ r = 121 ∨ r = 125

theorem forty_three_whole_cylinders (v r : Nat) (hr : RejectedOddResidue r) :
    ¬ B1SelfCertified (128*v+r) := by
  apply rejected_odd
  · unfold RejectedOddResidue at hr
    omega
  · unfold RejectedOddResidue at hr
    omega
  · unfold RejectedOddResidue at hr
    omega
  · unfold RejectedOddResidue at hr
    unfold B1DirectGuard
    omega

theorem nineteen_cylinder_rejected (v : Nat) : ¬ B1SelfCertified (128*v+19) := by
  apply forty_three_whole_cylinders
  unfold RejectedOddResidue
  omega

theorem two_rejected : ¬ B1SelfCertified 2 := by
  intro guard
  rcases guard with ⟨d,_⟩ | ⟨d,_⟩ | ⟨v,eq⟩ | hd | hr
  · omega
  · omega
  · omega
  · unfold B1DirectGuard at hd
    omega
  · have impossible := repayment_residue 2 hr
    omega

theorem one_accepted : B1SelfCertified 1 := by
  exact Or.inr (Or.inr (Or.inl ⟨0, rfl⟩))

theorem smallest_rejected_positive :
    ¬ B1SelfCertified 2 ∧ ∀ t, 0 < t → t < 2 → B1SelfCertified t := by
  constructor
  · exact two_rejected
  · intro t ht hlt
    have eq : t = 1 := by omega
    simpa [eq] using one_accepted

#print axioms forty_three_whole_cylinders
#print axioms smallest_rejected_positive
end GuardAudit
