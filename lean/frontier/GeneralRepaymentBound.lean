import RepaymentBound

/-! A generic arithmetic certificate for arbitrary growth blocks followed by
an equal number of J repayments. The finite physical growth-row enumeration
is deliberately NOT an assumption hidden in this module: its exact envelope
is an explicit premise of the principal theorem. -/
namespace FamilyCoverGeneralRepayment
open FamilyCoverRepayment

def growthFactor : Rat := 2187/128
def repaymentFactor : Rat := 3/128
def repaymentFixedPoint : Rat := 3/25
def beta : Rat := 6561/16384

def repaymentEndpoint (k : Nat) (s : Rat) : Rat :=
  repaymentFactor^k*(s-repaymentFixedPoint)+repaymentFixedPoint

theorem factor_power (k : Nat) :
    growthFactor^k*repaymentFactor^k=beta^k := by
  have constant : growthFactor*repaymentFactor=beta := by decide +kernel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Rat.pow_succ growthFactor k,Rat.pow_succ repaymentFactor k,Rat.pow_succ beta k]
    calc
      growthFactor^k*growthFactor*(repaymentFactor^k*repaymentFactor) =
          (growthFactor^k*repaymentFactor^k)*(growthFactor*repaymentFactor) := by grind
      _ = beta^k*beta := by rw [ih,constant]

/-- Any growth block meeting this envelope can repay its entire original-rank
debt with k copies of J. No intermediate growth restriction is imposed here. -/
theorem repayment_from_growth_envelope (k : Nat) (hk : 1 ≤ k)
    (t s : Rat) (ht : 1 ≤ t)
    (envelope : s+1 ≤ growthFactor^k*(t+1)) :
    repaymentEndpoint k s < t := by
  have rpos : 0 ≤ repaymentFactor^k := Rat.pow_nonneg (by decide +kernel)
  have multiplied := Rat.mul_le_mul_of_nonneg_right envelope rpos
  have factors := factor_power k
  have normalization : growthFactor^k*(t+1)*repaymentFactor^k = beta^k*(t+1) := by grind
  rw [normalization] at multiplied
  have nonneg : 0 ≤ repaymentFactor^k*(1+repaymentFixedPoint) :=
    Rat.mul_nonneg rpos (by decide +kernel)
  have exact_upper : repaymentEndpoint k s ≤
      beta^k*(t+1)-repaymentFactor^k*(1+repaymentFixedPoint)+repaymentFixedPoint := by
    have normalization : repaymentEndpoint k s =
        (s+1)*repaymentFactor^k-repaymentFactor^k*(1+repaymentFixedPoint)+repaymentFixedPoint := by
      unfold repaymentEndpoint
      grind
    rw [normalization]
    grind
  have decay : beta^k ≤ beta :=
    pow_le_self beta (by decide +kernel) (by decide +kernel) k hk
  have input_positive : 0 ≤ t+1 := by grind
  have decay_input := Rat.mul_le_mul_of_nonneg_right decay input_positive
  have upper : repaymentEndpoint k s ≤ beta*(t+1)+repaymentFixedPoint := by grind
  have beta_gap : 0 ≤ 1-beta := by decide +kernel
  have input_gap : 0 ≤ t-1 := by grind
  have product := Rat.mul_nonneg beta_gap input_gap
  have margin : 0 < 1-beta*2-repaymentFixedPoint := by decide +kernel
  have identity : t-(beta*(t+1)+repaymentFixedPoint) =
      (1-beta)*(t-1)+(1-beta*2-repaymentFixedPoint) := by grind
  have strictly : beta*(t+1)+repaymentFixedPoint < t := by grind
  grind

/-- The stated exact margin at the smallest source value. -/
theorem margin_at_one :
    1-beta*2-repaymentFixedPoint = (16199/204800:Rat) := by decide +kernel

end FamilyCoverGeneralRepayment

#print axioms FamilyCoverGeneralRepayment.repayment_from_growth_envelope
#print axioms FamilyCoverGeneralRepayment.margin_at_one
