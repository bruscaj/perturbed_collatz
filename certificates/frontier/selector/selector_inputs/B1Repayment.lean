import Collatz.SevenStepCertificate.B1RepaymentPrimitive
import Collatz.SevenStepCertificate.FrontierIdentities
import Collatz.SevenStepCertificate.B1SelfReturns
import Collatz.SevenStepCertificate.B1RepaymentArithmetic

/-! Arbitrarily many expanding B1 laps followed by arbitrarily many shadow
mergers. The second stage repays the expansion relative to the original
B1 parameter; no capture premise on the larger intermediate launch is used. -/
namespace Collatz.SevenStepCertificate

theorem b1_growth_history (h t T q : Nat)
    (source : 601*t+151 = 128^h*q) (target : 601*T+151 = 729^h*q) :
    run (.p1,6*t) (7*h) = (.p1,6*T) := by
  induction h generalizing t q with
  | zero =>
    simp only [Nat.pow_zero,Nat.one_mul] at source target
    have same : t = T := by omega
    rw [same]
    rfl
  | succ h ih =>
    have source' : 601*t+151 = 128*(128^h*q) := by
      rw [Nat.pow_succ] at source
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using source
    have residue : t % 128 = 17 := by omega
    have expand : t = 128*(t/128)+17 := by omega
    let v := t/128
    let nextT := 729*v+98
    have lower : 128^h*q = 601*v+81 := by dsimp [v]; omega
    have next_source : 601*nextT+151 = 128^h*(729*q) := by
      have reorder : 128^h*(729*q) = 729*(128^h*q) := by ac_rfl
      rw [reorder,lower]
      dsimp [nextT]
      omega
    have next_target : 601*T+151 = 729^h*(729*q) := by
      rw [Nat.pow_succ] at target
      simpa only [Nat.mul_assoc] using target
    have lap : run (.p1,6*t) 7 = (.p1,6*nextT) := by
      rw [expand]
      exact b1_growth_lap v
    rw [show 7*(h+1) = 7+7*h by omega,run_add,lap]
    exact ih nextT (729*q) next_source next_target

theorem b1_shadow_history (h r : Nat) :
    run (.p1,6*(1+131072*128^h*r)) (18+7*h) =
      run (.p1,6*(1+131072*9^h*r)) 18 := by
  induction h generalizing r with
  | zero => rfl
  | succ h ih =>
    have pow128 : 128^(h+1)*r = 128*(128^h*r) := by rw [Nat.pow_succ]; ac_rfl
    have source : 6*(1+131072*128^(h+1)*r) = 3*(33554432*(128^h*r)+2) := by
      have reorder : 131072*128^(h+1)*r = 131072*(128^(h+1)*r) := by ac_rfl
      rw [reorder,pow128]
      omega
    have alternate : 3*(2359296*(128^h*r)+2) = 6*(1+131072*128^h*(9*r)) := by
      have reorder : 131072*128^h*(9*r) = 1179648*(128^h*r) := by
        calc
          131072*128^h*(9*r) = (131072*9)*(128^h*r) := by ac_rfl
          _ = 1179648*(128^h*r) := rfl
      rw [reorder]
      omega
    have final : 6*(1+131072*9^h*(9*r)) = 6*(1+131072*9^(h+1)*r) := by
      rw [Nat.pow_succ]
      simp only [Nat.mul_assoc]
    rw [show 18+7*(h+1) = 25+7*h by omega,
        run_add (.p1,6*(1+131072*128^(h+1)*r)) 25 (7*h),source,
        b1_shadow_merger,alternate,
        ← run_add (.p1,6*(1+131072*128^h*(9*r))) 18 (7*h),ih,final]

theorem b1_repayment_merger (h t q r : Nat)
    (source : 601*t+151 = 128^h*q)
    (terminal : 729^h*q = 601*(1+131072*128^h*r)+151) :
    run (.p1,6*t) (14*h+18) = run (.p1,6*(1+131072*9^h*r)) 18 := by
  have growth := b1_growth_history h t (1+131072*128^h*r) q source terminal.symm
  rw [show 14*h+18 = 7*h+(18+7*h) by omega,run_add,growth]
  exact b1_shadow_history h r

/-- A nonempty CRT family at every positive pump depth. All hypotheses are
explicit integer equations; strict descent is proved, not assumed. -/
def B1RepaymentGuard (t : Nat) : Prop :=
  ∃ h q r, 0 < h ∧ 0 < r ∧ 601*t+151 = 128^h*q ∧
    729^h*q = 601*(1+131072*128^h*r)+151

theorem b1_repayment_self_progress (t : Nat) (guard : B1RepaymentGuard t) :
    B1SelfProgress t := by
  obtain ⟨h,q,r,hh,hr,source,terminal⟩ := guard
  right
  exact ⟨1+131072*9^h*r,14*h+18,18,by omega,
    b1_repayment_strict_parameter_drop h q r t hh hr source terminal,
    b1_repayment_merger h t q r source terminal⟩

theorem b1_repayment_source_residue (t : Nat) (guard : B1RepaymentGuard t) :
    t % 128 = 17 := by
  obtain ⟨h,q,r,hh,hr,source,terminal⟩ := guard
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  subst h
  rw [Nat.pow_succ] at source
  have fact : 128^k*128*q = 128*(128^k*q) := by ac_rfl
  rw [fact] at source
  omega

end Collatz.SevenStepCertificate
