import Std

/-!
Frozen supporting definitions. These are abstract integer prefix models.
No real slope, logarithm, rung predicate, pressure, density, or limit occurs.
-/
namespace ExternalPrefixSpec

abbrev Profile := Nat → Int

/-- Cumulative positive-integer letters, with a floor endpoint and cap. -/
def FloorAdmissible (L K : Profile) (n : Nat) : Prop :=
  K 0 = 0 ∧
  K n = L n ∧
  (∀ t : Nat, t < n → K t + 1 ≤ K (t + 1)) ∧
  (∀ t : Nat, t ≤ n → K t ≤ L t)

/-- A depth profile starting and ending at zero, with the exact step cap. -/
def DepthBridge (L J : Profile) (n : Nat) : Prop :=
  J 0 = 0 ∧
  J n = 0 ∧
  (∀ t : Nat, t ≤ n → 0 ≤ J t) ∧
  (∀ t : Nat, t < n →
    J (t + 1) ≤ J t + L (t + 1) - L t - 1)

def DepthOf (L K : Profile) : Profile := fun t => L t - K t

/-- Closing endpoint is one above the floor, with only interior caps. -/
def ClosingAdmissible (L K : Profile) (n : Nat) : Prop :=
  K 0 = 0 ∧
  K n = L n + 1 ∧
  (∀ t : Nat, t < n → K t + 1 ≤ K (t + 1)) ∧
  (∀ t : Nat, t < n → K t ≤ L t)

/-- Change just the closing endpoint; values after n are also unchanged. -/
def LowerEndpoint (n : Nat) (K : Profile) : Profile :=
  fun t => if t = n then K t - 1 else K t

def RaiseEndpoint (n : Nat) (K : Profile) : Profile :=
  fun t => if t = n then K t + 1 else K t

end ExternalPrefixSpec
