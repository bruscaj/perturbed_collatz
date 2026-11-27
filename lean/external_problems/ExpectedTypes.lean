import Definitions

namespace ExternalPrefixSpec

/-- No positivity or slope restriction on L is required for this equivalence. -/
def FloorDepthEquivalence : Prop :=
  ∀ (L K : Profile) (n : Nat), L 0 = 0 →
    (FloorAdmissible L K n ↔ DepthBridge L (DepthOf L K) n)

/-- Integer depth reflection is its own inverse, as an equality of functions. -/
def DepthInvolution : Prop :=
  ∀ (L K : Profile), DepthOf L (DepthOf L K) = K

/-- Unit floor increments ensure that lowering the final letter stays positive. -/
def ClosingFloorEquivalence : Prop :=
  ∀ (L K : Profile) (n : Nat),
    0 < n → (∀ t : Nat, t < n → L t + 1 ≤ L (t + 1)) →
    (ClosingAdmissible L K n ↔ FloorAdmissible L (LowerEndpoint n K) n)

/-- This direction needs no lower bound on increments of L. -/
def FloorRaiseSoundness : Prop :=
  ∀ (L K : Profile) (n : Nat), 0 < n →
    FloorAdmissible L K n → ClosingAdmissible L (RaiseEndpoint n K) n

/-- The endpoint transports are inverse on all profiles. -/
def EndpointInverses : Prop :=
  ∀ (K : Profile) (n : Nat),
    RaiseEndpoint n (LowerEndpoint n K) = K ∧
    LowerEndpoint n (RaiseEndpoint n K) = K

end ExternalPrefixSpec
