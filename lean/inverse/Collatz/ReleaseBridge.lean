import Collatz.SevenFrontier

namespace Collatz.ReleaseBridge
open Collatz.SevenStep

/- Release-only bridge, not copied from the research snapshot.
   The upstream theorem proves the difficult implication. The converse uses
   only that each of the three family launches has positive physical value.
   Both sides use the same signed dynamics, phase convention, and target cycle. -/
theorem global_capture_iff_three :
    (∀ (i : Phase) (n : Int), 0 < n → Captured (i,n)) ↔
      (∀ t : Nat, 0 < t → Captured (site 1 (2*t))) ∧
      (∀ t : Nat, Captured (site 3 (4*t+3))) ∧
      (∀ t : Nat, Captured (site 5 (8*t+2))) := by
  constructor
  · intro all
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      change Captured (1, 3*((2*t : Nat) : Int)-1+height 1)
      apply all
      have h : height 1 = 0 := by decide
      rw [h]
      omega
    · intro t
      change Captured (3, 3*((4*t+3 : Nat) : Int)-1+height 3)
      apply all
      have h : height 3 = 1 := by decide
      rw [h]
      omega
    · intro t
      change Captured (5, 3*((8*t+2 : Nat) : Int)-1+height 5)
      apply all
      have h : height 5 = 0 := by decide
      rw [h]
      omega
  · rintro ⟨B1, A3, N03⟩ i n positive
    exact global_capture_of_three B1 A3 N03 i n positive

end Collatz.ReleaseBridge
