import Std

namespace SevenStepSprint

def c51 (m : Nat) : Nat := (81*m+93)/128
def c33 (m : Nat) : Nat := (3*m+29)/128
def v (m : Nat) : Nat := (729*m+32)/128
def packetStart (u : Nat) : Nat := 2097152*u+1572915

/-- The contracting packet has the same entire image as the growing V macro. -/
theorem packet_guard_and_image (u : Nat) :
    let start := packetStart u
    start % 128 = 51 ∧
    c51 start % 128 = 33 ∧
    c33 (c51 start) % 128 = 33 ∧
    (128*u+96) % 128 = 96 ∧
    c33 (c33 (c51 start)) = v (128*u+96) ∧
    v (128*u+96) = 729*u+547 := by
  simp only [packetStart, c51, c33, v]
  repeat' constructor <;> omega

#print axioms packet_guard_and_image

end SevenStepSprint
