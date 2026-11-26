import Std

namespace SevenStepSprint

/-- Positive-coordinate update, with true selecting a T phase. -/
def forward (isT : Bool) (z : Nat) : Nat :=
  if isT then
    if z % 2 = 0 then z / 2 else (3 * z + 1) / 2
  else
    if z % 2 = 0 then 3 * z / 2 else (z + 1) / 2

/-- The inverse following a forward growing branch requires a ternary guard. -/
def allowed (isT grow : Bool) (z : Nat) : Prop :=
  if grow then
    if isT then z % 3 = 2 else z % 3 = 0
  else True

def predecessor (isT grow : Bool) (z : Nat) : Nat :=
  if grow then
    if isT then (2 * z - 1) / 3 else 2 * z / 3
  else
    if isT then 2 * z else 2 * z - 1

theorem predecessor_positive (isT grow : Bool) (z : Nat)
    (positive : 0 < z) (guard : allowed isT grow z) :
    0 < predecessor isT grow z := by
  cases isT <;> cases grow <;> simp [allowed, predecessor] at * <;> omega

theorem predecessor_replays (isT grow : Bool) (z : Nat)
    (positive : 0 < z) (guard : allowed isT grow z) :
    forward isT (predecessor isT grow z) = z := by
  cases isT <;> cases grow <;> simp [allowed, predecessor, forward] at *
  all_goals split <;> omega

theorem predecessor_bound (isT grow : Bool) (z : Nat) :
    (if grow then 3 else 1) * predecessor isT grow z ≤ 2 * z := by
  cases isT <;> cases grow <;> simp [predecessor] <;> omega

/-- Words are listed in reverse traversal order. -/
def replay : List (Bool × Bool) → Nat → Nat
  | [], z => z
  | (phase, grow) :: rest, z => replay rest (predecessor phase grow z)

def grows : List (Bool × Bool) → Nat
  | [] => 0
  | (_, grow) :: rest => grows rest + if grow then 1 else 0

theorem inverse_word_bound (word : List (Bool × Bool)) (z : Nat) :
    3 ^ grows word * replay word z ≤ 2 ^ word.length * z := by
  induction word generalizing z with
  | nil => simp [grows, replay]
  | cons branch rest ih =>
      obtain ⟨phase, grow⟩ := branch
      have factor : 3 ^ (if grow then 1 else 0 : Nat) = if grow then 3 else 1 := by
        cases grow <;> decide
      simp only [grows, replay, List.length_cons, Nat.pow_add, factor, Nat.pow_succ]
      calc
        (3 ^ grows rest * (if grow then 3 else 1)) *
            replay rest (predecessor phase grow z) =
            (if grow then 3 else 1) *
              (3 ^ grows rest * replay rest (predecessor phase grow z)) := by ac_rfl
        _ ≤ (if grow then 3 else 1) * (2 ^ rest.length * predecessor phase grow z) :=
            Nat.mul_le_mul_left _ (ih _)
        _ = 2 ^ rest.length * ((if grow then 3 else 1) * predecessor phase grow z) := by
            ac_rfl
        _ ≤ 2 ^ rest.length * (2 * z) := Nat.mul_le_mul_left _ (predecessor_bound _ _ _)
        _ = (2 ^ rest.length * 2) * z := by ac_rfl

#print axioms predecessor_positive
#print axioms predecessor_replays
#print axioms inverse_word_bound

end SevenStepSprint
