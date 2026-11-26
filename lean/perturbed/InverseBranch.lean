import Lean

namespace InverseBranch

def height : Bool → Int
  | false => 0
  | true => 1

def collatz (value : Int) : Int :=
  if value % 2 = 0 then value / 2 else (3 * value + 1) / 2

def forward (bit : Bool) (value : Int) : Int :=
  collatz (value + height bit) - height bit

def evenParent (bit : Bool) (target : Int) : Int := 2 * target + height bit

def oddParent (bit : Bool) (target : Int) : Int := (2 * target - 1 - height bit) / 3

def Gate (bit : Bool) (target : Int) : Prop := (target + height bit) % 3 = 2

private theorem height_bounds (bit : Bool) : 0 ≤ height bit ∧ height bit ≤ 1 := by
  cases bit <;> decide

theorem even_nonneg (bit : Bool) (target : Int) (nonneg : 0 ≤ target) :
    0 ≤ evenParent bit target := by
  have bounds := height_bounds bit
  unfold evenParent
  omega

theorem even_spec (bit : Bool) (target : Int) :
    (evenParent bit target + height bit) % 2 = 0 ∧ forward bit (evenParent bit target) = target := by
  have parity : (evenParent bit target + height bit) % 2 = 0 := by unfold evenParent; omega
  refine ⟨parity, ?_⟩
  unfold forward collatz
  rw [if_pos parity]
  unfold evenParent
  omega

theorem odd_spec (bit : Bool) (target : Int) (nonneg : 0 ≤ target) (gate : Gate bit target) :
    0 ≤ oddParent bit target ∧ (oddParent bit target + height bit) % 2 = 1 ∧
    forward bit (oddParent bit target) = target := by
  unfold Gate at gate
  have numerator : 2 * target - 1 - height bit =
      3 * (2 * ((target + height bit) / 3) + 1 - height bit) := by omega
  have raw : oddParent bit target + height bit = 2 * ((target + height bit) / 3) + 1 := by
    unfold oddParent
    rw [numerator]
    omega
  have parity : (oddParent bit target + height bit) % 2 = 1 := by rw [raw]; omega
  refine ⟨?_, parity, ?_⟩
  · have bounds := height_bounds bit
    omega
  · unfold forward collatz
    rw [if_neg (by omega : (oddParent bit target + height bit) % 2 ≠ 0), raw]
    omega

theorem gate_of_odd_replay (bit : Bool) (value target : Int)
    (parity : (value + height bit) % 2 = 1) (hit : forward bit value = target) : Gate bit target := by
  unfold forward collatz at hit
  rw [if_neg (by omega : (value + height bit) % 2 ≠ 0)] at hit
  unfold Gate
  omega

def evenChain : List Bool → Int → Int
  | [], target => target
  | bit :: rest, target => evenChain rest (evenParent bit target)

def Mixed (word : List Bool) : Prop := false ∈ word ∧ true ∈ word

def HitsGate (word : List Bool) (target : Int) : Prop :=
  ∃ (front : List Bool) (bit : Bool) (back : List Bool),
    word = front ++ (bit :: back) ∧ Gate bit (evenChain front target)

def threeLaps (word : List Bool) : List Bool := word ++ (word ++ word)

private theorem evenChain_append (first rest : List Bool) (target : Int) :
    evenChain (first ++ rest) target = evenChain rest (evenChain first target) := by
  induction first generalizing target with
  | nil => rfl
  | cons bit first ih => exact ih (evenParent bit target)

private theorem ungated_step (bit : Bool) (target : Int) (miss : ¬ Gate bit target) :
    target % 3 ≤ evenParent bit target % 3 ∧
    (target % 3 = evenParent bit target % 3 → target % 3 = 2 * height bit) := by
  have residues : target % 3 = 0 ∨ target % 3 = 1 ∨ target % 3 = 2 := by omega
  rcases residues with rem | rem | rem <;> cases bit <;>
    simp only [Gate, height, evenParent] at * <;> constructor <;> omega

private theorem scan (word : List Bool) (target : Int) :
    HitsGate word target ∨ (target % 3 ≤ evenChain word target % 3 ∧
      (target % 3 = evenChain word target % 3 → ∀ bit ∈ word, target % 3 = 2 * height bit)) := by
  induction word generalizing target with
  | nil => exact Or.inr ⟨Int.le_refl _, by simp⟩
  | cons bit rest ih =>
    by_cases gate : (target + height bit) % 3 = 2
    · exact Or.inl ⟨[], bit, rest, rfl, gate⟩
    · rcases ih (evenParent bit target) with ⟨front, pivot, back, shape, found⟩ | ⟨tailLe, tailEq⟩
      · exact Or.inl ⟨bit :: front, pivot, back, congrArg (List.cons bit) shape, found⟩
      · obtain ⟨headLe, headEq⟩ := ungated_step bit target gate
        refine Or.inr ⟨Int.le_trans headLe tailLe, ?_⟩
        intro same other member
        change target % 3 = evenChain rest (evenParent bit target) % 3 at same
        have firstEq : target % 3 = evenParent bit target % 3 := by omega
        rcases List.mem_cons.mp member with rfl | inRest
        · exact headEq firstEq
        · exact firstEq.trans (tailEq (by omega) other inRest)

theorem gate_or_increase (word : List Bool) (mixed : Mixed word) (target : Int) :
    HitsGate word target ∨ target % 3 < evenChain word target % 3 := by
  rcases scan word target with found | ⟨weak, stuck⟩
  · exact Or.inl found
  · right
    have different : target % 3 ≠ evenChain word target % 3 := by
      intro same
      have zero := stuck same false mixed.1
      have two := stuck same true mixed.2
      change target % 3 = 0 at zero
      change target % 3 = 2 at two
      omega
    omega

private theorem extend_gate (first rest : List Bool) (target : Int) :
    HitsGate first target ∨ HitsGate rest (evenChain first target) → HitsGate (first ++ rest) target := by
  rintro (⟨front, bit, back, shape, found⟩ | ⟨front, bit, back, shape, found⟩)
  · exact ⟨front, bit, back ++ rest, by simp [shape, List.append_assoc], found⟩
  · exact ⟨first ++ front, bit, back, by simp [shape, List.append_assoc],
      by simpa only [evenChain_append] using found⟩

theorem three_laps_gate (word : List Bool) (mixed : Mixed word) (target : Int) :
    HitsGate (threeLaps word) target := by
  let once := evenChain word target
  let twice := evenChain word once
  apply extend_gate word (word ++ word) target
  rcases gate_or_increase word mixed target with found | riseOne
  · exact Or.inl found
  right
  apply extend_gate word word once
  rcases gate_or_increase word mixed once with found | riseTwo
  · exact Or.inl found
  right
  rcases gate_or_increase word mixed twice with found | riseThree
  · exact found
  · exfalso
    dsimp only [once, twice] at riseTwo riseThree
    omega

def replay : List Bool → Int → Int
  | [], seed => seed
  | bit :: rest, seed => forward bit (replay rest seed)

def Preimage (word : List Bool) (target seed : Int) : Prop := 0 ≤ seed ∧ replay word seed = target

theorem evenChain_nonneg (word : List Bool) (target : Int) (nonneg : 0 ≤ target) :
    0 ≤ evenChain word target := by
  induction word generalizing target with
  | nil => exact nonneg
  | cons bit rest ih => exact ih _ (even_nonneg bit target nonneg)

theorem replay_even (word : List Bool) (target : Int) : replay word (evenChain word target) = target := by
  induction word generalizing target with
  | nil => rfl
  | cons bit rest ih =>
    exact (congrArg (forward bit) (ih (evenParent bit target))).trans (even_spec bit target).2

private theorem replay_append (first rest : List Bool) (seed : Int) :
    replay (first ++ rest) seed = replay first (replay rest seed) := by
  induction first with
  | nil => rfl
  | cons bit first ih => exact congrArg (forward bit) ih

theorem padded_preimages (front : List Bool) (bit : Bool) (back : List Bool) (target : Int)
    (nonneg : 0 ≤ target) (gate : Gate bit (evenChain front target)) :
    let word := front ++ (bit :: back)
    let evenSeed := evenChain word target
    let oddSeed := evenChain back (oddParent bit (evenChain front target))
    evenSeed ≠ oddSeed ∧ Preimage word target evenSeed ∧ Preimage word target oddSeed := by
  let pivot := evenChain front target
  obtain ⟨oddNonneg, oddParity, oddHit⟩ := odd_spec bit pivot (evenChain_nonneg front target nonneg) gate
  have evenParity := (even_spec bit pivot).1
  refine ⟨?_, ⟨evenChain_nonneg _ _ nonneg, replay_even _ _⟩, ⟨evenChain_nonneg _ _ oddNonneg, ?_⟩⟩
  · intro equal
    rw [evenChain_append] at equal
    change evenChain back (evenParent bit pivot) = evenChain back (oddParent bit pivot) at equal
    have same : evenParent bit pivot = oddParent bit pivot := by
      simpa only [replay_even] using congrArg (replay back) equal
    rw [same] at evenParity
    omega
  · rw [replay_append]
    change replay front (forward bit (replay back (evenChain back (oddParent bit pivot)))) = target
    rw [replay_even, oddHit]
    exact replay_even front target

theorem three_laps_preimages (word : List Bool) (mixed : Mixed word) (target : Int) (nonneg : 0 ≤ target) :
    ∃ (front : List Bool) (bit : Bool) (back : List Bool),
      threeLaps word = front ++ (bit :: back) ∧ front.length < 3 * word.length ∧
      Gate bit (evenChain front target) ∧
      let evenSeed := evenChain (threeLaps word) target
      let oddSeed := evenChain back (oddParent bit (evenChain front target))
      evenSeed ≠ oddSeed ∧ Preimage (threeLaps word) target evenSeed ∧ Preimage (threeLaps word) target oddSeed := by
  obtain ⟨front, bit, back, shape, found⟩ := three_laps_gate word mixed target
  have lengths := congrArg List.length shape
  simp only [threeLaps, List.length_append, List.length_cons] at lengths
  refine ⟨front, bit, back, shape, by omega, found, ?_⟩
  rw [shape]
  exact padded_preimages front bit back target nonneg found

end InverseBranch