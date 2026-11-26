import Lean

namespace PeriodSevenBasin

def step (offset value : Int) : Int :=
  (if value % 2 = 0 then value / 2 else (3 * value + 1) / 2) + offset

def run : List Int → Int → Int
  | [], value => value
  | offset :: rest, value => run rest (step offset value)

private def factor : List Int → Int → Int
  | [], _ => 1
  | offset :: rest, value => (if value % 2 = 0 then 1 else 3) * factor rest (step offset value)

private theorem step_lift (offset value shift : Int) :
    step offset (value + 2 * shift) = step offset value + (if value % 2 = 0 then shift else 3 * shift) := by
  have parity : (value + 2 * shift) % 2 = value % 2 := by omega
  unfold step
  rw [parity]
  split <;> omega

private theorem run_lift (offsets : List Int) (value shift : Int) :
    run offsets (value + 2 ^ offsets.length * shift) = run offsets value + factor offsets value * shift := by
  induction offsets generalizing value shift with
  | nil => simp [run, factor]
  | cons offset rest ih =>
    simp only [List.length_cons, Int.pow_succ, run, factor]
    rw [show 2 ^ rest.length * 2 * shift = 2 * (2 ^ rest.length * shift) by ac_rfl, step_lift]
    by_cases even : value % 2 = 0
    · simp [even, ih]
    · simp only [if_neg even]
      rw [show 3 * (2 ^ rest.length * shift) = 2 ^ rest.length * (3 * shift) by ac_rfl, ih]
      ac_rfl

def word : List Int := [-1, 0, 0, 1, 0, 0, 0]

private def branch (row : Fin 9) (digit : Fin 4) : Int × Int :=
  let rows : Array (Array (Int × Int)) := #[
    #[(6,1), (18,3), (38,3), (114,9)], #[(2,1), (22,1), (50,3), (66,3)],
    #[(41,1), (122,3), (123,3), (124,3)], #[(34,1), (55,1), (56,1), (146,3)],
    #[(58,1), (59,1), (60,1), (178,3)], #[(83,1), (84,1), (250,3), (251,3)],
    #[(90,1), (91,1), (92,1), (274,3)], #[(82,1), (102,1), (106,1), (107,1)],
    #[(126,1), (378,3), (379,3), (380,3)]]
  rows[row.val]![digit.val]!

set_option maxRecDepth 4096 in
private theorem branch_data : ∀ (row : Fin 9) (digit : Fin 4),
    let (base, stride) := branch row digit
    run word base = (row.val : Int) + 1 ∧ factor word base * stride = 9 ∧
    0 < base ∧ base ≤ 128 * ((row.val : Int) + 1) - 14 ∧ 0 < stride ∧ stride ≤ 9 := by decide

set_option maxRecDepth 4096 in
private theorem branch_tags : ∀ (row : Fin 9) (left right : Fin 4),
    (branch row left).1 % 128 = (branch row right).1 % 128 → left = right := by decide

private def rowOf (target : Int) : Fin 9 := ⟨((target - 1) % 9).toNat, by omega⟩

def child (target : Int) (digit : Fin 4) : Int :=
  let (base, stride) := branch (rowOf target) digit
  base + 128 * (stride * ((target - 1) / 9))

theorem child_returns (target : Int) (positive : 0 < target) (digit : Fin 4) :
    run word (child target digit) = target ∧ 0 < child target digit ∧ child target digit ≤ 128 * target - 14 := by
  let row := rowOf target
  let quotient := (target - 1) / 9
  have decomp : target = ((row.val : Int) + 1) + 9 * quotient := by dsimp [row, rowOf, quotient]; omega
  have nonneg : 0 ≤ quotient := by dsimp [quotient]; omega
  let base := (branch row digit).1
  let stride := (branch row digit).2
  have checked : run word base = (row.val : Int) + 1 ∧ factor word base * stride = 9 ∧
      0 < base ∧ base ≤ 128 * ((row.val : Int) + 1) - 14 ∧ 0 < stride ∧ stride ≤ 9 := branch_data row digit
  obtain ⟨endpoint, scale, basePos, baseMax, stridePos, strideMax⟩ := checked
  change run word (base + 128 * (stride * quotient)) = target ∧ _
  have lift := run_lift word base (stride * quotient)
  change run word (base + 128 * (stride * quotient)) = run word base + factor word base * (stride * quotient) at lift
  have shiftPos := Int.mul_nonneg (Int.le_of_lt stridePos) nonneg
  have shiftMax := Int.mul_le_mul_of_nonneg_right strideMax nonneg
  constructor
  · rw [lift, ← Int.mul_assoc, scale, endpoint, ← decomp]
  · change 0 < base + 128 * (stride * quotient) ∧ base + 128 * (stride * quotient) ≤ 128 * target - 14
    dsimp only [base, stride] at *
    omega

theorem child_distinct (target : Int) (left right : Fin 4) (equal : child target left = child target right) :
    left = right := by
  apply branch_tags (rowOf target)
  change (branch (rowOf target) left).1 + 128 * ((branch (rowOf target) left).2 * ((target - 1) / 9)) =
    (branch (rowOf target) right).1 + 128 * ((branch (rowOf target) right).2 * ((target - 1) / 9)) at equal
  omega

def periods : Nat → Int → Int
  | 0, seed => seed
  | depth + 1, seed => periods depth (run word seed)

private def seedAt : Nat → Int → Nat → Int
  | 0, target, _ => target
  | depth + 1, target, index => child (seedAt depth target (index / 4)) ⟨index % 4, by omega⟩

private theorem seedAt_spec (depth : Nat) (target : Int) (positive : 0 < target) (index : Nat) :
    periods depth (seedAt depth target index) = target ∧
    0 < seedAt depth target index ∧ seedAt depth target index ≤ (128 : Int) ^ depth * target := by
  induction depth generalizing index with
  | zero => simp [periods, seedAt, positive]
  | succ depth ih =>
    obtain ⟨reaches, parentPos, parentMax⟩ := ih (index / 4)
    obtain ⟨returns, childPos, childMax⟩ := child_returns _ parentPos ⟨index % 4, by omega⟩
    refine ⟨?_, childPos, ?_⟩
    · simp only [periods, seedAt, returns, reaches]
    · simp only [seedAt, Int.pow_succ]
      rw [show (128 : Int) ^ depth * 128 * target = 128 * (128 ^ depth * target) by ac_rfl]
      omega

private theorem seedAt_injective (depth : Nat) (target : Int) (positive : 0 < target) :
    ∀ left right : Nat, left < 4 ^ depth → right < 4 ^ depth →
      seedAt depth target left = seedAt depth target right → left = right := by
  induction depth with
  | zero => intro left right leftBound rightBound _; simp at leftBound rightBound; omega
  | succ depth ih =>
    intro left right leftBound rightBound equal
    rw [Nat.pow_succ] at leftBound rightBound
    let leftDigit : Fin 4 := ⟨left % 4, by omega⟩
    let rightDigit : Fin 4 := ⟨right % 4, by omega⟩
    change child (seedAt depth target (left / 4)) leftDigit = child (seedAt depth target (right / 4)) rightDigit at equal
    have parentEqual := congrArg (run word) equal
    rw [(child_returns _ (seedAt_spec depth target positive (left / 4)).2.1 leftDigit).1,
        (child_returns _ (seedAt_spec depth target positive (right / 4)).2.1 rightDigit).1] at parentEqual
    have high := ih (left / 4) (right / 4) (by omega) (by omega) parentEqual
    rw [← parentEqual] at equal
    have low := congrArg Fin.val (child_distinct _ _ _ equal)
    change left % 4 = right % 4 at low
    omega

theorem many_preimages (depth : Nat) (target : Int) (positive : 0 < target) :
    ∃ seeds : Fin (4 ^ depth) → Int,
      (∀ left right, seeds left = seeds right → left = right) ∧
      ∀ index, periods depth (seeds index) = target ∧ 0 < seeds index ∧ seeds index ≤ 128 ^ depth * target := by
  refine ⟨fun index => seedAt depth target index.val, ?_, fun index => seedAt_spec depth target positive index.val⟩
  intro left right equal
  exact Fin.ext (seedAt_injective depth target positive _ _ left.isLt right.isLt equal)

theorem cycle_targets : run word 2 = 2 ∧ run word 4 = 4 := by decide

def Escapes (seed : Int) : Prop :=
  ∀ bound : Int, ∃ cutoff : Nat, ∀ tick : Nat, cutoff ≤ tick →
    ∀ phase : Fin 7, bound < run (word.take phase.val) (periods tick seed)

private theorem periods_add (first rest : Nat) (seed : Int) :
    periods (first + rest) seed = periods rest (periods first seed) := by
  induction first generalizing seed with
  | zero => simp [periods]
  | succ first ih => rw [Nat.succ_add]; exact ih (run word seed)

private theorem escape_of_tail (depth : Nat) (seed : Int) (tail : Escapes (periods depth seed)) : Escapes seed := by
  intro bound
  obtain ⟨cutoff, beyond⟩ := tail bound
  refine ⟨depth + cutoff, ?_⟩
  intro tick later phase
  have reached := beyond (tick - depth) (by omega) phase
  rw [← periods_add, show depth + (tick - depth) = tick by omega] at reached
  exact reached

theorem many_escaping (depth : Nat) (target : Int) (positive : 0 < target) (escapes : Escapes target) :
    ∃ seeds : Fin (4 ^ depth) → Int,
      (∀ left right, seeds left = seeds right → left = right) ∧
      ∀ index, Escapes (seeds index) ∧ 0 < seeds index ∧ seeds index ≤ 128 ^ depth * target := by
  obtain ⟨seeds, distinct, hits⟩ := many_preimages depth target positive
  refine ⟨seeds, distinct, ?_⟩
  intro index
  obtain ⟨hit, seedPos, seedMax⟩ := hits index
  exact ⟨escape_of_tail depth _ (hit.symm ▸ escapes), seedPos, seedMax⟩

def LeastEscape (seed : Int) : Prop :=
  0 < seed ∧ Escapes seed ∧ ∀ smaller, 0 < smaller → smaller < seed → ¬Escapes smaller

theorem not_least_of_meeting (seed smaller : Int) (positive : 0 < smaller) (less : smaller < seed)
    (left right : Nat) (meeting : periods left seed = periods right smaller) : ¬LeastEscape seed := by
  rintro ⟨_, escapes, least⟩
  apply least smaller positive less
  apply escape_of_tail right
  rw [← meeting]
  intro bound
  obtain ⟨cutoff, later⟩ := escapes bound
  refine ⟨cutoff, ?_⟩
  intro tick past phase
  rw [← periods_add]
  exact later (left + tick) (by omega) phase

theorem rising_class_reduction (index : Nat) :
    let smaller : Int := 373 + 16384 * (index : Int)
    let seed : Int := 709 + 31104 * (index : Int)
    run word smaller = seed ∧ run word seed = 12122 + 531441 * (index : Int) ∧ ¬LeastEscape seed := by
  let quotient := (index : Int)
  have parent := run_lift word 373 (128 * quotient)
  change run word (373 + 128 * (128 * quotient)) = 709 + 243 * (128 * quotient) at parent
  have climb := run_lift word 709 (243 * quotient)
  change run word (709 + 128 * (243 * quotient)) = 12122 + 2187 * (243 * quotient) at climb
  simp only [← Int.mul_assoc] at parent climb
  refine ⟨parent, climb, ?_⟩
  have nonneg : 0 ≤ quotient := by dsimp [quotient]; omega
  apply not_least_of_meeting _ (373 + 16384 * quotient) (by omega) (by dsimp [quotient] at *; omega) 0 1
  exact parent.symm

end PeriodSevenBasin