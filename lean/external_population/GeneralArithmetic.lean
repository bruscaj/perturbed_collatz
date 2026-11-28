import GeneralExpectedTypes
import Arithmetic
import PopulationWeights

/-!
Finite-block arithmetic and window foundations for the frozen general-depth
specification. All future blocks are actual finite Syracuse iterates. No orbit
termination, population independence or density-existence hypothesis is used.
GeneralChallenge is deliberately not imported.
-/
namespace ExternalO3GeneralArithmetic

open ExternalO3GeneralDraft
open ExternalO3Spec (IsOddSeed stride strideValuation blockLength nextBlock)
open ExternalO3Arithmetic
open scoped BigOperators

/-- Every finite stride iterate stays in the source odd positive domain. -/
theorem stride_iterate_odd (x : ℕ) (hx : IsOddSeed x) (i : ℕ) :
    IsOddSeed ((Nat.iterate stride i) x) := by
  cases i with
  | zero => simpa using hx
  | succ i =>
    simp only [Function.iterate_succ_apply']
    exact stride_output _

theorem nextBlock_odd (x : ℕ) (hx : IsOddSeed x) : IsOddSeed (nextBlock x) := by
  exact stride_iterate_odd x hx (blockLength x)

theorem futureBlockSeed_odd (x : ℕ) (hx : IsOddSeed x) (i : ℕ) :
    IsOddSeed (futureBlockSeed x i) := by
  induction i with
  | zero => simpa [futureBlockSeed] using hx
  | succ i ih =>
    change IsOddSeed ((Nat.iterate nextBlock (i + 1)) x)
    rw [Function.iterate_succ_apply']
    exact nextBlock_odd _ ih

theorem blocks_well_defined : BlocksWellDefined := by
  intro x hx i
  have hy := futureBlockSeed_odd x hx i
  exact ⟨hy, block_length_law _ hy⟩

theorem window_validity : WindowValidity := by
  intro h x hx i
  exact block_length_positive _ (futureBlockSeed_odd x hx i.val)

/-- Deleting the first ascending stride does not change the next block endpoint. -/
theorem nextBlock_stride_of_long (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) : nextBlock (stride x) = nextBlock x := by
  unfold nextBlock
  rw [← block_decrements x hx hr]
  rw [Function.iterate_succ_apply]

/-- Beyond the head, all recorded complete blocks are unchanged by an ascent. -/
theorem futureBlockSeed_stride_of_pos (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) (i : ℕ) (hi : 0 < i) :
    futureBlockSeed (stride x) i = futureBlockSeed x i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hi)
  simp only [futureBlockSeed, Function.iterate_succ_apply]
  rw [nextBlock_stride_of_long x hx hr]

/-- At an exit the block endpoint is exactly the next stride, with no extra step. -/
theorem nextBlock_of_short (x : ℕ) (hr : blockLength x = 1) : nextBlock x = stride x := by
  simp [nextBlock, hr]

theorem futureBlockSeed_succ_of_short (x : ℕ) (hr : blockLength x = 1) (i : ℕ) :
    futureBlockSeed x (i + 1) = futureBlockSeed (stride x) i := by
  simp only [futureBlockSeed, Function.iterate_succ_apply]
  rw [nextBlock_of_short x hr]

theorem ascending_window_transport (h : Depth) (x : ℕ) (hx : IsOddSeed x)
    (hr : 2 ≤ blockLength x) :
    window h (stride x) = decrementHead h (window h x) := by
  funext i
  by_cases hi : i.val = 0
  · have hdec : blockLength (stride x) = blockLength x - 1 := by
      have ht := block_decrements x hx hr
      omega
    simpa [window, decrementHead, hi, futureBlockSeed] using hdec
  · simp only [window, decrementHead, ite_eq_right hi]
    rw [futureBlockSeed_stride_of_pos x hx hr i.val (Nat.pos_of_ne_zero hi)]

theorem exit_window_transport (h : Depth) (x : ℕ) (hr : blockLength x = 1) :
    window h x = prependOne h (window h (stride x)) := by
  funext i
  by_cases hi : i.val = 0
  · simp [window, prependOne, hi, futureBlockSeed, hr]
  · simp only [window, prependOne, dite_eq_right hi]
    have hs := futureBlockSeed_succ_of_short x hr (i.val - 1)
    have he : (i.val - 1) + 1 = i.val := by omega
    rw [he] at hs
    exact congrArg blockLength hs

theorem window_transport : WindowTransport := by
  intro h x hx
  exact ⟨ascending_window_transport h x hx, exit_window_transport h x⟩

theorem nextBlock_one : nextBlock 1 = 1 := by
  obtain ⟨hs, hb⟩ := fixed_point_convention
  simp [nextBlock, hs, hb]

theorem futureBlockSeed_one (i : ℕ) : futureBlockSeed 1 i = 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (Nat.iterate nextBlock (i + 1)) 1 = 1
    rw [Function.iterate_succ_apply']
    change nextBlock (futureBlockSeed 1 i) = 1
    rw [ih, nextBlock_one]

theorem window_one (h : Depth) : window h 1 = fun _ => 1 := by
  funext i
  simp only [window, futureBlockSeed_one, fixed_point_convention.2]

theorem fixed_point_and_zero : FixedPointAndZero := by
  refine ⟨fixed_point_convention.1, window_one, ?_⟩
  intro h φ
  constructor
  · refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [fixed_point_convention.1]
  · rintro ⟨hx, _⟩
    have hfalse := hx.1
    omega

theorem correction_restriction : CorrectionRestriction := by
  intro h φ ψ hagree x hx
  have hcur := hagree (window h x) (window_validity h x hx)
  have hnext := hagree (window h (stride x)) (window_validity h (stride x) (stride_output x))
  simp only [FailsAt, rawPotential, hcur, hnext]

end ExternalO3GeneralArithmetic
