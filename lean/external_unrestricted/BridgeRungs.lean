import BridgeExpectedTypes
import SyracuseSlope
import PositiveCeilReturns

/-! Unbounded strict upper-ceiling-defect records at irrational slopes.
The small-gap return theorem is reused; no finite-population or pressure
conclusion is assumed here. -/
namespace ExternalFiniteBridgeRungs
open ExternalFiniteBridgeDraft

theorem defect_pos (θ : ℝ) (hθ : Irrational θ) (r : ℕ) (hr : 0 < r) :
    0 < defect θ r := by
  have hi := hθ.natCast_mul (Nat.ne_of_gt hr)
  have hle := Int.le_ceil ((r : ℝ) * θ)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact sub_pos.mpr hlt
  · exact False.elim (hi.ne_int _ heq)

/-- Every finite initial segment of positive indices has a positive lower
bound for its ceiling gaps. No minimum over the zero index is taken. -/
theorem finite_gap_lower_bound (θ : ℝ) (hθ : Irrational θ) (R : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℕ, 0 < t → t ≤ R → ε ≤ defect θ t := by
  induction R with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro t ht htR
      omega
  | succ R ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      refine ⟨min ε (defect θ (R + 1)), lt_min hε (defect_pos θ hθ _ (by omega)), ?_⟩
      intro t ht htR
      by_cases hlast : t = R + 1
      · subst t
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound t ht (by omega))

/-- A least positive index with a gap smaller than every gap in the initial
segment is a new strict record beyond that segment. -/
theorem irrational_rungs_unbounded (θ : ℝ) (hθ : Irrational θ) (R : ℕ) :
    ∃ r : ℕ, R < r ∧ StrictRung θ r := by
  obtain ⟨ε, hε, hbound⟩ := finite_gap_lower_bound θ hθ R
  obtain ⟨u, hu, _, hsmall⟩ :=
    ExternalO3PositiveCeilReturns.exists_positive_ceil_gap θ hθ ε hε
  have hex : ∃ r : ℕ, 0 < r ∧ defect θ r < ε :=
    ⟨u, by omega, hsmall⟩
  let r := Nat.find hex
  have hr : 0 < r ∧ defect θ r < ε := Nat.find_spec hex
  have hR : R < r := by
    by_contra hnot
    have := hbound r hr.1 (by omega)
    linarith [hr.2]
  refine ⟨r, hR, hr.1, ?_⟩
  intro t ht htr
  have hnot := Nat.find_min hex htr
  have hlarge : ε ≤ defect θ t := by
    by_contra h
    exact hnot ⟨ht, lt_of_not_ge h⟩
  exact hr.2.trans_le hlarge

theorem source_rungs_unbounded : SourceRungsUnbounded := by
  intro R
  apply irrational_rungs_unbounded slope
  exact ExternalSyracuseSlope.theta_irrational

end ExternalFiniteBridgeRungs
