import RateExpectedTypes
import Mathlib.Data.List.MinMax

/-! The frozen first-future-maximum selector, including its strict tie rule.
No density or rate conclusion is assumed or proved in this module. -/
namespace ExternalO3RateMarker
open ExternalO3GeneralDraft ExternalO3RateDraft

/-- A sorted finite list preserves order of its members' first indices. -/
theorem value_le_of_idxOf_le {n : ℕ} {l : List (Fin n)}
    (hl : l.Pairwise (fun i j => i < j)) {i j : Fin n}
    (hi : i ∈ l) (hj : j ∈ l) (hij : l.idxOf i ≤ l.idxOf j) : i ≤ j := by
  have hi' := List.idxOf_lt_length_iff.mpr hi
  have hj' := List.idxOf_lt_length_iff.mpr hj
  rcases lt_or_eq_of_le hij with hlt | heq
  · have h := hl.rel_getElem_of_lt hi' hj' hlt
    simpa only [List.getElem_idxOf] using le_of_lt h
  · have h : i = j := by
      calc
        i = l[l.idxOf i] := (List.getElem_idxOf hi').symm
        _ = l[l.idxOf j] := by simp only [heq]
        _ = j := List.getElem_idxOf hj'
    exact h.le

/-- The frozen fold is the standard first-occurring list argmax. -/
theorem firstFutureMax_eq_argmax (h : Depth) (w : Window h) :
    firstFutureMax h w =
      (((List.finRange h.val).filter (fun i => 0 < i.val)).argmax w).getD
        (zeroIndex h) := by
  unfold firstFutureMax List.argmax List.argAux
  congr 2
  funext o i
  cases o <;> rfl

/-- Exact frozen selector law, valid on all natural-valued windows. -/
theorem marker_selector_law : MarkerSelectorLaw := by
  intro h w hh
  let l := (List.finRange h.val).filter (fun i => 0 < i.val)
  let one : Fin h.val := ⟨1, by omega⟩
  have hone : one ∈ l := by simp [l, one]
  have hn : l ≠ [] := by intro he; simp [he] at hone
  have hp : l.Pairwise (fun i j => i < j) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange h.val)
  have hex : ∃ j, l.argmax w = some j := by
    cases he : l.argmax w with
    | none => exact False.elim (hn (List.argmax_eq_none.mp he))
    | some j => exact ⟨j, rfl⟩
  obtain ⟨j, hj⟩ := hex
  have hjmem : j ∈ l.argmax w := hj
  have hjl := List.argmax_mem hjmem
  have hs : firstFutureMax h w = j := by
    rw [firstFutureMax_eq_argmax]
    change (l.argmax w).getD (zeroIndex h) = j
    rw [hj]; rfl
  rw [hs]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [l, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] using hjl
  · intro i hi
    have hil : i ∈ l := by simp [l, hi]
    exact List.le_of_mem_argmax hil hjmem
  · intro i hi hij
    have hil : i ∈ l := by simp [l, hi]
    by_contra hnot
    have hidx := List.index_of_argmax hjmem hil (le_of_not_gt hnot)
    have hord := value_le_of_idxOf_le hp hjl hil hidx
    exact (not_lt_of_ge hord) hij

end ExternalO3RateMarker
