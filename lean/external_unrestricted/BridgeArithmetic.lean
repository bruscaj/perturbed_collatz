import BridgeExpectedTypes
import SyracuseSlope

/-! Arithmetic targets for the frozen finite source-word dictionary. -/
namespace ExternalFiniteBridgeArithmetic
open ExternalFiniteBridgeDraft

theorem defect_bounds : DefectBounds := by
  intro θ r
  exact ⟨ExternalRungTransfer.defect_nonneg θ r,
    ExternalRungTransfer.defect_lt_one θ r⟩

theorem nonintegral_endpoint : NonintegralEndpoint := by
  intro θ r hni
  apply (Int.ceil_eq_floor_add_one_iff_notMem _).mpr
  rintro ⟨z, hz⟩
  exact hni ⟨z, hz.symm⟩

theorem strict_rung_caps : StrictRungCaps := by
  intro θ r hr t ht
  exact ExternalRungTransfer.rung_cap θ r t hr ht

theorem unit_floor_increments : UnitFloorIncrements := by
  intro θ hθ t
  exact ExternalRungTransfer.floor_increments θ hθ t

theorem floor_increment_alphabet : FloorIncrementAlphabet := by
  intro θ hlo hhi t
  have hl := unit_floor_increments θ hlo t
  have hu : floorAt θ (t + 1) ≤ floorAt θ t + 2 := by
    have hm : ((t + 1 : ℕ) : ℝ) * θ ≤ (t : ℝ) * θ + 2 := by
      push_cast
      linarith
    have hf := Int.floor_mono hm
    simpa only [floorAt, Int.floor_add_ofNat] using hf
  omega

theorem source_slope_facts : SourceSlopeFacts := by
  exact ⟨ExternalSyracuseSlope.one_lt_theta,
    ExternalSyracuseSlope.theta_lt_two, ExternalSyracuseSlope.theta_irrational⟩

theorem source_slope_nonintegral : SourceSlopeNonintegral := by
  intro r hr
  rintro ⟨z, hz⟩
  exact ((source_slope_facts.2.2.natCast_mul (Nat.ne_of_gt hr)).ne_int z) hz

theorem literal_closing_depth : LiteralClosingDepth := by
  intro r w hw
  change floorAt slope r - wordPrefix r w (Fin.last r) = -1
  rw [hw.2.2.1, nonintegral_endpoint slope r (source_slope_nonintegral r hw.1)]
  omega

end ExternalFiniteBridgeArithmetic
