import AnalyticCost

/-! Exact composition of the actual candidate pressure laws. -/
namespace ExternalBridgePressureAnalyticCore
open ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureAnalyticUniformPressure ExternalBridgePressureAnalyticCost

theorem candidate_core_pressure_components : CandidateCorePressureComponents :=
  ⟨source_rung_pressure_composition,
    physical_reward_pressure_composition.1,
    cost_pressure_composition.1,
    physical_reward_pressure_composition.2,
    cost_pressure_composition.2.2⟩

end ExternalBridgePressureAnalyticCore
