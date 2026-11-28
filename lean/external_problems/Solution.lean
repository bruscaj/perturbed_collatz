import ExpectedTypes

/-! Abstract integer supporting lemmas only. No headline limit theorem. -/
namespace ExternalPrefixChallenge
open ExternalPrefixSpec

theorem floorDepthEquivalence : FloorDepthEquivalence := by
  intro L K n hL
  simp only [FloorAdmissible, DepthBridge, DepthOf]
  constructor
  · rintro ⟨h0, hn, hstep, hcap⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro t ht
      have := hcap t ht
      omega
    · intro t ht
      have := hstep t ht
      omega
  · rintro ⟨h0, hn, hcap, hstep⟩
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro t ht
      have := hstep t ht
      omega
    · intro t ht
      have := hcap t ht
      omega

theorem depthInvolution : DepthInvolution := by
  intro L K
  funext t
  simp only [DepthOf]
  omega

theorem closingFloorEquivalence : ClosingFloorEquivalence := by
  intro L K n hn hL
  simp only [ClosingAdmissible, FloorAdmissible]
  constructor
  · rintro ⟨h0, hend, hstep, hcap⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [LowerEndpoint, show 0 ≠ n by omega, h0]
    · simp [LowerEndpoint, hend]
    · intro t ht
      have htn : t ≠ n := by omega
      by_cases hlast : t + 1 = n
      · have hc := hcap t ht
        have hl := hL t ht
        simp only [LowerEndpoint, ite_eq_right htn, ite_eq_left hlast]
        rw [hlast] at hl
        rw [hlast]
        omega
      · have hs := hstep t ht
        simpa only [LowerEndpoint, ite_eq_right htn, ite_eq_right hlast] using hs
    · intro t ht
      by_cases he : t = n
      · subst t
        simp [LowerEndpoint, hend]
      · have hc := hcap t (by omega)
        simpa only [LowerEndpoint, ite_eq_right he] using hc
  · rintro ⟨h0, hend, hstep, hcap⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [LowerEndpoint, ite_eq_right (show 0 ≠ n by omega)] using h0
    · simp only [LowerEndpoint, ite_eq_left] at hend
      omega
    · intro t ht
      have htn : t ≠ n := by omega
      have hs := hstep t ht
      by_cases hlast : t + 1 = n
      · simp only [LowerEndpoint, ite_eq_right htn, ite_eq_left hlast] at hs
        omega
      · simpa only [LowerEndpoint, ite_eq_right htn, ite_eq_right hlast] using hs
    · intro t ht
      have hc := hcap t (by omega)
      simpa only [LowerEndpoint, ite_eq_right (show t ≠ n by omega)] using hc

theorem floorRaiseSoundness : FloorRaiseSoundness := by
  intro L K n hn h
  rcases h with ⟨h0, hend, hstep, hcap⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [RaiseEndpoint, show 0 ≠ n by omega, h0]
  · simp [RaiseEndpoint, hend]
  · intro t ht
    have hs := hstep t ht
    have htn : t ≠ n := by omega
    by_cases hlast : t + 1 = n
    · simp only [RaiseEndpoint, ite_eq_right htn, ite_eq_left hlast]
      omega
    · simpa only [RaiseEndpoint, ite_eq_right htn, ite_eq_right hlast] using hs
  · intro t ht
    simpa only [RaiseEndpoint, ite_eq_right (show t ≠ n by omega)] using hcap t (by omega)

theorem endpointInverses : EndpointInverses := by
  intro K n
  constructor <;> funext t <;>
    simp only [RaiseEndpoint, LowerEndpoint] <;>
    split <;> omega

end ExternalPrefixChallenge
