import BridgeDefinitions

/-! UNFROZEN proposed finite bridge targets. Definitions of propositions only. -/
namespace ExternalFiniteBridgeDraft

def FiniteWordPrefixEncoding : Prop :=
  (∀ r (w : Word r), PositiveWord r w →
    PositivePrefix r (wordPrefix r w) ∧ prefixLetters r (wordPrefix r w) = w) ∧
  (∀ r (K : Prefix r), PositivePrefix r K →
    PositiveWord r (prefixLetters r K) ∧ wordPrefix r (prefixLetters r K) = K)

def AbstractPrefixCompatibility : Prop :=
  (∀ θ r (w : Word r), 0 < r →
    (FloorWord θ r w ↔ ExternalPrefixSpec.FloorAdmissible
      (floorAt θ) (extendPrefix r (wordPrefix r w)) r)) ∧
  (∀ θ r (J : Depth r), DepthBridge θ r J ↔
    ExternalPrefixSpec.DepthBridge (floorAt θ) (extendPrefix r J) r)

def DefectBounds : Prop := ∀ θ r, 0 ≤ defect θ r ∧ defect θ r < 1

def NonintegralEndpoint : Prop := ∀ θ r, NonIntegralAt θ r →
  Int.ceil ((r : ℝ) * θ) = floorAt θ r + 1

def StrictRungCaps : Prop := ∀ θ r, StrictRung θ r →
  ∀ t : ℕ, t < r → literalCap θ r t = floorAt θ t

def UnitFloorIncrements : Prop := ∀ θ : ℝ, 1 ≤ θ → ∀ t : ℕ,
  floorAt θ t + 1 ≤ floorAt θ (t + 1)

def FloorIncrementAlphabet : Prop := ∀ θ : ℝ, 1 ≤ θ → θ ≤ 2 → ∀ t : ℕ,
  floorAt θ (t + 1) - floorAt θ t = 1 ∨ floorAt θ (t + 1) - floorAt θ t = 2

def SourceSlopeFacts : Prop := 1 < slope ∧ slope < 2 ∧ Irrational slope

def SourceSlopeNonintegral : Prop := ∀ r : ℕ, 0 < r → NonIntegralAt slope r

def SourceRungsUnbounded : Prop := ∀ R : ℕ, ∃ r : ℕ, R < r ∧ StrictRung slope r

def LiteralClosingDepth : Prop := ∀ r (w : Word r), SourceWord slope r w →
  wordDepth slope r w (Fin.last r) = -1

def SourceLastLetterLowerable : Prop := ∀ θ r (w : Word r), 1 ≤ θ →
  StrictRung θ r → NonIntegralAt θ r → SourceWord θ r w →
  ∀ i : Fin r, i.val + 1 = r → 2 ≤ w i

def LowerRaiseTransport : Prop := ∀ θ r, 1 ≤ θ → StrictRung θ r → NonIntegralAt θ r →
  (∀ w : Word r, SourceWord θ r w →
    FloorWord θ r (lowerLast r w) ∧ raiseLast r (lowerLast r w) = w) ∧
  (∀ w : Word r, FloorWord θ r w →
    SourceWord θ r (raiseLast r w) ∧ lowerLast r (raiseLast r w) = w)

def FinitePopulations : Prop := ∀ θ r,
  Finite {w : Word r // SourceWord θ r w} ∧
  Finite {w : Word r // FloorWord θ r w} ∧
  Finite {J : Depth r // DepthBridge θ r J}

def SourceFloorBijection : Prop := ∀ θ r, 1 ≤ θ → StrictRung θ r → NonIntegralAt θ r →
  ∃ e : {w : Word r // SourceWord θ r w} ≃ {w : Word r // FloorWord θ r w},
    (∀ w, (e w).val = lowerLast r w.val) ∧
    (∀ w, (e.symm w).val = raiseLast r w.val)

def SourceDepthBijection : Prop := ∀ r, StrictRung slope r →
  ∃ e : {w : Word r // SourceWord slope r w} ≃ {J : Depth r // DepthBridge slope r J},
    (∀ w, (e w).val = sourceBridgeDepth slope r w.val) ∧
    (∀ J, (e.symm J).val = raiseLast r (depthLetters slope r J.val))

def RewardEndpointInvariant : Prop := ∀ r (w : Word r),
  reward r (lowerLast r w) = reward r w ∧ reward r (raiseLast r w) = reward r w

def RewardRealPower : Prop := ∀ r (w : Word r), powerReward slope r w = reward r w

def SourceDepthReward : Prop := ∀ r (w : Word r),
  reward r w = depthReward slope r (sourceBridgeDepth slope r w)

def ReferenceAtRungs : Prop := ∀ r, StrictRung slope r →
  literalReference slope r = phaseZeroReference slope r

def PhaseZeroExtremizer : Prop := ∀ r, StrictRung slope r →
  SourceWord slope r (mechanicalWord slope r) ∧
  reward r (mechanicalWord slope r) = phaseZeroReference slope r ∧
  ∀ w : Word r, SourceWord slope r w → reward r w ≤ phaseZeroReference slope r

/-- Added at the owner pre-freeze review: equality at the finite maximum is unique. -/
def UniqueExtremizer : Prop := ∀ r, StrictRung slope r → ∀ w : Word r,
  SourceWord slope r w →
  (reward r w = phaseZeroReference slope r ↔ w = mechanicalWord slope r)

def ThresholdCountPreservation : Prop := ∀ r, StrictRung slope r → ∀ q : ℝ,
  sourceCount r q = floorCount r q ∧ sourceCount r q = depthCount r q

def LengthOneBoundary : Prop :=
  StrictRung slope 1 ∧
  (∀ w : Word 1, SourceWord slope 1 w ↔ w 0 = 2) ∧
  (∀ w : Word 1, FloorWord slope 1 w ↔ w 0 = 1) ∧
  (∀ w : Word 1, SourceWord slope 1 w →
    reward 1 w = 1 ∧ wordDepth slope 1 w (Fin.last 1) = -1 ∧
    sourceBridgeDepth slope 1 w = fun _ => 0) ∧
  phaseZeroReference slope 1 = 1 ∧ sourceCount 1 1 = 1

def ZeroLengthConvention : Prop :=
  (∀ w : Word 0, ¬ SourceWord slope 0 w ∧ ¬ FloorWord slope 0 w ∧ reward 0 w = 0) ∧
  (∀ J : Depth 0, DepthBridge slope 0 J ↔ J = fun _ => 0)

end ExternalFiniteBridgeDraft
