import OptimizationEncoding
import OptimizationArithmetic
import OptimizationPaths
import OptimizationDeletion
import OptimizationMass
import OptimizationDensity
import OptimizationJoin

/-! All fifteen required targets; the optional monotonicity target remains separate. -/
namespace ExternalO3OptimizationChallenge
open ExternalO3OptimizationDraft

theorem genericStrictCycleCriterion : GenericStrictCycleCriterion :=
  ExternalO3OptimizationPaths.generic_strict_cycle_criterion

theorem vertexEncodingAndExtension : VertexEncodingAndExtension :=
  ExternalO3OptimizationEncoding.vertex_encoding_and_extension

theorem edgeEncodingAndWeights : EdgeEncodingAndWeights :=
  ExternalO3OptimizationEncoding.edge_encoding_and_weights

theorem naturalCycleSigns : NaturalCycleSigns :=
  ExternalO3OptimizationArithmetic.natural_cycle_signs

theorem commonDyadicDenominator : CommonDyadicDenominator :=
  ExternalO3OptimizationArithmetic.common_dyadic_denominator

theorem numeratorMinimumWellPosed : NumeratorMinimumWellPosed :=
  ExternalO3OptimizationArithmetic.numerator_minimum_well_posed

theorem genericElementaryReduction : GenericElementaryReduction :=
  ExternalO3OptimizationPaths.generic_elementary_reduction

theorem genericDeletionOptimum : GenericDeletionOptimum :=
  ExternalO3OptimizationDeletion.generic_deletion_optimum

theorem finiteOptimizationExact : FiniteOptimizationExact :=
  ExternalO3OptimizationDeletion.finite_optimization_exact

theorem truncationMassIdentity : TruncationMassIdentity :=
  ExternalO3OptimizationMass.truncation_mass_identity

theorem discardedMassBound : DiscardedMassBound :=
  ExternalO3OptimizationMass.discarded_mass_bound

theorem literalInfimumSandwich : LiteralInfimumSandwich :=
  ExternalO3OptimizationDensity.literal_infimum_sandwich

theorem diagonalConvergence : DiagonalConvergence :=
  ExternalO3OptimizationDensity.diagonal_convergence

theorem computableExactOptimizer : ComputableExactOptimizer :=
  ExternalO3OptimizationJoin.computable_exact_optimizer

theorem computableDyadicApproximation : ComputableDyadicApproximation :=
  ExternalO3OptimizationJoin.computable_dyadic_approximation

end ExternalO3OptimizationChallenge
