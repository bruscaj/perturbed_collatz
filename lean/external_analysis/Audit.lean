import Lean
import Solution

open Lean Elab Command

run_cmd do
  let env ← getEnv
  if env.header.moduleNames.contains `Challenge then
    throwError "Accepted solution environment imported the designated-hole Challenge"
  let owned : Array Name := #[`Definitions, `ExpectedTypes, `Arithmetic, `DensityBounds, `Progressions, `Cylinders, `ExitCylinders, `Gains, `PopulationWeights, `CountablePartition, `PartitionGeneral, `PopulationLabels, `SourceDensity, `DensityTheorems, `DepthOneSeries, `DepthOneLower, `DepthOneUpper, `DepthOneFormula, `DepthOneNumerics, `NumericInfimum, `LogRatioIrrational, `PositiveCeilReturns, `DepthOneNonattainment, `Solution]
  let selected : Array Name := #[``ExternalO3Challenge.valuationFoundation, ``ExternalO3Challenge.blockLengthLaw, ``ExternalO3Challenge.fixedPointConvention, ``ExternalO3Challenge.correctionZeroIrrelevant, ``ExternalO3Challenge.densityExists, ``ExternalO3Challenge.densityUnique, ``ExternalO3Challenge.sourceDensityEquivalence, ``ExternalO3Challenge.symbolicMassSummable, ``ExternalO3Challenge.densityEqualsSymbolic, ``ExternalO3Challenge.infimumWellPosed, ``ExternalO3Challenge.depthOneSeriesSummable, ``ExternalO3Challenge.depthOneFormula, ``ExternalO3Challenge.depthOneNotAttained, ``ExternalO3Challenge.depthOneTail]
  let mut targetCount : Nat := 0
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if owned.contains moduleName then
        if let .axiomInfo _ := info then
          throwError "Own module {moduleName} contains an unproved axiom {name}"
        if getOriginalConstKind? env name == some .thm then
          let axioms ← collectAxioms name
          for axiomName in axioms do
            unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
              throwError "{name} has forbidden axiom {axiomName}"
          if selected.contains name then
            let statement ← liftTermElabM do return toString (← Meta.ppExpr info.type)
            let row := Json.mkObj [("declaration", toJson name.toString),
              ("module", toJson moduleName.toString), ("statement", toJson statement),
              ("raw_type", toJson (repr info.type).pretty),
              ("axioms", toJson (axioms.map Name.toString))]
            liftIO <| IO.println ("O3_TARGET " ++ row.compress)
            targetCount := targetCount + 1
          else
            let row := Json.mkObj [("declaration", toJson name.toString),
              ("module", toJson moduleName.toString),
              ("axioms", toJson (axioms.map Name.toString))]
            liftIO <| IO.println ("O3_HELPER " ++ row.compress)
          theoremCount := theoremCount + 1
  unless targetCount == 14 do throwError "Missing frozen challenge implementations: {targetCount}"
  logInfo m!"Audited all {theoremCount} own theorem closures including generated helpers, with {targetCount} frozen h=1 targets."
