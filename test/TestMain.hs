{-# LANGUAGE DataKinds #-}

module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)

import RHGarden.Algebra
import RHGarden.Core
import RHGarden.Evidence
import RHGarden.Explorer.Suzuki
import RHGarden.Mobius
import RHGarden.Registry
import RHGarden.Representation
import RHGarden.Search

main :: IO ()
main = do
  check "polynomial normalization" $
    polynomial [1, 2, 0, 0] == polynomial [1, 2]
  check "exact polynomial derivative" $
    derivative (polynomial [3, 2, 5]) == polynomial [2, 10]
  check "rational-function quotient derivative" quotientDerivativeTest
  check "Mobius derivative exact identity" $
    case checkMobiusDerivative of Just _ -> True; Nothing -> False
  check "KernelMode rejects LiteratureCertified representation edges" $
    shortestRepresentationRoute KernelMode representationGraph XiAfterMobius LogXiMobius == Nothing
  check "KernelMode rejects ExactExecutable representation edges" $
    shortestRepresentationRoute KernelMode representationGraph MobiusVariable XiAfterMobius == Nothing
  check "KernelMode accepts LeanChecked nontrivial-zeta-zero to xi-zero edge" $
    case shortestRepresentationRoute KernelMode representationGraph NontrivialZetaZero XiZero of
      Just _ -> True
      Nothing -> False
  check "KernelMode accepts LeanChecked xi-zero to nontrivial-zeta-zero edge" $
    case shortestRepresentationRoute KernelMode representationGraph XiZero NontrivialZetaZero of
      Just _ -> True
      Nothing -> False
  check "LeanChecked RH equivalence route does not discharge its terminal proposition" $
    case shortestRoute KernelMode certifiedGraph RH XiRiemannHypothesis of
      Just _ -> not (submissionReady (Nothing :: Maybe (Proof 'RH)))
      Nothing -> False
  check "Li and Li-test Weil positivity are LeanChecked equivalent" $
    case shortestRoute KernelMode certifiedGraph LiPositive WeilLiPositive of
      Just _ -> True
      Nothing -> False
  check "full Weil-form PSD remains a distinct open criterion" $
    shortestRoute KernelMode certifiedGraph WeilFormPSD LiPositive == Nothing
  check "critical-line reality LeanChecks screw-kernel PSD" $
    case shortestRoute KernelMode certifiedGraph ScrewKernelPSD XiZerosReal of
      Just _ -> True
      Nothing -> False
  check "screw-kernel PSD LeanChecks critical-line reality" $
    case shortestRoute KernelMode certifiedGraph XiZerosReal ScrewKernelPSD of
      Just _ -> True
      Nothing -> False
  check "screw-kernel PSD LeanChecks Suzuki pointwise nonnegativity" $
    case shortestRoute KernelMode certifiedGraph SuzukiPsiNonnegative ScrewKernelPSD of
      Just _ -> True
      Nothing -> False
  check "Suzuki pointwise nonnegativity LeanChecks critical-line reality" $
    case shortestRoute KernelMode certifiedGraph XiZerosReal SuzukiPsiNonnegative of
      Just _ -> True
      Nothing -> False
  check "Xi critical-line reality and the Nevanlinna criterion are LeanChecked equivalent" $
    case shortestRoute KernelMode certifiedGraph XiZerosReal XiNevanlinnaFunction of
      Just _ -> True
      Nothing -> False
  check "shifted xi zero-free and Nevanlinna representations are LeanChecked equivalent" $
    case ( shortestRepresentationRoute KernelMode representationGraph
             XiZeroFreeHalfPlane XiShiftedNevanlinnaFunction
         , shortestRepresentationRoute KernelMode representationGraph
             XiShiftedNevanlinnaFunction XiZeroFreeHalfPlane ) of
      (Just _, Just _) -> True
      _ -> False
  check "shifted Nevanlinna-to-eventual-positivity is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph
      XiShiftedNevanlinnaFunction SuzukiShiftedEventualPositivitySet of
      Just route -> routeEndsAt route SuzukiShiftedEventualPositivitySet
      Nothing -> False
  check "shifted Nevanlinna reconstructs a LeanChecked shifted screw function" $
    case shortestRepresentationRoute KernelMode representationGraph
      XiShiftedNevanlinnaFunction ShiftedScrewFunction of
      Just route -> routeEndsAt route ShiftedScrewFunction
      Nothing -> False
  check "a shifted xi zero-free half-plane gives global shifted positivity" $
    case shortestRepresentationRoute KernelMode representationGraph
      XiZeroFreeHalfPlane SuzukiShiftedPositivitySet of
      Just route -> routeEndsAt route SuzukiShiftedPositivitySet
      Nothing -> False
  check "the specialized screw-to-Nevanlinna bridge is LeanChecked" $
    case shortestRoute KernelMode certifiedGraph XiNevanlinnaFunction ScrewFunction of
      Just _ -> True
      Nothing -> False
  check "LiteratureMode rejects Conjectural edges" $
    shortestRepresentationRoute LiteratureMode representationExplorationGraph WeilLiQuadraticValues LiSequence == Nothing
  check "ExplorationMode accepts Conjectural edges" $
    case shortestRepresentationRoute ExplorationMode representationExplorationGraph WeilLiQuadraticValues LiSequence of
      Just _ -> True
      Nothing -> False
  check "LiteratureMode rejects NumericalEvidence Explorer edges" $
    shortestRepresentationRoute LiteratureMode representationGraph
      SuzukiPositivityExplorer CandidateCellCertificate == Nothing
  check "ExplorationMode accepts NumericalEvidence Explorer edges" $
    case shortestRepresentationRoute ExplorationMode representationGraph
      SuzukiPositivityExplorer CandidateCellCertificate of
      Just route -> routeEndsAt route CandidateCellCertificate
      Nothing -> False
  check "KernelMode rejects numerical Suzuki branch/crossing geometry" $
    shortestRepresentationRoute KernelMode representationGraph
      SuzukiPositivityExplorer SuzukiEnvelopeCrossings == Nothing
  check "ExplorationMode accepts the Suzuki branch-to-crossing route" $
    case shortestRepresentationRoute ExplorationMode representationGraph
      SuzukiPositivityExplorer SuzukiEnvelopeCrossings of
      Just route -> routeEndsAt route SuzukiEnvelopeCrossings
      Nothing -> False
  check "Suzuki Explorer smoke scan returns both requested omega summaries" $
    case exploreSuzuki defaultExplorerOptions
        { explorerOmegas = [0, 0.5]
        , explorerTMax = 1
        , explorerSamples = 41
        } of
      Right report -> length (reportSummaries report) == 2 &&
        not (null (reportCellMinima report)) &&
        all validSuzukiSummary (reportSummaries report)
      Left _ -> False
  check "Suzuki numerical normalization has Psi(0)=0" $
    suzukiPsiNumeric 0 == 0
  check "Suzuki branch scan enumerates classified interior minima" $
    case exploreSuzuki defaultExplorerOptions
        { explorerMode = BranchesMode
        , explorerOmegas = [0, 0.05]
        , explorerTMax = 2
        , explorerSamples = 1001
        } of
      Right report -> not (null (reportCriticalPoints report)) &&
        not (null (reportBranches report)) &&
        all (\point -> length
          [other | other <- reportCriticalPoints report,
            criticalCell other == criticalCell point,
            abs (criticalOmega other - criticalOmega point) < 1e-12] == 1)
          [point | point <- reportCriticalPoints report,
            criticalCell point >= 2] &&
        all ((< 1e-3) . summaryDerivativeCheckError) (reportSummaries report)
      Left _ -> False
  check "Suzuki closed shifted derivative agrees with finite differences" $
    and
      [ let h = 1e-5
            finiteDifference =
              (psiShiftedNumeric omega (t + h) -
                psiShiftedNumeric omega (t - h)) / (2 * h)
        in abs (dPsiDt omega t - finiteDifference) < 3e-5
      | (omega, t) <- [(0, 0.46), (0.025, 1.31), (0.05, 1.78), (0.1, 0.9)]
      ]
  check "Suzuki closed shifted curvature agrees with derivative differences" $
    and
      [ let h = 1e-5
            finiteDifference =
              (dPsiDt omega (t + h) - dPsiDt omega (t - h)) / (2 * h)
        in abs (d2PsiDt2 omega t - finiteDifference) < 3e-5
      | (omega, t) <- [(0.025, 1.31), (0.05, 1.78), (0.1, 0.9)]
      ]
  check "Suzuki margin mode exposes the two-number arithmetic state" $
    case exploreSuzuki defaultExplorerOptions
        { explorerMode = MarginsMode
        , explorerOmegas = [0]
        , explorerTMax = 1.4
        , explorerSamples = 1001
        , explorerPrimeCells = True
        , explorerCellMin = Just 2
        , explorerCellMax = Just 3
        } of
      Right report ->
        map marginCell (reportMargins report) == [2, 3] &&
        all (\row -> abs (marginValue row -
          (marginIntercept row - marginDual row)) < 1e-12)
          (reportMargins report)
      Left _ -> False
  check "Suzuki block mode collapses constant Mangoldt states" $
    case exploreSuzuki defaultExplorerOptions
        { explorerMode = BlocksMode
        , explorerOmegas = [0]
        , explorerTMax = 5.71
        , explorerSamples = 1201
        , explorerPrimeCells = True
        } of
      Right report ->
        any (\row -> blockLeftEvent row == 199 &&
          blockRightEvent row == 211 && blockWinningCell row == 208 &&
          blockMinimizerType row == "interior" &&
          blockSlopeDeficitLeft row > 0 &&
          blockSlopeDeficitRight row < 0)
          (reportBlockMargins report) &&
        any (\row -> blockLeftEvent row == 13 && blockRightEvent row == 16)
          (reportBlockMargins report) &&
        any (\row -> blockLeftEvent row == 32 && blockRightEvent row == 37)
          (reportBlockMargins report)
      Left _ -> False
  check "Suzuki dual mode tracks the Lean-checked event recurrence" $
    case exploreSuzuki defaultExplorerOptions
        { explorerMode = DualMode
        , explorerOmegas = [0]
        , explorerTMin = 1.5
        , explorerTMax = 5.71
        , explorerSamples = 401
        , explorerPrimeCells = True
        } of
      Right report ->
        not (null (reportDualDynamics report)) &&
        all (\row -> abs (dualPredictedNextDeficit row -
          (dualDeficit row + dualArchDrift row - dualNextImpulse row)) < 1e-12)
          (reportDualDynamics report) &&
        all (\row -> dualLogGap row > 0 &&
          dualArchDrift row + 1e-10 >= dualLogGap row &&
          dualConvexRemainder row + 1e-10 >= dualLogGap row ^ (2 :: Int) / 2 &&
          dualSafetyEnergy row <= dualBlockMargin row + 1e-9 &&
          dualKickDisplacement row >= -1e-10 &&
          dualKickDisplacement row <= dualNextImpulse row + 1e-9 &&
          dualKickArea row >= -1e-9 &&
          dualKickArea row <= dualNextImpulse row ^ (2 :: Int) / 2 + 1e-8)
          (reportDualDynamics report) &&
        all (\(row, next) -> dualNextEvent row == dualEvent next &&
          abs (dualEventValue next -
            (dualEventValue row + dualDeficit row * dualLogGap row +
              dualConvexRemainder row)) < 1e-8 &&
          abs (dualOptimizerDisplacement next -
            (dualOptimizerDisplacement row + dualLogGap row -
              dualKickDisplacement row)) < 1e-8)
          (zip (reportDualDynamics report) (drop 1 (reportDualDynamics report))) &&
        any (\row -> dualEvent row == 199 && dualNextEvent row == 211 &&
          dualActive row && dualBlockEqualsGlobal row &&
          exp (dualOptimizer row) > 208 && exp (dualOptimizer row) < 209)
          (reportDualDynamics report)
      Left _ -> False
  check "formal Mobius-to-coefficients route is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph MobiusFormalSeries LiFormalCoefficientSequence of
      Just _ -> True
      Nothing -> False
  check "certified analytic composition route is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph XiTaylorAtOne LiFormalCoefficientSequence of
      Just _ -> True
      Nothing -> False
  check "analytic xi Taylor realization is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph XiFunction XiTaylorAtOne of
      Just _ -> True
      Nothing -> False
  check "formal-to-classical Li identification remains LiteratureCertified" $
    shortestRepresentationRoute KernelMode representationGraph LiFormalCoefficientSequence ClassicalLiSequence == Nothing
  check "analytic generating-log extraction is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph XiAfterFormalMobius LiGeneratingSequence of
      Just _ -> True
      Nothing -> False
  check "generating and normalized-original Li definitions are LeanChecked equivalent" $
    case shortestRepresentationRoute KernelMode representationGraph LiGeneratingSequence NormalizedClassicalLiSequence of
      Just _ -> True
      Nothing -> False
  check "normalization-by-2 is LeanChecked locally" $
    case shortestRepresentationRoute KernelMode representationGraph NormalizedClassicalLiSequence ClassicalLiSequence of
      Just _ -> True
      Nothing -> False
  check "generating-to-standard classical Li route is fully LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph LiGeneratingSequence ClassicalLiSequence of
      Just _ -> True
      Nothing -> False
  check "standard and normalized classical Li sequences are LeanChecked equivalent" $
    case shortestRepresentationRoute KernelMode representationGraph ClassicalLiSequence NormalizedClassicalLiSequence of
      Just _ -> True
      Nothing -> False
  check "real-valued classical Li sequence is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph ClassicalLiSequence ClassicalLiRealSequence of
      Just _ -> True
      Nothing -> False
  check "Li-to-Weil test-function corridor remains literature-only" $
    shortestRepresentationRoute KernelMode representationGraph ClassicalLiRealSequence WeilLiTestFunctions == Nothing
  check "finite Weil-Li algebra is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph WeilLiTestFunctions FiniteWeilCutoffValues of
      Just _ -> True
      Nothing -> False
  check "finite-to-infinite Weil limit is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph FiniteWeilCutoffValues WeilLiQuadraticValues of
      Just route -> routeEndsAt route WeilLiQuadraticValues
      Nothing -> False
  check "xi divisor reaches the zero-side screw kernel in kernel mode" $
    case shortestRepresentationRoute KernelMode representationGraph XiDivisor RiemannScrewKernel of
      Just _ -> True
      Nothing -> False
  check "the Riemann screw has a LeanChecked high-strip Nevanlinna transform" $
    case shortestRepresentationRoute KernelMode representationGraph RiemannScrew XiNevanlinnaTransformHighStrip of
      Just _ -> True
      Nothing -> False
  check "sampled screw-kernel positivity reaches the compact integral form" $
    case shortestRepresentationRoute KernelMode representationGraph RiemannScrewKernel IntegralScrewQuadraticForm of
      Just route -> routeEndsAt route IntegralScrewQuadraticForm
      Nothing -> False
  check "shifted eventual positivity LeanChecks a zero-free half-plane" $
    case shortestRepresentationRoute KernelMode representationGraph
        SuzukiShiftedEventualPositivitySet XiZeroFreeHalfPlane of
      Just route -> routeEndsAt route XiZeroFreeHalfPlane
      Nothing -> False
  check "zero-free to shifted eventual positivity is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph
      XiZeroFreeHalfPlane SuzukiShiftedEventualPositivitySet of
      Just route -> routeEndsAt route SuzukiShiftedEventualPositivitySet
      Nothing -> False
  check "a supplied Suzuki Gram representation evaluates to the screw kernel" $
    case shortestRepresentationRoute KernelMode representationGraph SuzukiGramKernel RiemannScrewKernel of
      Just _ -> True
      Nothing -> False
  check "xi divisor to height-ordered star partial sums is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph XiFunction LiStarPartialSums of
      Just _ -> True
      Nothing -> False
  check "height cutoff feeds finite Weil algebra in kernel mode" $
    case shortestRepresentationRoute KernelMode representationGraph XiDivisor FiniteWeilCutoffValues of
      Just _ -> True
      Nothing -> False
  check "xi affine canonical-product factorization is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph XiFunction XiAffineFactorization of
      Just _ -> True
      Nothing -> False
  check "xi occurrence partial-fraction formula is LeanChecked" $
    case shortestRepresentationRoute KernelMode representationGraph XiCanonicalProduct XiLogDerivPartialFraction of
      Just _ -> True
      Nothing -> False
  check "star convergence remains outside kernel mode" $
    shortestRepresentationRoute KernelMode representationGraph LiStarPartialSums LiStarConvergence == Nothing
  check "classical Li coefficients equal negative-index star limits in kernel mode" $
    case shortestRepresentationRoute KernelMode representationGraph ClassicalLiSequence LiStarConvergence of
      Just _ -> True
      Nothing -> False
  check "local count conditionally reduces to star convergence in kernel mode" $
    case shortestRepresentationRoute KernelMode representationGraph XiLocalZeroCountBound LiStarConvergence of
      Just _ -> True
      Nothing -> False
  check "radial cutoff is not the authoritative star-partial route" $
    shortestRepresentationRoute KernelMode representationGraph XiRadialZeroCutoff LiStarPartialSums == Nothing
  let evidence = checkLagariasPrefix 100
  check "finite Lagarias result remains Evidence, not Proof" $
    checkedThrough evidence == 100 && not (submissionReady (Nothing :: Maybe (Proof 'RH)))
  check "both representation routes converge on LiSequence" liRoutesConverge
  check "submission remains negative without a kernel proof term" $
    not (submissionReady (Nothing :: Maybe (Proof 'RH)))
  putStrLn "All rh-garden tests passed."

check :: String -> Bool -> IO ()
check label condition = unless condition $ do
  putStrLn ("FAILED: " ++ label)
  exitFailure

quotientDerivativeTest :: Bool
quotientDerivativeTest =
  case (rationalFunction variable (add (constant 1) variable),
        rationalFunction (constant 1) (multiply denominatorPolynomial denominatorPolynomial)) of
    (Just value, Just expected) ->
      equalByCrossMultiplication (differentiateRational value) expected
    _ -> False
  where
    denominatorPolynomial = add (constant 1) variable

liRoutesConverge :: Bool
liRoutesConverge =
  case ( shortestRepresentationRoute LiteratureMode representationGraph XiFunction LogXiMobius
       , shortestRepresentationRoute LiteratureMode representationGraph LogXiMobius LiSequence
       , shortestRepresentationRoute LiteratureMode representationGraph XiFunction XiZeros
       , shortestRepresentationRoute LiteratureMode representationGraph XiZeros LiSequence
       ) of
    (Just _, Just generated, Just _, Just zeroFormula) ->
      routeEndsAt generated LiSequence && routeEndsAt zeroFormula LiSequence
    _ -> False

routeEndsAt :: RepresentationRoute -> Representation -> Bool
routeEndsAt route expected =
  case reverse (representationRouteSteps route) of
    edge:_ -> rreTo edge == expected
    [] -> False

validSuzukiSummary :: OmegaSummary -> Bool
validSuzukiSummary summary =
  not (isNaN (summaryMinimum summary)) &&
  not (isInfinite (summaryMinimum summary)) &&
  summaryCrossCheckError summary < 0.01
