{-# LANGUAGE DataKinds #-}

module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)

import RHGarden.Algebra
import RHGarden.Core
import RHGarden.Evidence
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
  check "LiteratureMode rejects Conjectural edges" $
    shortestRepresentationRoute LiteratureMode representationExplorationGraph WeilQuadraticValues LiSequence == Nothing
  check "ExplorationMode accepts Conjectural edges" $
    case shortestRepresentationRoute ExplorationMode representationExplorationGraph WeilQuadraticValues LiSequence of
      Just _ -> True
      Nothing -> False
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
  check "finite-to-infinite Weil limit remains literature-only" $
    shortestRepresentationRoute KernelMode representationGraph FiniteWeilCutoffValues WeilQuadraticValues == Nothing
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
