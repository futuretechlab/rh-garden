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
  check "normalization-by-2 remains a separate literature boundary" $
    shortestRepresentationRoute KernelMode representationGraph NormalizedClassicalLiSequence ClassicalLiSequence == Nothing
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
