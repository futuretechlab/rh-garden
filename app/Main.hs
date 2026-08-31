{-# LANGUAGE DataKinds #-}

module Main (main) where

import System.Environment (getArgs)
import Text.Read (readMaybe)

import RHGarden.Core
import RHGarden.Evidence
import RHGarden.Mobius
import RHGarden.Registry
import RHGarden.Representation
import RHGarden.Search

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> overview
    ["kernel"] -> routes KernelMode certifiedGraph
    ["routes"] -> routes LiteratureMode certifiedGraph
    ["explore"] -> routes ExplorationMode explorationGraph
    ["check-lagarias", nText] ->
      case readMaybe nText of
        Just n | n >= 1 -> putStrLn . renderLagariasCheck $ checkLagariasPrefix n
        _ -> usage
    ["submission"] -> submissionStatus
    ["formal-status"] -> formalStatus
    ["garden"] -> garden LiteratureMode
    ["check-mobius"] -> putStr renderMobiusCheck
    ["path", fromText, toText] -> representationPath LiteratureMode fromText toText
    _ -> usage

overview :: IO ()
overview = do
  putStrLn "RH Garden v0.1.0"
  putStrLn "================"
  putStrLn "A typed representation-graph proof-search scaffold for RH."
  putStrLn ""
  putStrLn "Current invariant: KernelMode admits only LeanChecked reductions."
  putStrLn "Finite numerical checks are evidence only and cannot discharge a universal criterion."
  putStrLn ""
  putStrLn "Try:"
  putStrLn "  rh-garden kernel"
  putStrLn "  rh-garden routes"
  putStrLn "  rh-garden explore"
  putStrLn "  rh-garden check-lagarias 10000"
  putStrLn "  rh-garden check-mobius"
  putStrLn "  rh-garden garden"
  putStrLn "  rh-garden path XiFunction LiSequence"
  putStrLn "  rh-garden submission"
  putStrLn "  rh-garden formal-status"
  putStrLn ""
  submissionStatus

routes :: SearchMode -> [RuntimeReduction] -> IO ()
routes mode graph = do
  putStrLn $ "Search mode: " ++ show mode
  mapM_ (showTarget mode graph) targets
  where
    targets =
      [ XiZerosReal
      , XiRiemannHypothesis
      , LiPositive
      , NymanBeurlingDense
      , LagariasInequality
      , SelfAdjointXiRealization
      ]

showTarget :: SearchMode -> [RuntimeReduction] -> Criterion -> IO ()
showTarget mode graph target = do
  putStrLn ""
  putStrLn $ "Target viewpoint: " ++ criterionLabel target
  case shortestRoute mode graph RH target of
    Nothing -> putStrLn "  no admissible route registered"
    Just r -> putStrLn (renderRoute RH r)

submissionStatus :: IO ()
submissionStatus = do
  putStrLn "Submission status"
  putStrLn "-----------------"
  putStrLn "NO PROOF OF RH IS CLAIMED."
  putStrLn "The program currently certifies route bookkeeping, not the missing mathematical theorem."
  putStrLn "The Mobius derivative has an ExactExecutable finite algebra certificate, but it does not discharge RH."
  case shortestRoute KernelMode certifiedGraph RH LiPositive of
    Nothing -> putStrLn "No complete LeanChecked route from RH to a discharged universal theorem exists."
    Just _ -> putStrLn "A kernel-only bookkeeping route exists, but no discharged kernel theorem is registered; submission remains negative."
  if submissionReady (Nothing :: Maybe (Proof 'RH))
    then putStrLn "Kernel proof term present."
    else putStrLn "Kernel proof term absent."
  putStrLn ""
  putStrLn "Open proof frontiers already represented in the graph:"
  putStrLn "  1. LiPositive: prove lambda_n >= 0 for every n >= 1."
  putStrLn "  2. NymanBeurlingDense: prove the required L2 closure/density statement."
  putStrLn "  3. LagariasInequality: prove the divisor-sum inequality for every n >= 1."
  putStrLn "  4. SelfAdjointXiRealization: explicitly construct and certify the Hilbert-Polya operator."
  putStrLn ""
  putStrLn "A publishable proof requires at least one frontier to be discharged by a finite, auditable proof term."

formalStatus :: IO ()
formalStatus = do
  putStrLn "Formal theorem registry (navigation metadata only)"
  putStrLn "--------------------------------------------------"
  putStrLn "Authoritative check: run `lake build` in formal/."
  mapM_ (putStrLn . ("  LeanChecked: RHGarden." ++))
    [ "riemannXi_zero"
    , "riemannXi_one"
    , "differentiable_riemannXi"
    , "riemannXi_one_sub"
    , "riemannXi_eq_completedRiemannZeta"
    , "liMobius_eq_one_sub_liStandard"
    , "riemannXi_liMobius_eq_liStandard"
    , "XiT_neg"
    , "riemannZeta_eq_zero_of_riemannXi_eq_zero"
    , "gamma_half_add_one_ne_zero_of_nontrivial"
    , "zetaXiDenominator_ne_zero_of_nontrivial"
    , "zetaXiNumerator_eq_zero_of_riemannZeta_eq_zero"
    , "two_mul_riemannXi_eq_mul_zetaXiNumerator"
    , "riemannXi_eq_zero_of_nontrivial_riemannZeta_zero"
    , "IsNontrivialZetaZero.riemannXi_eq_zero"
    , "riemannHypothesis_iff_nontrivialZero_re"
    , "completedRiemannZeta_ne_zero_of_riemannZeta_ne_zero"
    , "riemannXi_pos_odd_ne_zero"
    , "riemannXi_trivialZetaPoint_ne_zero"
    , "isNontrivialZetaZero_of_riemannXi_eq_zero"
    , "riemannXi_eq_zero_iff_nontrivialZetaZero"
    , "riemannHypothesis_iff_xiRiemannHypothesis"
    , "xiRiemannHypothesis_iff_XiTZerosReal"
    , "riemannHypothesis_iff_XiTZerosReal"
    , "liMobiusSeries_constantCoeff"
    , "liMobiusSeries_coeff"
    , "one_add_liMobiusSeries_eq_inv_one_sub_X"
    , "normalizedXiTaylor_constantCoeff"
    , "differentiable_normalizedXiAtOne"
    , "analyticAt_normalizedXiAtOne"
    , "normalizedXiAtOne_hasFPowerSeriesAt"
    , "normalizedXiFPowerSeries_coeff"
    , "normalizedXiTaylor_hasSum"
    , "analyticAt_liMobius"
    , "analyticAt_analyticLiXi"
    , "liMobiusFPowerSeries_coeff_zero"
    , "liMobiusFPowerSeries_coeff_succ"
    , "liMobiusFPowerSeries_coeff_eq_powerSeries"
    , "liMobius_hasFPowerSeriesAt"
    , "analyticLiXi_hasFPowerSeriesAt_comp"
    , "analyticLiXiFMS_eq_derivativeTaylor"
    , "analyticLiXiPowerSeries_coeff"
    , "analyticLiXiPowerSeries_constantCoeff"
    , "analyticLiXiPowerSeries_isUnit"
    , "analyticLiXiPowerSeries_mul_inv"
    , "certifiedLiXiSeries_hasSum"
    , "normalizedXi_one"
    , "normalizedXiAtOne_zero"
    , "analyticLiXi_zero"
    , "analyticAt_liLocalLog"
    , "analyticAt_liGeneratingLog"
    , "liLocalLog_zero"
    , "liGeneratingLog_zero"
    , "deriv_liGeneratingLog_zero"
    , "normalizedClassicalLiCoefficient_eq_shifted"
    , "liLocalLogTaylor_constantCoeff"
    , "liLocalLog_hasFPowerSeriesAt"
    , "liLocalLogFPowerSeries_coeff"
    , "liGeneratingLog_hasFPowerSeriesAt_comp"
    , "liGeneratingLogFMS_eq_derivativeTaylor"
    , "liGeneratingCoefficient_eq_succ_mul_fms_coeff"
    , "coeff_liMobiusSeries_pow"
    , "coeff_one_add_X_pow"
    , "coeff_subst_liMobius_eq_coeff_one_add_pow_mul"
    , "liGeneratingFunctional_eq_liOriginalFunctional"
    , "card_composition_succ_length_succ"
    , "sum_composition_by_length"
    , "coeff_comp_liMobiusFMS"
    , "coeff_subst_liMobius_binomial"
    , "coeff_comp_liMobiusFMS_eq_subst"
    , "liGeneratingLogFPowerSeries_coeff_eq_subst"
    , "liGeneratingCoefficient_eq_shiftedClassical"
    , "liGeneratingCoefficient_eq_normalizedClassical"
    , "liXiSeries_eq_certifiedLiXiSeries"
    , "riemannXi_one_ne_zero"
    , "riemannXi_one_mem_slitPlane"
    , "analyticAt_standardXiLog"
    , "analyticAt_log_normalizedXi"
    , "analyticAt_logNormalizationDifference"
    , "eventually_deriv_log_normalizedXi_eq_standardXiLog"
    , "deriv_log_normalizedXi_eq_standardXiLog"
    , "eventually_log_normalizedXi_eq_standardXiLog_add_const"
    , "eventuallyEq_logNormalizationDifference_const"
    , "iteratedDeriv_log_normalizedXi_eq_standardXiLog"
    , "iteratedDeriv_const_mul_pow_succ_eq_zero"
    , "normalizedClassicalLiCoefficient_eq_classical"
    , "liGeneratingCoefficient_eq_classical"
    , "riemannXi_conj"
    , "eventually_standardXiLog_conj"
    , "iteratedDeriv_standardXiLog_conj"
    , "iteratedDeriv_standardXiLog_im_eq_zero"
    , "classicalLiCoefficient_conj"
    , "classicalLiCoefficient_im_eq_zero"
    , "classicalLiCoefficient_eq_real"
    , "weilLiTest_zero_index"
    , "weilLiTest_one_index"
    , "weilLiTest_neg"
    , "weilLiTest_mul_neg"
    , "conj_weilLiTest_weilReflect"
    , "finiteWeilScalar_liTest"
    , "finiteWeilScalar_liTest_self"
    , "finiteLiZeroValue_neg_eq_conj"
    , "finiteWeilScalar_liTest_self_eq_two_re"
    , "liXiSeries_constantCoeff"
    , "liXiSeries_isUnit"
    , "liXiSeries_mul_inv"
    , "cubicLiFormalCoefficient_zero"
    , "cubicLiFormalCoefficient_one"
    , "cubicLiFormalCoefficient_two"
    ]
  putStrLn "  ExactExecutable: Mobius derivative (Haskell Rational checker)"
  putStrLn "This command reads static metadata; it does not validate or promote a theorem."

usage :: IO ()
usage = do
  putStrLn "usage: rh-garden [kernel | routes | explore | garden | path FROM TO | check-mobius | check-lagarias N | formal-status | submission]"

garden :: SearchMode -> IO ()
garden mode = do
  putStrLn $ "Representation garden (" ++ show mode ++ ")"
  putStrLn "Edges classify representation changes separately from proof reductions."
  mapM_ renderEdge representationGraph
  putStrLn ""
  putStrLn "Route A: transformed log-xi generating function"
  case routeThroughGeneratingSeries mode of
    Nothing -> putStrLn "  no admissible route registered"
    Just route -> putStr (renderRepresentationRoute XiFunction route)
  putStrLn "Route B: zero multiset / Li zero formula"
  case routeThroughZeros mode of
    Nothing -> putStrLn "  no admissible route registered"
    Just route -> putStr (renderRepresentationRoute XiFunction route)
  where
    renderEdge edge = putStrLn $
      "  " ++ show (rreFrom edge) ++ " --[" ++ show (rreKind edge) ++ ", " ++
      show (rreTrust edge) ++ "]--> " ++ show (rreTo edge)

routeThroughZeros :: SearchMode -> Maybe RepresentationRoute
routeThroughZeros mode = do
  first <- shortestRepresentationRoute mode representationGraph XiFunction XiZeros
  second <- shortestRepresentationRoute mode representationGraph XiZeros LiSequence
  pure (RepresentationRoute
    (representationRouteCost first + representationRouteCost second)
    (representationRouteSteps first ++ representationRouteSteps second))

routeThroughGeneratingSeries :: SearchMode -> Maybe RepresentationRoute
routeThroughGeneratingSeries mode = do
  first <- shortestRepresentationRoute mode representationGraph XiFunction LogXiMobius
  second <- shortestRepresentationRoute mode representationGraph LogXiMobius LiSequence
  pure (RepresentationRoute
    (representationRouteCost first + representationRouteCost second)
    (representationRouteSteps first ++ representationRouteSteps second))

showRepresentationRoute :: SearchMode -> Representation -> Representation -> IO ()
showRepresentationRoute mode fromRepresentation toRepresentation =
  case shortestRepresentationRoute mode representationGraph fromRepresentation toRepresentation of
    Nothing -> putStrLn "  no admissible route registered"
    Just route -> putStr (renderRepresentationRoute fromRepresentation route)

representationPath :: SearchMode -> String -> String -> IO ()
representationPath mode fromText toText =
  case (readRepresentation fromText, readRepresentation toText) of
    (Just fromRepresentation, Just toRepresentation) ->
      showRepresentationRoute mode fromRepresentation toRepresentation
    _ -> do
      putStrLn "Unknown representation name. Known names are:"
      putStrLn $ "  " ++ unwords (map show ([minBound .. maxBound] :: [Representation]))

readRepresentation :: String -> Maybe Representation
readRepresentation text =
  case reads text of
    [(value, "")] -> Just value
    _ -> Nothing
