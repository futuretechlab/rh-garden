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
      , WeilLiPositive
      , WeilFormPSD
      , ScrewKernelPSD
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
  putStrLn "  2. WeilLiPositive: equivalently prove nonnegativity on every Li-test diagonal."
  putStrLn "  3. WeilFormPSD: prove positive semidefiniteness on the full Weil test space."
  putStrLn "  4. ScrewKernelPSD converse: formalize Suzuki's recovery of critical-line reality."
  putStrLn "  5. NymanBeurlingDense: prove the required L2 closure/density statement."
  putStrLn "  6. LagariasInequality: prove the divisor-sum inequality for every n >= 1."
  putStrLn "  7. SelfAdjointXiRealization: explicitly construct and certify the Hilbert-Polya operator."
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
    , "analyticAt_riemannXi"
    , "meromorphicOn_riemannXi"
    , "analyticOrderAt_riemannXi_ne_top"
    , "xiDivisor_nonneg"
    , "xiMultiplicity_cast"
    , "xiDivisor_ne_zero_iff"
    , "mem_xiDivisor_support_iff_nontrivialZetaZero"
    , "xiZeroSupportInClosedBall_finite"
    , "count_xiZeroRadialCutoff"
    , "xiZeroRadialCutoff_valid"
    , "riemannXi_zero_re_mem_Ioo"
    , "xiZeroSupportInHeightStrip_finite"
    , "count_xiZeroHeightCutoff"
    , "xiZeroHeightCutoff_valid"
    , "weilReflect_im"
    , "abs_im_weilReflect"
    , "iteratedDeriv_riemannXi_conj"
    , "analyticOrderNatAt_riemannXi_conj"
    , "xiMultiplicity_conj"
    , "xiMultiplicity_one_sub"
    , "xiMultiplicity_weilReflect"
    , "xiZeroHeightCutoff_reflectionStable"
    , "finiteWeilScalar_heightCutoff_self_eq_two_re"
    , "norm_weilReflect_sub_norm_le_one"
    , "completedZeta_order_eq_zeta_order"
    , "analyticOrderAt_riemannXi_eq_completedZeta"
    , "xiMultiplicity_eq_zetaMultiplicity"
    , "isNontrivialZetaZero_iff_zeta_zero_re_mem_Ioo"
    , "xiZeroSupportInHeightWindow_finite"
    , "count_xiZeroHeightWindowCutoff"
    , "xiHeightWindowMultiplicityCount_eq_sum"
    , "xiHeightWindowMultiplicityCount_eq_zeta"
    , "xi_reciprocal_sq_summable"
    , "xi_reciprocal_pow_summable"
    , "xiZeroHeightCutoff_conjStable"
    , "reciprocalStarPartial_conj"
    , "abs_reciprocal_re_le_sq"
    , "reciprocalStarPartial_sub_norm_le"
    , "exists_reciprocalStarLimit"
    , "weilLiTest_nat_expansion"
    , "reciprocalPowPartial_tendsto"
    , "liStarPartial_neg"
    , "LiStarConvergesTo.neg"
    , "exists_liStarLimit_nat"
    , "exists_liStarLimit_neg_nat"
    , "liStarConvergence_of_localZeroCount"
    , "xiLocalZeroCountBound"
    , "liStarConvergence"
    , "norm_Complex_Gamma_le_Real_Gamma_re"
    , "Real.Gamma_le_one_add_ceil_pow"
    , "Real.Gamma_coarse_exp_bound"
    , "norm_GammaR_coarse"
    , "riemannXi_coarse_growth_right"
    , "riemannXi_coarse_growth_global"
    , "one_add_mul_log_le_four_rpow_three_halves"
    , "riemannXi_subquadratic_growth"
    , "zeroFreeEntire_eq_exp_entire"
    , "subquadraticGrowth_specialize_seven_fourths"
    , "re_entireLog_le_of_exp_growth"
    , "norm_centered_entireLog_le"
    , "iteratedDeriv_two_eq_zero_of_re_growth"
    , "entire_eq_affine_of_iteratedDeriv_two_eq_zero"
    , "subquadratic_zeroFree_entire_is_exp_affine"
    , "subquadraticZeroFreeEntireIsExpAffine"
    , "analyticOrderNatAt_xiCanonicalProductOccurrences"
    , "meromorphicOrderAt_xiRawQuotient"
    , "differentiable_xiZeroFreeQuotient"
    , "xiZeroFreeQuotient_ne_zero"
    , "riemannXi_eq_zeroFreeQuotient_mul_canonicalProduct"
    , "riemannXi_eq_exp_affine_mul_canonicalProduct_of_quotient_growth"
    , "primaryFactorOne_zero"
    , "primaryFactorOne_eq_zero_iff"
    , "primaryFactorOne_ne_zero_iff"
    , "differentiable_primaryFactorOne_div"
    , "differentiable_finitePrimaryProduct"
    , "logDeriv_primaryFactorOne_div"
    , "finitePrimaryProduct_ne_zero"
    , "logDeriv_finitePrimaryProduct"
    , "finiteLogDerivLiJet_eq_finiteLiZeroValue"
    , "differentiable_xiPrimaryFactor"
    , "analyticAt_xiPrimaryFactor"
    , "xiPrimaryFactor_zero"
    , "xiPrimaryFactor_ne_zero"
    , "xiCanonicalProduct_zero"
    , "differentiable_xiCanonicalProduct"
    , "differentiable_xiOccurrencePrimaryFactor"
    , "analyticAt_xiOccurrencePrimaryFactor"
    , "xiOccurrencePrimaryFactor_zero"
    , "xiOccurrencePrimaryFactor_ne_zero"
    , "xi_reciprocal_sq_summable_unconditional"
    , "xiOccurrence_reciprocal_sq_summable"
    , "xiOccurrence_reciprocal_three_halves_summable"
    , "norm_primaryFactorOne_sub_one_le"
    , "xiOccurrencePrimaryDelta_summableLocallyUniformly"
    , "xiOccurrencePrimaryFactors_multipliableLocallyUniformly"
    , "xiCanonicalProductOccurrences_zero"
    , "differentiable_xiCanonicalProductOccurrences"
    , "xiCanonicalProductOccurrences_ne_zero"
    , "logDeriv_xiOccurrencePrimaryFactor"
    , "summable_logDeriv_xiOccurrencePrimaryFactor"
    , "logDeriv_xiCanonicalProductOccurrences"
    , "posLog_norm_primaryFactorOne_le_three_halves"
    , "xiCanonicalProductOccurrences_growth_three_halves"
    , "logCounting_top_eq_zero_of_differentiable"
    , "characteristic_top_le_of_entire_exp_growth"
    , "riemannXi_characteristic_subquadratic"
    , "xiCanonicalProductOccurrences_characteristic_three_halves"
    , "characteristic_inv_xiCanonicalProductOccurrences_eq"
    , "inv_xiCanonicalProductOccurrences_characteristic_three_halves"
    , "xiRawQuotient_eventuallyEq_xiZeroFreeQuotient"
    , "characteristic_xiZeroFreeQuotient_eq_xiRawQuotient"
    , "characteristic_xiRawQuotient_le_add"
    , "characteristic_xiZeroFreeQuotient_le"
    , "xiZeroFreeQuotient_eq_exp_entire"
    , "re_entireLog_xiZeroFreeQuotient_eq_log_norm"
    , "re_entireLog_xiZeroFreeQuotient_le_three_mul_characteristic"
    , "xiQuotient_subquadratic_growth"
    , "riemannXi_eq_exp_affine_mul_canonicalProduct"
    , "logDeriv_xiCanonicalProductOccurrences_zero"
    , "logDeriv_exp_affine"
    , "riemannXi_eq_half_mul_exp_logDeriv_zero_mul_canonicalProduct"
    , "logDeriv_riemannXi_eq_zero_value_add_zero_sum"
    , "xiLogDerivPartialFractionOccurrences"
    , "deriv_riemannXi_one_eq_neg_deriv_zero"
    , "logDeriv_riemannXi_one_eq_neg_zero"
    , "xiCorrectedPartialFraction_one_tendsto"
    , "xiCorrectedPartialFraction_one_eq_two_mul_reciprocalStarPartial"
    , "reciprocalStarPartial_tendsto_neg_logDeriv_zero"
    , "xiCorrectedOccurrence_summableLocallyUniformlyOn"
    , "xiCorrectedPartialFraction_tendstoLocallyUniformlyOn"
    , "xiCorrectedPartialFraction_tendstoLocallyUniformlyOn_logDeriv_sub_zero"
    , "xiPartialFraction_tendstoLocallyUniformlyOn_logDeriv"
    , "iteratedDeriv_xiPartialFraction_tendstoLocallyUniformlyOn"
    , "iteratedDeriv_xiPartialFraction_tendsto"
    , "logDerivLiJet_xiPartialFraction_eq_finiteLogDerivLiJet"
    , "logDerivLiJet_logDeriv_riemannXi_eq_classicalLiCoefficient"
    , "logDerivLiJet_xiPartialFraction_tendsto"
    , "finiteLogDerivLiJet_tendsto_classicalLiCoefficient"
    , "classicalLiEqualsNegativeStar"
    , "classicalLiEqualsPositiveStar"
    , "classicalLiSigned_neg"
    , "liStarConvergesTo_classicalLiSigned"
    , "norm_weilLiTest_le_inv_norm"
    , "summable_weilLiScalarTerm"
    , "tendsto_heightCutoff_sum_of_summable"
    , "finiteWeilScalar_heightCutoff_tendsto"
    , "weilLiScalar_eq_classicalLiSigned"
    , "weilLiScalar_conj_symm"
    , "weilLiScalar_self"
    , "weilLiScalar_self_nat"
    , "weilLiQuadraticValue_eq_two_li"
    , "liPositive_iff_weilLiPositive"
    , "xiZero_eq_half_sub_I_mul_spectral"
    , "riemannXi_half_sub_I_mul_spectral_eq_zero"
    , "xiSpectralParameter_ne_zero_iff_value_ne_half"
    , "xiSpectralParameter_ne_zero_of_midpoint"
    , "xiTZerosReal_iff_spectralParameters_real"
    , "half_norm_value_le_norm_xiSpectralParameter"
    , "xiSpectral_reciprocal_sq_summable"
    , "summable_suzukiPsiZero_term"
    , "suzukiPsiZero_zero"
    , "suzukiPsiZero_conj"
    , "suzukiPsiZero_neg"
    , "riemannScrewKernel_hermitian"
    , "summable_suzukiKernelTerm"
    , "riemannScrewKernel_eq_zero_sum"
    , "riemannScrewKernel_eq_gram_of_XiTZerosReal"
    , "riemannScrewKernelHeight_tendsto"
    , "riemannScrewKernelHeight_psd_of_XiTZerosReal"
    , "riemannScrewKernel_psd_of_XiTZerosReal"
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
