{-# LANGUAGE DataKinds #-}

module RHGarden.Registry
  ( certifiedGraph
  , explorationGraph
  , representationGraph
  , representationExplorationGraph
  ) where

import RHGarden.Core
import RHGarden.Representation

liRef :: Reference
liRef = Reference
  { refShort = "Li 1997 / Lagarias 2004"
  , refCitation =
      "X.-J. Li, The positivity of a sequence of numbers and the Riemann hypothesis, " ++
      "J. Number Theory 65 (1997), 325-333; see also J. C. Lagarias, " ++
      "Li coefficients for automorphic L-functions (2004/2005)."
  }

nymanRef :: Reference
nymanRef = Reference
  { refShort = "Nyman-Beurling / Baez-Duarte 2002"
  , refCitation =
      "Nyman-Beurling criterion; L. Baez-Duarte, A strengthening of the " ++
      "Nyman-Beurling criterion for the Riemann Hypothesis, 2002."
  }

lagariasRef :: Reference
lagariasRef = Reference
  { refShort = "Lagarias 2002"
  , refCitation =
      "J. C. Lagarias, An elementary problem equivalent to the Riemann hypothesis, " ++
      "Amer. Math. Monthly 109 (2002), 534-543."
  }

xiRef :: Reference
xiRef = Reference
  { refShort = "Riemann xi completion"
  , refCitation =
      "Definition of xi(s)=1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s), together " ++
      "with the fact that the nontrivial zeros of zeta are precisely the zeros of xi."
  }

hilbertPolyaRef :: Reference
hilbertPolyaRef = Reference
  { refShort = "Hilbert-Polya spectral strategy"
  , refCitation =
      "Classical Hilbert-Polya strategy; see J. B. Conrey, The Riemann Hypothesis, " ++
      "Notices AMS 50 (2003), 341-353."
  }

formalXiRef :: Reference
formalXiRef = Reference
  { refShort = "RHGarden.riemannHypothesis_iff_xiRiemannHypothesis"
  , refCitation = "Lean theorem in formal/RHGarden/ZetaZeros.lean; lake build is authoritative."
  }

formalXiTRef :: Reference
formalXiTRef = Reference
  { refShort = "RHGarden.xiRiemannHypothesis_iff_XiTZerosReal"
  , refCitation = "Lean theorem in formal/RHGarden/CriticalLine.lean; lake build is authoritative."
  }

rhToXiHypothesis :: RuntimeReduction
rhToXiHypothesis = eraseReduction $ leanEquiv
  SRH SXiRiemannHypothesis
  "mathlib RH iff entire-xi zero formulation"
  1 formalXiRef
  "LeanChecked equivalence of open propositions; this does not prove or discharge either proposition."

xiHypothesisToRh :: RuntimeReduction
xiHypothesisToRh = eraseReduction $ leanEquiv
  SXiRiemannHypothesis SRH
  "entire-xi zero formulation iff mathlib RH"
  1 formalXiRef
  "Reverse use of the same LeanChecked equivalence; neither endpoint is discharged."

xiHypothesisToXiT :: RuntimeReduction
xiHypothesisToXiT = eraseReduction $ leanEquiv
  SXiRiemannHypothesis SXiZerosReal
  "rotate entire-xi zeros to the XiT coordinate"
  1 formalXiTRef
  "LeanChecked coordinate equivalence between two open propositions."

xiTToXiHypothesis :: RuntimeReduction
xiTToXiHypothesis = eraseReduction $ leanEquiv
  SXiZerosReal SXiRiemannHypothesis
  "undo the XiT critical-line coordinate"
  1 formalXiTRef
  "Reverse use of the LeanChecked coordinate equivalence; no proposition is discharged."

rhToLi :: RuntimeReduction
rhToLi = eraseReduction $ literatureEquiv
  SRH SLiPositive
  "Li positivity criterion"
  2 liRef
  "Replace a zero-location statement by positivity of every Li coefficient."

liToRh :: RuntimeReduction
liToRh = eraseReduction $ literatureEquiv
  SLiPositive SRH
  "Li positivity criterion (reverse)"
  2 liRef
  "Nonnegativity of all Li coefficients is necessary and sufficient for RH."

rhToNyman :: RuntimeReduction
rhToNyman = eraseReduction $ literatureEquiv
  SRH SNymanBeurlingDense
  "Nyman-Beurling criterion"
  4 nymanRef
  "Replace zero location by a density/closure problem in an L2 function space."

nymanToRh :: RuntimeReduction
nymanToRh = eraseReduction $ literatureEquiv
  SNymanBeurlingDense SRH
  "Nyman-Beurling criterion (reverse)"
  4 nymanRef
  "The closure property is equivalent to RH."

rhToLagarias :: RuntimeReduction
rhToLagarias = eraseReduction $ literatureEquiv
  SRH SLagariasInequality
  "Lagarias elementary inequality"
  3 lagariasRef
  "Replace RH by sigma(n) <= H_n + exp(H_n) log(H_n) for every positive integer n."

lagariasToRh :: RuntimeReduction
lagariasToRh = eraseReduction $ literatureEquiv
  SLagariasInequality SRH
  "Lagarias elementary inequality (reverse)"
  3 lagariasRef
  "The universal divisor-sum inequality is equivalent to RH."

-- Goal-reduction direction: to prove Xi-real-zero criterion, it is sufficient
-- to construct the required self-adjoint realization.  Self-adjoint spectra are
-- real; the hard part is the exact spectral correspondence.
xiToSelfAdjoint :: RuntimeReduction
xiToSelfAdjoint = eraseReduction $ literatureSufficient
  SXiZerosReal SSelfAdjointXiRealization
  "Hilbert-Polya reduction"
  2 hilbertPolyaRef
  "A self-adjoint operator with spectrum exactly equal to the Xi zero ordinates would force those ordinates to be real."

-- This is deliberately conjectural.  It represents a future candidate bridge,
-- not a theorem.  It is kept out of proof mode by construction.
selfAdjointToNyman :: RuntimeReduction
selfAdjointToNyman = eraseReduction $ conjecturalReduction
  SSelfAdjointXiRealization SNymanBeurlingDense
  "candidate spectral/functional-analytic bridge"
  SufficientCondition
  8
  (Reference
    { refShort = "UNPROVED RESEARCH EDGE"
    , refCitation = "No literature theorem is registered for this edge."
    })
  "Placeholder for discovering a concrete operator from Nyman-Beurling geometry. It cannot appear in a certified proof."

certifiedGraph :: [RuntimeReduction]
certifiedGraph =
  [ rhToXiHypothesis, xiHypothesisToRh
  , xiHypothesisToXiT, xiTToXiHypothesis
  , rhToLi, liToRh
  , rhToNyman, nymanToRh
  , rhToLagarias, lagariasToRh
  , xiToSelfAdjoint
  ]

explorationGraph :: [RuntimeReduction]
explorationGraph = certifiedGraph ++ [selfAdjointToNyman]

mobiusRef :: Reference
mobiusRef = Reference
  { refShort = "RHGarden.riemannXi_liMobius_eq_liStandard"
  , refCitation = "Lean theorem in formal/RHGarden/Mobius.lean; lake build is authoritative."
  }

liGeneratingRef :: Reference
liGeneratingRef = Reference
  { refShort = "Li 1997, generating-function convention"
  , refCitation =
      "X.-J. Li, J. Number Theory 65 (1997), using phi(z)=xi(-z/(1-z)) " ++
      "and d/dz log phi(z)=sum_{n>=1} lambda_n z^(n-1)."
  }

liZeroRef :: Reference
liZeroRef = Reference
  { refShort = "Li zero-sum formula"
  , refCitation =
      "Li's coefficients satisfy lambda_n=sum_rho[1-(1-1/rho)^n], with zeros " ++
      "and summation interpreted under the standard analytic hypotheses and limiting convention."
  }

weilRef :: Reference
weilRef = Reference
  { refShort = "Lagarias, Li coefficients and Weil functional"
  , refCitation =
      "J. C. Lagarias, Li coefficients for automorphic L-functions, Ann. Inst. Fourier 57 (2007), Section 3, equations (3.1)--(3.4)."
  }

liFormalRef :: Reference
liFormalRef = Reference
  { refShort = "RHGarden.LiFormal"
  , refCitation = "Lean definitions and theorems in formal/RHGarden/LiFormal.lean; lake build is authoritative."
  }

liClassicalRef :: Reference
liClassicalRef = Reference
  { refShort = "RHGarden Li formalization"
  , refCitation = "Lean definitions and theorems in formal/RHGarden/LiClassical.lean, LiCombinatorics.lean, LiComposition.lean, and LiNormalization.lean; lake build is authoritative."
  }

xiCutoffRef :: Reference
xiCutoffRef = Reference
  { refShort = "RHGarden.XiZeroCutoff"
  , refCitation = "Lean divisor, multiplicity, radial/height cutoffs, zeta/xi multiplicity adapters, and height-window counts in formal/RHGarden/XiZeroCutoff.lean and ZetaMultiplicity.lean; lake build is authoritative."
  }

classicalLiIdentityRef :: Reference
classicalLiIdentityRef = Reference
  { refShort = "Li 1997 logarithmic-derivative identity"
  , refCitation =
      "d/dz log xi(1/(1-z)) = sum_{n>=0} lambda_(n+1) z^n. " ++
      "Equality with RHGarden's independently constructed formal coefficients is not yet formalized."
  }

xiMobius :: RuntimeRepresentationEdge
xiMobius = eraseRepresentationEdge $ representationEdge
  SXiFunction SXiAfterMobius "Mobius substitution in xi"
  ExactRepresentation leanCheckedTrust 1 mobiusRef
  "Lean checks xi(-z/(1-z)) = xi(1/(1-z)) for z != 1 using the xi functional equation."
  (ExactInverse "s=m(z) is involutive: z=m(s), away from the pole in the rational coordinate.")
  Nothing

mobiusCoordinate :: RuntimeRepresentationEdge
mobiusCoordinate = eraseRepresentationEdge $ representationEdge
  SMobiusVariable SXiAfterMobius "use Mobius coordinate as xi argument"
  ExactRepresentation exactExecutableTrust 1
  (Reference "RHGarden.Mobius exact algebra" "Finite Haskell Rational computation; not a Lean proof artifact.")
  "The XiAfterMobius syntax records m(z) as the argument of xi."
  (NoReconstruction "This edge supplies a coordinate to a composite object; xi is separate input.")
  Nothing

phiLogDerivative :: RuntimeRepresentationEdge
phiLogDerivative = eraseRepresentationEdge $ representationEdge
  SXiAfterMobius SLogXiMobius "logarithmic derivative"
  InformationLoss literatureCertifiedTrust 2 liGeneratingRef
  "Form d/dz log(phi(z)); analytic domain and nonvanishing hypotheses are literature obligations."
  (ReconstructionUpTo "Recovering phi from its logarithmic derivative requires integration, a multiplicative constant, and analytic hypotheses.")
  Nothing

logToSeries :: RuntimeRepresentationEdge
logToSeries = eraseRepresentationEdge $ representationEdge
  SLogXiMobius SLiGeneratingSeries "Li generating identity"
  EquivalentTheorem literatureCertifiedTrust 2 liGeneratingRef
  "Identify d/dz log(phi(z)) with sum_{n>=1} lambda_n z^(n-1)."
  (ExactInverse "A convergent power series is reconstructed from its ordered coefficients inside its domain of convergence.")
  Nothing

seriesToSequence :: RuntimeRepresentationEdge
seriesToSequence = eraseRepresentationEdge $ representationEdge
  SLiGeneratingSeries SLiSequence "Taylor coefficient extraction"
  ExactRepresentation literatureCertifiedTrust 1 liGeneratingRef
  "Extract coefficient of z^(n-1) as lambda_n for every n>=1."
  (ExactInverse "Reassemble sum_{n>=1} lambda_n z^(n-1), subject to the registered analytic convergence theorem.")
  Nothing

xiToZeros :: RuntimeRepresentationEdge
xiToZeros = eraseRepresentationEdge $ representationEdge
  SXiFunction SXiZeros "take zero multiset"
  InformationLoss literatureCertifiedTrust 2 xiRef
  "Record the nontrivial zeros with multiplicity."
  (ReconstructionUpTo "Hadamard reconstruction needs order, normalization, exponential factors, and analytic hypotheses.")
  Nothing

xiToDivisor :: RuntimeRepresentationEdge
xiToDivisor = eraseRepresentationEdge $ representationEdge
  SXiFunction SXiDivisor "form the entire xi divisor"
  ExactRepresentation leanCheckedTrust 1 xiCutoffRef
  "RHGarden.xiDivisor uses MeromorphicOn.divisor; support and values encode zeros with analytic multiplicity."
  (NoReconstruction "The divisor records zero data, not the normalized entire function.")
  Nothing

divisorToRadialCutoff :: RuntimeRepresentationEdge
divisorToRadialCutoff = eraseRepresentationEdge $ representationEdge
  SXiDivisor SXiRadialZeroCutoff "restrict divisor to |rho|<=T"
  ExactRepresentation leanCheckedTrust 1 xiCutoffRef
  "RHGarden.xiZeroRadialCutoff repeats every supported point by xiMultiplicity; count_xiZeroRadialCutoff verifies the exact radial count."
  (NoReconstruction "A single bounded cutoff does not reconstruct the global divisor.")
  Nothing

divisorToHeightCutoff :: RuntimeRepresentationEdge
divisorToHeightCutoff = eraseRepresentationEdge $ representationEdge
  SXiDivisor SXiHeightZeroCutoff "restrict divisor to |Im rho|<=T"
  ExactRepresentation leanCheckedTrust 1 xiCutoffRef
  "RHGarden.xiZeroHeightCutoff is Lagarias's multiplicity-aware height ordering; its support is finite by the unconditional critical-strip bound."
  (NoReconstruction "A single bounded-height cutoff does not reconstruct the global divisor.")
  Nothing

heightCutoffToStarPartial :: RuntimeRepresentationEdge
heightCutoffToStarPartial = eraseRepresentationEdge $ representationEdge
  SXiHeightZeroCutoff SLiStarPartialSums "evaluate Lagarias height-ordered Li sums"
  ExactRepresentation leanCheckedTrust 1 xiCutoffRef
  "RHGarden.liStarPartial is finiteLiZeroValue on the genuine multiplicity-aware height cutoff."
  (ExactInverse "The indexed partial-sum object retains its cutoff parameter and integer index.")
  Nothing

heightCutoffToFiniteWeil :: RuntimeRepresentationEdge
heightCutoffToFiniteWeil = eraseRepresentationEdge $ representationEdge
  SXiHeightZeroCutoff SFiniteWeilCutoffValues "apply finite Weil-Li algebra to height cutoffs"
  ExactRepresentation leanCheckedTrust 1 xiCutoffRef
  "RHGarden.xiZeroHeightCutoff_valid and xiZeroHeightCutoff_reflectionStable instantiate the finite diagonal 2Re identity."
  (NoReconstruction "Finite scalar values do not reconstruct the cutoff multiset.")
  Nothing

starPartialToConvergence :: RuntimeRepresentationEdge
starPartialToConvergence = eraseRepresentationEdge $ representationEdge
  SLiStarPartialSums SLiStarConvergence "prove height-ordered star convergence"
  EquivalentTheorem literatureCertifiedTrust 5 weilRef
  "LiStarConvergesTo is defined as Tendsto atTop; no convergence theorem is registered."
  (ExactInverse "A proved convergence proposition identifies the limit of the full partial-sum net.")
  Nothing

classicalLiToStarConvergence :: RuntimeRepresentationEdge
classicalLiToStarConvergence = eraseRepresentationEdge $ representationEdge
  SClassicalLiSequence SLiStarConvergence "derivative Li equals negative-index star limit"
  EquivalentTheorem literatureCertifiedTrust 5 weilRef
  "ClassicalLiEqualsNegativeStar records the exact open target with index -(k+1)."
  (ExactInverse "The target identifies each derivative coefficient with its star limit.")
  Nothing

starConvergenceToWeil :: RuntimeRepresentationEdge
starConvergenceToWeil = eraseRepresentationEdge $ representationEdge
  SLiStarConvergence SWeilQuadraticValues "pass star identities to the infinite Weil functional"
  EquivalentTheorem literatureCertifiedTrust 5 weilRef
  "Requires separate conditional Li and absolute Weil convergence control."
  (NoReconstruction "Convergence values alone do not reconstruct the full Weil form.")
  Nothing

nontrivialZetaZeroToXiZero :: RuntimeRepresentationEdge
nontrivialZetaZeroToXiZero = eraseRepresentationEdge $ representationEdge
  SNontrivialZetaZero SXiZero "nontrivial zeta zero gives xi zero"
  EquivalentTheorem leanCheckedTrust 1
  (Reference
    "RHGarden.riemannXi_eq_zero_iff_nontrivialZetaZero"
    "Lean theorem in formal/RHGarden/ZetaZeros.lean; lake build is authoritative.")
  "Forward direction of the global LeanChecked pointwise zero equivalence."
  (ExactInverse "The reverse direction is registered as a separate directed edge.")
  Nothing

xiZeroToNontrivialZetaZero :: RuntimeRepresentationEdge
xiZeroToNontrivialZetaZero = eraseRepresentationEdge $ representationEdge
  SXiZero SNontrivialZetaZero "xi zero is a nontrivial zeta zero"
  EquivalentTheorem leanCheckedTrust 1
  (Reference
    "RHGarden.riemannXi_eq_zero_iff_nontrivialZetaZero"
    "Lean theorem in formal/RHGarden/ZetaZeros.lean; lake build is authoritative.")
  "Reverse direction, including xi nonvanishing at 0, 1, and every trivial zeta-zero location."
  (ExactInverse "The forward direction is registered as a separate directed edge.")
  Nothing

zerosToLi :: RuntimeRepresentationEdge
zerosToLi = eraseRepresentationEdge $ representationEdge
  SXiZeros SLiSequence "Li zero-sum formula"
  EquivalentTheorem literatureCertifiedTrust 2 liZeroRef
  "lambda_n=sum_rho [1-(1-1/rho)^n], n>=1, in the standard limiting sense."
  (NoReconstruction "The registered edge does not claim that the Li sequence uniquely reconstructs the zero multiset.")
  Nothing

realLiToZeroSum :: RuntimeRepresentationEdge
realLiToZeroSum = eraseRepresentationEdge $ representationEdge
  SClassicalLiRealSequence SLiZeroSumSequence "derivative Li equals star-convergent zero-sum Li"
  EquivalentTheorem literatureCertifiedTrust 3 weilRef
  "Identify the derivative-defined coefficient with the conditionally star-convergent zero sum; this analytic bridge is not LeanChecked."
  (ExactInverse "The literature theorem identifies the indexed values once its convergence convention is formalized.")
  Nothing

zeroSumToFiniteCutoffs :: RuntimeRepresentationEdge
zeroSumToFiniteCutoffs = eraseRepresentationEdge $ representationEdge
  SLiZeroSumSequence SFiniteWeilCutoffValues "choose multiplicity-preserving finite zero cutoffs"
  InformationLoss literatureCertifiedTrust 2 weilRef
  "A concrete cofinal family of cutoffs and its relation to star convergence remains to be formalized."
  (NoReconstruction "One finite cutoff cannot reconstruct a conditional infinite zero sum.")
  Nothing

weilTestsToFiniteValues :: RuntimeRepresentationEdge
weilTestsToFiniteValues = eraseRepresentationEdge $ representationEdge
  SWeilLiTestFunctions SFiniteWeilCutoffValues "finite Lagarias identities"
  ExactRepresentation leanCheckedTrust 1 liClassicalRef
  "RHGarden.finiteWeilScalar_liTest proves (3.3) for every valid finite Multiset cutoff; no convergence or positivity is used."
  (NoReconstruction "The output also depends on the chosen finite zero multiset.")
  Nothing

finiteCutoffsToWeil :: RuntimeRepresentationEdge
finiteCutoffsToWeil = eraseRepresentationEdge $ representationEdge
  SFiniteWeilCutoffValues SWeilQuadraticValues "pass finite cutoffs to the infinite Weil scalar"
  EquivalentTheorem literatureCertifiedTrust 4 weilRef
  "Requires absolute convergence of the Weil scalar and limit control; the finite Lean theorem does not prove this step."
  (ReconstructionUpTo "The infinite value is a controlled limit of a specified cofinal cutoff family.")
  Nothing

xiToTaylorData :: RuntimeRepresentationEdge
xiToTaylorData = eraseRepresentationEdge $ representationEdge
  SXiFunction SXiTaylorAtOne "analytic xi Taylor realization at s=1"
  ExactRepresentation leanCheckedTrust 2 liFormalRef
  "RHGarden.normalizedXiAtOne_hasFPowerSeriesAt certifies local convergence; RHGarden.normalizedXiFPowerSeries_coeff identifies its scalar coefficients with normalizedXiTaylor."
  (NoReconstruction "The certificate is local analytic realization; the bare PowerSeries object itself carries no convergence data.")
  Nothing

mobiusToFormalSeries :: RuntimeRepresentationEdge
mobiusToFormalSeries = eraseRepresentationEdge $ representationEdge
  SMobiusVariable SMobiusFormalSeries "expand z/(1-z) as a formal series"
  ExactRepresentation leanCheckedTrust 1 liFormalRef
  "RHGarden.liMobiusSeries has coefficient 0 at degree zero and coefficient 1 at every positive degree."
  (ExactInverse "Lean checks 1+U=(1-X)^(-1); this is formal algebra, not convergence.")
  Nothing

formalTaylorComposition :: RuntimeRepresentationEdge
formalTaylorComposition = eraseRepresentationEdge $ representationEdge
  SXiTaylorAtOne SXiAfterFormalMobius "compose certified analytic germs"
  ExactRepresentation leanCheckedTrust 1 liFormalRef
  "RHGarden.analyticLiXi_hasFPowerSeriesAt_comp certifies FMS composition; certifiedLiXiSeries adapts those coefficients to PowerSeries and sums locally to analyticLiXi."
  (NoReconstruction "This local analytic germ certificate does not identify the coefficients with independently defined classical Li coefficients.")
  Nothing

formalMobiusCompositionInput :: RuntimeRepresentationEdge
formalMobiusCompositionInput = eraseRepresentationEdge $ representationEdge
  SMobiusFormalSeries SXiAfterFormalMobius "use U as formal substitution input"
  ExactRepresentation leanCheckedTrust 1 liFormalRef
  "The explicit liMobiusFPowerSeries has coefficients 0,1,1,..., agrees coefficientwise with liMobiusSeries, and has a HasFPowerSeriesAt certificate."
  (NoReconstruction "The older PowerSeries.subst encoding remains separate; equality with the certified FMS adapter is not registered as proved.")
  Nothing

formalLogDerivative :: RuntimeRepresentationEdge
formalLogDerivative = eraseRepresentationEdge $ representationEdge
  SXiAfterFormalMobius SLiFormalLogDerivative "formal logarithmic derivative"
  ExactRepresentation leanCheckedTrust 1 liFormalRef
  "Form derivative(G) * G^(-1) from certifiedLiXiSeries; Lean checks constantCoeff G=1 and G*G^(-1)=1."
  (ReconstructionUpTo "A logarithmic derivative determines a unit series only up to its fixed constant; no analytic log is used.")
  Nothing

formalCoefficientExtraction :: RuntimeRepresentationEdge
formalCoefficientExtraction = eraseRepresentationEdge $ representationEdge
  SLiFormalLogDerivative SLiFormalCoefficientSequence "formal coefficient extraction"
  ExactRepresentation leanCheckedTrust 1 liFormalRef
  "Define certifiedLiFormalCoefficient n as coefficient n of the certified formal logarithmic derivative; classical lambda_(n+1) identification remains separate."
  (ExactInverse "A formal power series is extensionally determined by all coefficients.")
  Nothing

formalToClassicalLi :: RuntimeRepresentationEdge
formalToClassicalLi = eraseRepresentationEdge $ representationEdge
  SLiFormalCoefficientSequence SClassicalLiSequence "identify formal coefficients with classical Li coefficients"
  EquivalentTheorem literatureCertifiedTrust 3 classicalLiIdentityRef
  "This analytic identity is not LeanChecked; classical Li coefficients remain conceptually independent."
  (ExactInverse "Would follow from a proved generating-series equality with matching indexing.")
  Nothing

certifiedXiToGeneratingLog :: RuntimeRepresentationEdge
certifiedXiToGeneratingLog = eraseRepresentationEdge $ representationEdge
  SXiAfterFormalMobius SLiGeneratingLog "take the local analytic logarithm"
  ExactRepresentation leanCheckedTrust 1 liClassicalRef
  "RHGarden.analyticAt_liGeneratingLog checks the principal-log germ at zero, where analyticLiXi(0)=1."
  (ReconstructionUpTo "Only a local logarithm germ is asserted; no global logarithm or branch identity is registered.")
  Nothing

generatingLogToSequence :: RuntimeRepresentationEdge
generatingLogToSequence = eraseRepresentationEdge $ representationEdge
  SLiGeneratingLog SLiGeneratingSequence "extract generating-log derivatives"
  ExactRepresentation leanCheckedTrust 1 liClassicalRef
  "Define liGeneratingCoefficient n from the (n+1)-st derivative at zero, independently of the formal G'/G sequence."
  (NoReconstruction "The registered edge extracts the complete derivative sequence but does not assert a global analytic reconstruction.")
  Nothing

generatingToNormalizedClassical :: RuntimeRepresentationEdge
generatingToNormalizedClassical = eraseRepresentationEdge $ representationEdge
  SLiGeneratingSequence SNormalizedClassicalLiSequence "Li generating/original derivative identity"
  EquivalentTheorem leanCheckedTrust 2 classicalLiIdentityRef
  "RHGarden.liGeneratingCoefficient_eq_normalizedClassical proves coefficientwise equality via the specialized Mobius FMS/PowerSeries adapter."
  (ExactInverse "Both sequences have the same indexed coefficients by a Lean-checked theorem.")
  Nothing

normalizedToClassicalLi :: RuntimeRepresentationEdge
normalizedToClassicalLi = eraseRepresentationEdge $ representationEdge
  SNormalizedClassicalLiSequence SClassicalLiSequence "remove the xi normalization factor 2"
  EquivalentTheorem leanCheckedTrust 1 liClassicalRef
  "RHGarden.normalizedClassicalLiCoefficient_eq_classical proves coefficientwise equality using local logarithmic derivatives and a locally constant difference."
  (ExactInverse "Both independently defined sequences have the same indexed coefficients by a Lean-checked theorem.")
  Nothing

classicalToNormalizedLi :: RuntimeRepresentationEdge
classicalToNormalizedLi = eraseRepresentationEdge $ representationEdge
  SClassicalLiSequence SNormalizedClassicalLiSequence "restore the xi normalization factor 2"
  EquivalentTheorem leanCheckedTrust 1 liClassicalRef
  "Reverse orientation of RHGarden.normalizedClassicalLiCoefficient_eq_classical."
  (ExactInverse "Both independently defined sequences have the same indexed coefficients by a Lean-checked theorem.")
  Nothing

classicalLiToReal :: RuntimeRepresentationEdge
classicalLiToReal = eraseRepresentationEdge $ representationEdge
  SClassicalLiSequence SClassicalLiRealSequence "take the proved real classical Li sequence"
  EquivalentTheorem leanCheckedTrust 1 liClassicalRef
  "RHGarden.classicalLiCoefficient_eq_real proves coefficientwise equality with the complex embedding of classicalLiRealCoefficient."
  (ExactInverse "The complex coefficient is exactly the real coefficient embedded into C.")
  Nothing

negativeToStandardMobiusXi :: RuntimeRepresentationEdge
negativeToStandardMobiusXi = eraseRepresentationEdge $ representationEdge
  SNegativeMobiusXi SStandardLiMobiusXi "xi symmetry identifies Mobius conventions"
  EquivalentTheorem leanCheckedTrust 1 mobiusRef
  "Lean checks xi(-z/(1-z))=xi(1/(1-z)) for z!=1."
  (ExactInverse "Equality is symmetric.")
  Nothing

standardToNegativeMobiusXi :: RuntimeRepresentationEdge
standardToNegativeMobiusXi = eraseRepresentationEdge $ representationEdge
  SStandardLiMobiusXi SNegativeMobiusXi "xi symmetry identifies Mobius conventions (reverse)"
  EquivalentTheorem leanCheckedTrust 1 mobiusRef
  "Reverse orientation of the same Lean theorem."
  (ExactInverse "Equality is symmetric.")
  Nothing

conjecturalPositiveFactorization :: RuntimeRepresentationEdge
conjecturalPositiveFactorization = eraseRepresentationEdge $ representationEdge
  SWeilQuadraticValues SLiSequence "candidate positive Gram factorization"
  ConjecturalBridge conjecturalTrust 8
  (Reference "UNPROVED RESEARCH EDGE" "No positive operator or norm-square factorization is currently proved.")
  "Seek lambda_n=||T v_n||^2 without assuming RH."
  (NoReconstruction "No transform exists until the conjectural factorization is constructed and proved.")
  (Just (PropertyTransport WeilFormNonnegative AllLiCoefficientsNonnegative
    "A proved norm-square identity would transport positivity, but this statement is currently conjectural."))

representationGraph :: [RuntimeRepresentationEdge]
representationGraph =
  [ xiMobius, mobiusCoordinate, phiLogDerivative, logToSeries, seriesToSequence
  , xiToZeros, xiToDivisor, divisorToRadialCutoff, divisorToHeightCutoff
  , heightCutoffToStarPartial, heightCutoffToFiniteWeil, starPartialToConvergence
  , classicalLiToStarConvergence, starConvergenceToWeil
  , nontrivialZetaZeroToXiZero, xiZeroToNontrivialZetaZero
  , zerosToLi, realLiToZeroSum, zeroSumToFiniteCutoffs
  , weilTestsToFiniteValues, finiteCutoffsToWeil
  , xiToTaylorData, mobiusToFormalSeries, formalTaylorComposition
  , formalMobiusCompositionInput, formalLogDerivative, formalCoefficientExtraction
  , formalToClassicalLi, certifiedXiToGeneratingLog, generatingLogToSequence
  , generatingToNormalizedClassical, normalizedToClassicalLi, classicalToNormalizedLi
  , classicalLiToReal
  , negativeToStandardMobiusXi, standardToNegativeMobiusXi
  ]

representationExplorationGraph :: [RuntimeRepresentationEdge]
representationExplorationGraph = representationGraph ++ [conjecturalPositiveFactorization]
