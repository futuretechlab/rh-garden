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

suzukiScrewRef :: Reference
suzukiScrewRef = Reference
  { refShort = "RHGarden.riemannScrewKernel_psd_of_XiTZerosReal"
  , refCitation =
      "Lean theorem in formal/RHGarden/SuzukiScrew.lean; the zero-side kernel identity, " ++
      "critical-line Gram expansion, finite-matrix PSD proof, and spectral-denominator " ++
      "nonvanishing are kernel checked."
  }

suzukiConverseRef :: Reference
suzukiConverseRef = Reference
  { refShort = "RHGarden.XiTZerosReal_of_suzukiPsi_nonneg"
  , refCitation =
      "Lean theorems in formal/RHGarden/SuzukiPointwise.lean; the all-moment " ++
      "Landau boundary argument, analytic continuation, pointwise Suzuki criterion, " ++
      "and specialized screw-kernel converse are kernel checked."
  }

xiNevanlinnaRef :: Reference
xiNevanlinnaRef = Reference
  { refShort = "RHGarden.xiTZerosReal_iff_xiNevanlinna"
  , refCitation =
      "Lean theorems in formal/RHGarden/XiNevanlinna.lean: the corrected centered " ++
      "spectral partial fraction, both directions of the xi Nevanlinna criterion, " ++
      "screw continuity, and the high-strip Fourier-Laplace transform are kernel checked."
  }

suzukiPointwiseRef :: Reference
suzukiPointwiseRef = Reference
  { refShort = "RHGarden.suzukiPsi_nonnegative_of_kernelPSD"
  , refCitation =
      "Lean theorems in formal/RHGarden/SuzukiPointwise.lean: Q_xi oddness, " ++
      "the normalized Psi Laplace transform, the screw-kernel diagonal, " ++
      "positive-real-axis xi nonvanishing, all Laplace moments and derivatives, " ++
      "Tonelli exponential summation, and the Landau boundary principle are kernel checked."
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

screwPSDFromXiT :: RuntimeReduction
screwPSDFromXiT = eraseReduction $ leanSufficient
  SScrewKernelPSD SXiZerosReal
  "critical-line spectral parameters give a positive screw kernel"
  1 suzukiScrewRef
  "RHGarden.riemannScrewKernel_psd_of_XiTZerosReal rewrites the zero-side kernel as an occurrence-indexed Gram sum and passes finite-cutoff positivity to the limit."

suzukiPsiNonnegativeFromScrewPSD :: RuntimeReduction
suzukiPsiNonnegativeFromScrewPSD = eraseReduction $ leanSufficient
  SSuzukiPsiNonnegative SScrewKernelPSD
  "the screw-kernel diagonal is twice Suzuki's Psi"
  1 suzukiPointwiseRef
  "RHGarden.riemannScrewKernel_self and RHGarden.suzukiPsi_nonnegative_of_kernelPSD are LeanChecked."

xiTFromSuzukiPsiNonnegative :: RuntimeReduction
xiTFromSuzukiPsiNonnegative = eraseReduction $ leanSufficient
  SXiZerosReal SSuzukiPsiNonnegative
  "Suzuki pointwise positivity criterion via Landau's Laplace boundary theorem"
  1 suzukiConverseRef
  "RHGarden.XiTZerosReal_of_suzukiPsi_nonneg is LeanChecked. It is a conditional criterion and does not prove pointwise positivity."

xiNevanlinnaFromXiT :: RuntimeReduction
xiNevanlinnaFromXiT = eraseReduction $ leanEquiv
  SXiNevanlinnaFunction SXiZerosReal
  "critical-line spectral sum makes Q_xi Nevanlinna"
  1 xiNevanlinnaRef
  "RHGarden.xiNevanlinna_of_XiTZerosReal is LeanChecked; it does not prove either open endpoint."

xiTFromXiNevanlinna :: RuntimeReduction
xiTFromXiNevanlinna = eraseReduction $ leanEquiv
  SXiZerosReal SXiNevanlinnaFunction
  "upper-half-plane analyticity excludes nonreal xi spectral zeros"
  1 xiNevanlinnaRef
  "RHGarden.XiTZerosReal_of_xiNevanlinna uses analytic order at arbitrary-multiplicity zeros."

screwFunctionFromKernelPSD :: RuntimeReduction
screwFunctionFromKernelPSD = eraseReduction $ leanEquiv
  SScrewFunction SScrewKernelPSD
  "continuous normalized Riemann screw function reduces to kernel PSD"
  1 xiNevanlinnaRef
  "RHGarden.riemannScrew_isScrew_iff_kernelPSD discharges continuity, normalization, and Hermitian symmetry."

kernelPSDFromScrewFunction :: RuntimeReduction
kernelPSDFromScrewFunction = eraseReduction $ leanEquiv
  SScrewKernelPSD SScrewFunction
  "Suzuki screw-function axioms include kernel PSD"
  1 xiNevanlinnaRef
  "Reverse direction of the same LeanChecked equivalence of open propositions."

xiNevanlinnaFromScrewFunction :: RuntimeReduction
xiNevanlinnaFromScrewFunction = eraseReduction $ leanSufficient
  SXiNevanlinnaFunction SScrewFunction
  "specialized Suzuki pointwise/Landau bridge"
  1 suzukiConverseRef
  "The LeanChecked composition is ScrewFunction -> KernelPSD -> Psi>=0 -> Landau -> XiTZerosReal -> XiNevanlinna. It is specialized to the Riemann screw function, not a general Krein--Langer theorem."

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

liToWeilLiPositive :: RuntimeReduction
liToWeilLiPositive = eraseReduction $ leanEquiv
  SLiPositive SWeilLiPositive
  "Li positivity iff positivity of the Li-test Weil diagonal"
  1 liWeilInfiniteRef
  "RHGarden.liPositive_iff_weilLiPositive uses W(G_n,G_n)=2*lambda_n; it proves an equivalence of open propositions only."

weilLiPositiveToLi :: RuntimeReduction
weilLiPositiveToLi = eraseReduction $ leanEquiv
  SWeilLiPositive SLiPositive
  "positivity of the Li-test Weil diagonal iff Li positivity"
  1 liWeilInfiniteRef
  "Reverse direction of the same LeanChecked coefficientwise identity; full Weil-form PSD is a distinct, stronger future criterion."

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
  , screwPSDFromXiT, suzukiPsiNonnegativeFromScrewPSD
  , xiTFromSuzukiPsiNonnegative
  , xiNevanlinnaFromXiT, xiTFromXiNevanlinna
  , screwFunctionFromKernelPSD, kernelPSDFromScrewFunction
  , xiNevanlinnaFromScrewFunction
  , rhToLi, liToRh, liToWeilLiPositive, weilLiPositiveToLi
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

liStarConditionalRef :: Reference
liStarConditionalRef = Reference
  { refShort = "RHGarden.LiStarConvergence"
  , refCitation = "Lean theorems in formal/RHGarden/LiStarConvergence.lean and Zeta23LocalCount.lean; the local count premise is discharged by the pinned Zeta23 theorem."
  }

xiCanonicalProductRef :: Reference
xiCanonicalProductRef = Reference
  { refShort = "RHGarden.LiHadamardInfinite"
  , refCitation = "Lean occurrence-indexed canonical-product convergence and logarithmic-derivative theorems in formal/RHGarden/LiHadamardInfinite.lean; lake build is authoritative."
  }

xiQuotientGrowthRef :: Reference
xiQuotientGrowthRef = Reference
  { refShort = "RHGarden.LiQuotientGrowth"
  , refCitation = "Lean primary-factor, Nevanlinna-characteristic, Poisson, quotient-growth, normalized affine-factorization, and exact xi partial-fraction theorems in formal/RHGarden/LiQuotientGrowth.lean; lake build is authoritative."
  }

liStarIdentificationRef :: Reference
liStarIdentificationRef = Reference
  { refShort = "RHGarden.LiStarIdentification"
  , refCitation = "Lean reciprocal-star limit, locally uniform xi partial-fraction convergence, finite Li-jet transport, and classicalLiEqualsNegativeStar in formal/RHGarden/LiStarIdentification.lean; lake build is authoritative."
  }

liWeilInfiniteRef :: Reference
liWeilInfiniteRef = Reference
  { refShort = "RHGarden.LiWeilInfinite"
  , refCitation = "Lean absolute Weil-summability, height-cutoff exhaustion, infinite Lagarias (3.3), diagonal (3.4), and Li/Weil-Li positivity-equivalence theorems in formal/RHGarden/LiWeilInfinite.lean; lake build is authoritative."
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

xiToSubquadraticGrowth :: RuntimeRepresentationEdge
xiToSubquadraticGrowth = eraseRepresentationEdge $ representationEdge
  SXiFunction SXiSubquadraticGrowth "prove coarse global growth below order two"
  InformationLoss leanCheckedTrust 2
  (Reference "RHGarden.riemannXi_subquadratic_growth"
    "Lean theorem in formal/RHGarden/LiHadamardGrowth.lean; lake build is authoritative.")
  "Euler's integral reduces complex Gamma to real Gamma; a ceiling/factorial bound and xi symmetry yield order at most 3/2."
  (NoReconstruction "A growth bound is a property of xi and does not reconstruct the function.")
  Nothing

subquadraticZeroFreeToExpAffine :: RuntimeRepresentationEdge
subquadraticZeroFreeToExpAffine = eraseRepresentationEdge $ representationEdge
  SZeroFreeEntireSubquadratic SExpAffineEntire
  "integrate H'/H and apply Borel-Caratheodory plus Cauchy's estimate"
  SufficientReduction leanCheckedTrust 2
  (Reference "RHGarden.subquadraticZeroFreeEntireIsExpAffine"
    "Generic Lean theorem in formal/RHGarden/LiExpAffine.lean; lake build is authoritative.")
  "At exponent 7/4, the Cauchy bound forces the second derivative of the global entire logarithm to vanish."
  (ExactInverse "The theorem supplies constants A and B with H(z)=exp(A+Bz).")
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

divisorToOccurrences :: RuntimeRepresentationEdge
divisorToOccurrences = eraseRepresentationEdge $ representationEdge
  SXiDivisor SXiZeroOccurrences "expand analytic multiplicities into zero occurrences"
  ExactRepresentation leanCheckedTrust 1 xiCanonicalProductRef
  "XiZeroOccurrence is the dependent sum of each supported xi zero with Fin xiMultiplicity."
  (ExactInverse "Regroup each finite occurrence fiber to recover the divisor multiplicity.")
  Nothing

occurrencesToCanonicalProduct :: RuntimeRepresentationEdge
occurrencesToCanonicalProduct = eraseRepresentationEdge $ representationEdge
  SXiZeroOccurrences SXiCanonicalProduct "form the locally uniform genus-one occurrence product"
  SufficientReduction leanCheckedTrust 1 xiCanonicalProductRef
  "xiOccurrencePrimaryFactors_multipliableLocallyUniformly uses reciprocal-square summability and the E1 quadratic estimate."
  (NoReconstruction "The canonical product alone does not retain a chosen occurrence labeling.")
  Nothing

canonicalProductToLogDerivative :: RuntimeRepresentationEdge
canonicalProductToLogDerivative = eraseRepresentationEdge $ representationEdge
  SXiCanonicalProduct SXiCanonicalProductLogDerivative "take the canonical-product logarithmic derivative"
  ExactRepresentation leanCheckedTrust 1 xiCanonicalProductRef
  "logDeriv_xiCanonicalProductOccurrences gives the exact occurrence-indexed partial-fraction tsum away from xi zeros."
  (ReconstructionUpTo "A logarithmic derivative reconstructs a nonzero entire function up to a multiplicative constant on a connected domain.")
  Nothing

xiAndCanonicalProductToZeroFreeQuotient :: RuntimeRepresentationEdge
xiAndCanonicalProductToZeroFreeQuotient = eraseRepresentationEdge $ representationEdge
  SXiCanonicalProduct SXiZeroFreeQuotient "remove the common xi divisor"
  SufficientReduction leanCheckedTrust 2 xiCanonicalProductRef
  "RHGarden.xiZeroFreeQuotient is the canonical meromorphic normal-form extension; its order is zero everywhere."
  (ExactInverse "RHGarden.riemannXi_eq_zeroFreeQuotient_mul_canonicalProduct reconstructs xi globally.")
  Nothing

zeroFreeQuotientToGrowth :: RuntimeRepresentationEdge
zeroFreeQuotientToGrowth = eraseRepresentationEdge $ representationEdge
  SXiZeroFreeQuotient SXiQuotientSubquadraticGrowth "prove quotient subquadratic growth"
  InformationLoss leanCheckedTrust 3 xiQuotientGrowthRef
  "RHGarden.xiQuotient_subquadratic_growth uses Nevanlinna characteristic bounds and Poisson's formula to prove the pointwise bound."
  (NoReconstruction "A growth bound does not reconstruct the quotient.")
  Nothing

quotientGrowthToAffineFactorization :: RuntimeRepresentationEdge
quotientGrowthToAffineFactorization = eraseRepresentationEdge $ representationEdge
  SXiQuotientSubquadraticGrowth SXiAffineFactorization "apply the generic exp-affine theorem"
  SufficientReduction leanCheckedTrust 1 xiQuotientGrowthRef
  "RHGarden.riemannXi_eq_half_mul_exp_logDeriv_zero_mul_canonicalProduct is the unconditional normalized genus-one Hadamard representation."
  (ExactInverse "The conclusion fixes the constant factor at 1/2 and the linear coefficient at logDeriv riemannXi 0.")
  Nothing

canonicalProductToXiLogDerivPartialFraction :: RuntimeRepresentationEdge
canonicalProductToXiLogDerivPartialFraction = eraseRepresentationEdge $ representationEdge
  SXiCanonicalProduct SXiLogDerivPartialFraction
  "normalize the affine factor and take the xi logarithmic derivative"
  SufficientReduction leanCheckedTrust 1 xiQuotientGrowthRef
  "RHGarden.xiLogDerivPartialFractionOccurrences discharges XiLogDerivPartialFractionOccurrences with B = logDeriv riemannXi 0."
  (ReconstructionUpTo "The logarithmic derivative determines xi up to a nonzero multiplicative constant; the normalized factorization separately fixes xi(0)=1/2.")
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

localCountToReciprocalSquare :: RuntimeRepresentationEdge
localCountToReciprocalSquare = eraseRepresentationEdge $ representationEdge
  SXiLocalZeroCountBound SReciprocalSquareSummability
  "derive reciprocal-square summability from unit-window counts"
  SufficientReduction leanCheckedTrust 1 liStarConditionalRef
  "xi_reciprocal_sq_summable is checked with XiLocalZeroCountBound as an explicit premise."
  (NoReconstruction "Summability does not recover a local zero-count estimate.")
  Nothing

reciprocalSquareToStar :: RuntimeRepresentationEdge
reciprocalSquareToStar = eraseRepresentationEdge $ representationEdge
  SReciprocalSquareSummability SReciprocalStarConvergence
  "use conjugation pairing and critical-strip bounds"
  SufficientReduction leanCheckedTrust 1 liStarConditionalRef
  "The reciprocal shell is real and dominated by the reciprocal-square tail."
  (NoReconstruction "First-moment convergence does not recover the local count.")
  Nothing

localCountToLiStar :: RuntimeRepresentationEdge
localCountToLiStar = eraseRepresentationEdge $ representationEdge
  SXiLocalZeroCountBound SLiStarConvergence
  "derive every integer-indexed Li star limit"
  SufficientReduction leanCheckedTrust 1 liStarConditionalRef
  "liStarConvergence_of_localZeroCount combines pairing, higher powers, binomial expansion, and reflection."
  (NoReconstruction "Existence of the limits does not recover the local count bound.")
  Nothing

classicalLiToStarConvergence :: RuntimeRepresentationEdge
classicalLiToStarConvergence = eraseRepresentationEdge $ representationEdge
  SClassicalLiSequence SLiStarConvergence "derivative Li equals negative-index star limit"
  EquivalentTheorem leanCheckedTrust 1 liStarIdentificationRef
  "RHGarden.classicalLiEqualsNegativeStar identifies each zero-based classical coefficient with the exact height-ordered star limit at index -(k+1)."
  (ExactInverse "The target identifies each derivative coefficient with its star limit.")
  Nothing

starConvergenceToWeil :: RuntimeRepresentationEdge
starConvergenceToWeil = eraseRepresentationEdge $ representationEdge
  SLiStarConvergence SWeilLiQuadraticValues "pass star identities to the infinite Weil-Li scalar"
  EquivalentTheorem leanCheckedTrust 1 liWeilInfiniteRef
  "RHGarden.weilLiScalar_eq_classicalLiSigned combines ordinary absolute convergence on the Weil side with the three signed Li star limits."
  (NoReconstruction "Convergence values alone do not reconstruct the full Weil form.")
  Nothing

divisorToXiSpectral :: RuntimeRepresentationEdge
divisorToXiSpectral = eraseRepresentationEdge $ representationEdge
  SXiDivisor SXiSpectralParameters "rotate xi zeros to Suzuki spectral coordinates"
  ExactRepresentation leanCheckedTrust 1 suzukiScrewRef
  "RHGarden.xiZero_eq_half_sub_I_mul_spectral and the coordinate formulas identify gamma=i(rho-1/2), preserving analytic multiplicity occurrences."
  (ExactInverse "Recover rho as 1/2-I*gamma occurrence by occurrence.")
  Nothing

xiSpectralToSuzukiPsi :: RuntimeRepresentationEdge
xiSpectralToSuzukiPsi = eraseRepresentationEdge $ representationEdge
  SXiSpectralParameters SSuzukiPsiZeroSide "sum the reciprocal-square Suzuki zero expansion"
  ExactRepresentation leanCheckedTrust 1 suzukiScrewRef
  "RHGarden.xiSpectral_reciprocal_sq_summable and summable_suzukiPsiZero_term prove the occurrence-indexed series converges absolutely for each real t; RHGarden.xiSpectralParameter_ne_zero proves every displayed denominator is nonzero."
  (NoReconstruction "The summed function does not by itself reconstruct the labelled spectral divisor.")
  Nothing

suzukiPsiToRiemannScrew :: RuntimeRepresentationEdge
suzukiPsiToRiemannScrew = eraseRepresentationEdge $ representationEdge
  SSuzukiPsiZeroSide SRiemannScrew "take g=-Psi and prove compact-local normal convergence"
  ExactRepresentation leanCheckedTrust 1 xiNevanlinnaRef
  "RHGarden.continuous_suzukiPsiZero and continuous_riemannScrew prove the zero-side sum is a continuous real-even screw candidate."
  (ExactInverse "Psi is the negative of the normalized Riemann screw function.")
  Nothing

riemannScrewToKernel :: RuntimeRepresentationEdge
riemannScrewToKernel = eraseRepresentationEdge $ representationEdge
  SRiemannScrew SRiemannScrewKernel "take the translation-difference kernel"
  ExactRepresentation leanCheckedTrust 1 suzukiScrewRef
  "The kernel is defined by g(t-u)-g(t)-g(-u)+g(0), and RHGarden.riemannScrewKernel_eq_zero_sum identifies its zero expansion."
  (NoReconstruction "A translation-difference kernel loses affine additions to a general screw function.")
  Nothing

riemannScrewToNevanlinnaTransform :: RuntimeRepresentationEdge
riemannScrewToNevanlinnaTransform = eraseRepresentationEdge $ representationEdge
  SRiemannScrew SXiNevanlinnaTransformHighStrip
  "take the absolutely convergent Fourier-Laplace transform on Im z>1/2"
  ExactRepresentation leanCheckedTrust 1 xiNevanlinnaRef
  "RHGarden.integral_riemannScrew_exp_eq_xiNevanlinnaQ_neg proves integral_0^infinity g(t)e^(izt)dt=(i/z^2)Q_xi(-z) with the project's spectral-coordinate convention."
  (NoReconstruction "The checked theorem records the high-strip transform identity; no inverse-transform theorem is asserted.")
  Nothing

riemannScrewKernelToIntegralForm :: RuntimeRepresentationEdge
riemannScrewKernelToIntegralForm = eraseRepresentationEdge $ representationEdge
  SRiemannScrewKernel SIntegralScrewQuadraticForm
  "extend sampled kernel positivity to compact integral quadratic forms"
  ExactRepresentation leanCheckedTrust 1
  (Reference
    "RHGarden.integralRiemannScrewKernelPSD_of_kernelPSD"
    "Lean theorem in formal/RHGarden/KernelIntegral.lean; finite-range approximation and dominated convergence are kernel checked.")
  "RHGarden.integralKernelPSD_of_kernelPSD is generic for continuous complex kernels; its screw-kernel specialization and compact-support Hermitian-form theorem are LeanChecked."
  (NoReconstruction "Only the sampled-to-integral positivity direction is registered; point-mass approximation for the converse is not yet formalized.")
  Nothing

suzukiPsiToScrewKernel :: RuntimeRepresentationEdge
suzukiPsiToScrewKernel = eraseRepresentationEdge $ representationEdge
  SSuzukiPsiZeroSide SRiemannScrewKernel "take Suzuki's translation-difference screw kernel"
  ExactRepresentation leanCheckedTrust 1 suzukiScrewRef
  "RHGarden.riemannScrewKernel_eq_zero_sum proves Suzuki equation (1.9) by absolutely convergent tsum algebra."
  (NoReconstruction "A translation-difference kernel loses affine additions to the screw function.")
  Nothing

suzukiGramToScrewKernel :: RuntimeRepresentationEdge
suzukiGramToScrewKernel = eraseRepresentationEdge $ representationEdge
  SSuzukiGramKernel SRiemannScrewKernel "evaluate the critical-line Suzuki Gram expansion"
  ExactRepresentation leanCheckedTrust 1 suzukiScrewRef
  "RHGarden.riemannScrewKernel_eq_gram_of_XiTZerosReal identifies the supplied critical-line Gram expansion with the zero-side screw kernel. The XiTZerosReal witness belongs to the source representation and is not inferred from the kernel."
  (NoReconstruction "No direct representation reconstruction is registered here. At the criterion level, kernel PSD now LeanChecks Xi spectral reality, which in turn supplies the Gram identity.")
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
  SFiniteWeilCutoffValues SWeilLiQuadraticValues "pass finite cutoffs to the infinite Weil-Li scalar"
  EquivalentTheorem leanCheckedTrust 1 liWeilInfiniteRef
  "RHGarden.finiteWeilScalar_heightCutoff_tendsto proves exhaustion of the ordinary absolutely convergent occurrence-indexed tsum."
  (ReconstructionUpTo "The infinite value is a controlled limit of a specified cofinal cutoff family.")
  Nothing

realLiToWeilLiQuadratic :: RuntimeRepresentationEdge
realLiToWeilLiQuadratic = eraseRepresentationEdge $ representationEdge
  SClassicalLiRealSequence SWeilLiQuadraticValues
  "identify each Li-test Weil diagonal value as twice the classical Li coefficient"
  EquivalentTheorem leanCheckedTrust 1 liWeilInfiniteRef
  "RHGarden.weilLiQuadraticValue_eq_two_li proves W(G_(k+1),G_(k+1))=2*lambda_(k+1)."
  (ExactInverse "Recover each real Li coefficient by division by 2.")
  Nothing

weilLiQuadraticToRealLi :: RuntimeRepresentationEdge
weilLiQuadraticToRealLi = eraseRepresentationEdge $ representationEdge
  SWeilLiQuadraticValues SClassicalLiRealSequence
  "recover classical Li coefficients from the Li-test Weil diagonal"
  EquivalentTheorem leanCheckedTrust 1 liWeilInfiniteRef
  "Reverse use of RHGarden.weilLiQuadraticValue_eq_two_li."
  (ExactInverse "Multiply each real Li coefficient by 2 to recover the Weil diagonal value.")
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
  SWeilLiQuadraticValues SLiSequence "candidate positive Gram factorization"
  ConjecturalBridge conjecturalTrust 8
  (Reference "UNPROVED RESEARCH EDGE" "No positive operator or norm-square factorization is currently proved.")
  "Seek lambda_n=||T v_n||^2 without assuming RH."
  (NoReconstruction "No transform exists until the conjectural factorization is constructed and proved.")
  (Just (PropertyTransport WeilLiValuesNonnegative AllLiCoefficientsNonnegative
    "A proved norm-square identity would transport positivity, but this statement is currently conjectural."))

representationGraph :: [RuntimeRepresentationEdge]
representationGraph =
  [ xiMobius, mobiusCoordinate, phiLogDerivative, logToSeries, seriesToSequence
  , xiToZeros, xiToDivisor, xiToSubquadraticGrowth, subquadraticZeroFreeToExpAffine
  , divisorToRadialCutoff, divisorToHeightCutoff
  , divisorToOccurrences, occurrencesToCanonicalProduct, canonicalProductToLogDerivative
  , xiAndCanonicalProductToZeroFreeQuotient, zeroFreeQuotientToGrowth
  , quotientGrowthToAffineFactorization, canonicalProductToXiLogDerivPartialFraction
  , heightCutoffToStarPartial, heightCutoffToFiniteWeil, starPartialToConvergence
  , localCountToReciprocalSquare, reciprocalSquareToStar, localCountToLiStar
  , classicalLiToStarConvergence, starConvergenceToWeil
  , divisorToXiSpectral, xiSpectralToSuzukiPsi, suzukiPsiToRiemannScrew
  , riemannScrewToKernel, riemannScrewToNevanlinnaTransform
  , riemannScrewKernelToIntegralForm
  , suzukiPsiToScrewKernel
  , suzukiGramToScrewKernel
  , nontrivialZetaZeroToXiZero, xiZeroToNontrivialZetaZero
  , zerosToLi, realLiToZeroSum, zeroSumToFiniteCutoffs
  , weilTestsToFiniteValues, finiteCutoffsToWeil
  , realLiToWeilLiQuadratic, weilLiQuadraticToRealLi
  , xiToTaylorData, mobiusToFormalSeries, formalTaylorComposition
  , formalMobiusCompositionInput, formalLogDerivative, formalCoefficientExtraction
  , formalToClassicalLi, certifiedXiToGeneratingLog, generatingLogToSequence
  , generatingToNormalizedClassical, normalizedToClassicalLi, classicalToNormalizedLi
  , classicalLiToReal
  , negativeToStandardMobiusXi, standardToNegativeMobiusXi
  ]

representationExplorationGraph :: [RuntimeRepresentationEdge]
representationExplorationGraph = representationGraph ++ [conjecturalPositiveFactorization]
