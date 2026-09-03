{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module RHGarden.Representation
  ( Representation(..)
  , SRepresentation(..)
  , representationValue
  , representationLabel
  , RepresentationKind(..)
  , Property(..)
  , PropertyTransport(..)
  , Reconstruction(..)
  , SymbolicObject(..)
  , RepresentationEdge
  , representationEdge
  , RuntimeRepresentationEdge(..)
  , eraseRepresentationEdge
  ) where

import RHGarden.Core (Reference, Trust)

data Representation
  = XiFunction
  | XiSubquadraticGrowth
  | ZeroFreeEntireSubquadratic
  | ExpAffineEntire
  | XiDivisor
  | XiRadialZeroCutoff
  | XiHeightZeroCutoff
  | XiZeros
  | NontrivialZetaZero
  | XiZero
  | XiZeroOccurrences
  | XiCanonicalProduct
  | XiCanonicalProductLogDerivative
  | XiZeroFreeQuotient
  | XiQuotientSubquadraticGrowth
  | XiAffineFactorization
  | XiLogDerivPartialFraction
  | MobiusVariable
  | XiAfterMobius
  | LogXiMobius
  | LiGeneratingSeries
  | LiSequence
  | LiStarPartialSums
  | XiLocalZeroCountBound
  | ReciprocalSquareSummability
  | ReciprocalStarConvergence
  | LiStarConvergence
  | LiZeroSumSequence
  | WeilLiTestFunctions
  | FiniteWeilCutoffValues
  | WeilLiQuadraticValues
  | XiTaylorAtOne
  | MobiusFormalSeries
  | XiAfterFormalMobius
  | LiFormalLogDerivative
  | LiFormalCoefficientSequence
  | LiGeneratingLog
  | LiGeneratingSequence
  | NormalizedClassicalLiSequence
  | ClassicalLiSequence
  | ClassicalLiRealSequence
  | NegativeMobiusXi
  | StandardLiMobiusXi
  deriving (Eq, Ord, Show, Read, Enum, Bounded)

data SRepresentation (r :: Representation) where
  SXiFunction :: SRepresentation 'XiFunction
  SXiSubquadraticGrowth :: SRepresentation 'XiSubquadraticGrowth
  SZeroFreeEntireSubquadratic :: SRepresentation 'ZeroFreeEntireSubquadratic
  SExpAffineEntire :: SRepresentation 'ExpAffineEntire
  SXiDivisor :: SRepresentation 'XiDivisor
  SXiRadialZeroCutoff :: SRepresentation 'XiRadialZeroCutoff
  SXiHeightZeroCutoff :: SRepresentation 'XiHeightZeroCutoff
  SXiZeros :: SRepresentation 'XiZeros
  SNontrivialZetaZero :: SRepresentation 'NontrivialZetaZero
  SXiZero :: SRepresentation 'XiZero
  SXiZeroOccurrences :: SRepresentation 'XiZeroOccurrences
  SXiCanonicalProduct :: SRepresentation 'XiCanonicalProduct
  SXiCanonicalProductLogDerivative :: SRepresentation 'XiCanonicalProductLogDerivative
  SXiZeroFreeQuotient :: SRepresentation 'XiZeroFreeQuotient
  SXiQuotientSubquadraticGrowth :: SRepresentation 'XiQuotientSubquadraticGrowth
  SXiAffineFactorization :: SRepresentation 'XiAffineFactorization
  SXiLogDerivPartialFraction :: SRepresentation 'XiLogDerivPartialFraction
  SMobiusVariable :: SRepresentation 'MobiusVariable
  SXiAfterMobius :: SRepresentation 'XiAfterMobius
  SLogXiMobius :: SRepresentation 'LogXiMobius
  SLiGeneratingSeries :: SRepresentation 'LiGeneratingSeries
  SLiSequence :: SRepresentation 'LiSequence
  SLiStarPartialSums :: SRepresentation 'LiStarPartialSums
  SXiLocalZeroCountBound :: SRepresentation 'XiLocalZeroCountBound
  SReciprocalSquareSummability :: SRepresentation 'ReciprocalSquareSummability
  SReciprocalStarConvergence :: SRepresentation 'ReciprocalStarConvergence
  SLiStarConvergence :: SRepresentation 'LiStarConvergence
  SLiZeroSumSequence :: SRepresentation 'LiZeroSumSequence
  SWeilLiTestFunctions :: SRepresentation 'WeilLiTestFunctions
  SFiniteWeilCutoffValues :: SRepresentation 'FiniteWeilCutoffValues
  SWeilLiQuadraticValues :: SRepresentation 'WeilLiQuadraticValues
  SXiTaylorAtOne :: SRepresentation 'XiTaylorAtOne
  SMobiusFormalSeries :: SRepresentation 'MobiusFormalSeries
  SXiAfterFormalMobius :: SRepresentation 'XiAfterFormalMobius
  SLiFormalLogDerivative :: SRepresentation 'LiFormalLogDerivative
  SLiFormalCoefficientSequence :: SRepresentation 'LiFormalCoefficientSequence
  SLiGeneratingLog :: SRepresentation 'LiGeneratingLog
  SLiGeneratingSequence :: SRepresentation 'LiGeneratingSequence
  SNormalizedClassicalLiSequence :: SRepresentation 'NormalizedClassicalLiSequence
  SClassicalLiSequence :: SRepresentation 'ClassicalLiSequence
  SClassicalLiRealSequence :: SRepresentation 'ClassicalLiRealSequence
  SNegativeMobiusXi :: SRepresentation 'NegativeMobiusXi
  SStandardLiMobiusXi :: SRepresentation 'StandardLiMobiusXi

deriving instance Show (SRepresentation r)

representationValue :: SRepresentation r -> Representation
representationValue SXiFunction = XiFunction
representationValue SXiSubquadraticGrowth = XiSubquadraticGrowth
representationValue SZeroFreeEntireSubquadratic = ZeroFreeEntireSubquadratic
representationValue SExpAffineEntire = ExpAffineEntire
representationValue SXiDivisor = XiDivisor
representationValue SXiRadialZeroCutoff = XiRadialZeroCutoff
representationValue SXiHeightZeroCutoff = XiHeightZeroCutoff
representationValue SXiZeros = XiZeros
representationValue SNontrivialZetaZero = NontrivialZetaZero
representationValue SXiZero = XiZero
representationValue SXiZeroOccurrences = XiZeroOccurrences
representationValue SXiCanonicalProduct = XiCanonicalProduct
representationValue SXiCanonicalProductLogDerivative = XiCanonicalProductLogDerivative
representationValue SXiZeroFreeQuotient = XiZeroFreeQuotient
representationValue SXiQuotientSubquadraticGrowth = XiQuotientSubquadraticGrowth
representationValue SXiAffineFactorization = XiAffineFactorization
representationValue SXiLogDerivPartialFraction = XiLogDerivPartialFraction
representationValue SMobiusVariable = MobiusVariable
representationValue SXiAfterMobius = XiAfterMobius
representationValue SLogXiMobius = LogXiMobius
representationValue SLiGeneratingSeries = LiGeneratingSeries
representationValue SLiSequence = LiSequence
representationValue SLiStarPartialSums = LiStarPartialSums
representationValue SXiLocalZeroCountBound = XiLocalZeroCountBound
representationValue SReciprocalSquareSummability = ReciprocalSquareSummability
representationValue SReciprocalStarConvergence = ReciprocalStarConvergence
representationValue SLiStarConvergence = LiStarConvergence
representationValue SLiZeroSumSequence = LiZeroSumSequence
representationValue SWeilLiTestFunctions = WeilLiTestFunctions
representationValue SFiniteWeilCutoffValues = FiniteWeilCutoffValues
representationValue SWeilLiQuadraticValues = WeilLiQuadraticValues
representationValue SXiTaylorAtOne = XiTaylorAtOne
representationValue SMobiusFormalSeries = MobiusFormalSeries
representationValue SXiAfterFormalMobius = XiAfterFormalMobius
representationValue SLiFormalLogDerivative = LiFormalLogDerivative
representationValue SLiFormalCoefficientSequence = LiFormalCoefficientSequence
representationValue SLiGeneratingLog = LiGeneratingLog
representationValue SLiGeneratingSequence = LiGeneratingSequence
representationValue SNormalizedClassicalLiSequence = NormalizedClassicalLiSequence
representationValue SClassicalLiSequence = ClassicalLiSequence
representationValue SClassicalLiRealSequence = ClassicalLiRealSequence
representationValue SNegativeMobiusXi = NegativeMobiusXi
representationValue SStandardLiMobiusXi = StandardLiMobiusXi

representationLabel :: Representation -> String
representationLabel XiFunction = "completed xi function xi(s)"
representationLabel XiSubquadraticGrowth = "proved global subquadratic growth bound for xi"
representationLabel ZeroFreeEntireSubquadratic = "zero-free entire function with subquadratic growth"
representationLabel ExpAffineEntire = "exponential of an affine entire function"
representationLabel XiDivisor = "locally finite xi divisor with analytic multiplicities"
representationLabel XiRadialZeroCutoff = "radial xi-zero Multiset cutoff |rho|<=T"
representationLabel XiHeightZeroCutoff = "Lagarias xi-zero Multiset cutoff |Im rho|<=T"
representationLabel XiZeros = "multiset of nontrivial xi zeros"
representationLabel NontrivialZetaZero = "a nontrivial Riemann-zeta zero s"
representationLabel XiZero = "the corresponding zero xi(s)=0"
representationLabel XiZeroOccurrences = "xi zeros expanded into analytic-multiplicity occurrences"
representationLabel XiCanonicalProduct = "locally uniformly convergent intrinsic genus-one xi canonical product"
representationLabel XiCanonicalProductLogDerivative = "occurrence-indexed logarithmic derivative of the xi canonical product"
representationLabel XiZeroFreeQuotient = "entire everywhere-nonzero xi/canonical-product quotient"
representationLabel XiQuotientSubquadraticGrowth = "proved subquadratic growth bound for the xi quotient"
representationLabel XiAffineFactorization = "normalized LeanChecked xi genus-one canonical product"
representationLabel XiLogDerivPartialFraction = "exact occurrence-indexed partial fraction for the xi logarithmic derivative"
representationLabel MobiusVariable = "Mobius coordinate m(z)=-z/(1-z)"
representationLabel XiAfterMobius = "phi(z)=xi(-z/(1-z))"
representationLabel LogXiMobius = "logarithmic derivative d/dz log phi(z)"
representationLabel LiGeneratingSeries = "Li generating series sum_{n>=1} lambda_n z^(n-1)"
representationLabel LiSequence = "Li coefficient sequence (lambda_n)_{n>=1}"
representationLabel LiStarPartialSums = "Lagarias height-ordered Li star partial sums"
representationLabel XiLocalZeroCountBound = "open unit-height xi-zero multiplicity bound"
representationLabel ReciprocalSquareSummability = "multiplicity-weighted reciprocal-square summability"
representationLabel ReciprocalStarConvergence = "conjugate-paired reciprocal star convergence"
representationLabel LiStarConvergence = "Lagarias height-ordered star-convergence proposition"
representationLabel LiZeroSumSequence = "conditionally star-convergent Li zero-sum sequence"
representationLabel WeilLiTestFunctions = "Lagarias Li test functions G_n(s)=1-(1-1/s)^n"
representationLabel FiniteWeilCutoffValues = "multiplicity-preserving finite Weil/Li cutoff values"
representationLabel WeilLiQuadraticValues = "absolutely convergent diagonal Weil values on the Li test family"
representationLabel XiTaylorAtOne = "formal Taylor data of F(u)=2*xi(1+u) at u=0"
representationLabel MobiusFormalSeries = "formal series U=X/(1-X)=X+X^2+..."
representationLabel XiAfterFormalMobius = "certified coefficient series of 2*xi(1/(1-z))"
representationLabel LiFormalLogDerivative = "formal derivative of certified G times inverse(G)"
representationLabel LiFormalCoefficientSequence = "coefficients of the certified formal logarithmic derivative"
representationLabel LiGeneratingLog = "local analytic log of 2*xi(1/(1-z))"
representationLabel LiGeneratingSequence = "derivative coefficients of the local Li generating log"
representationLabel NormalizedClassicalLiSequence = "Li original-derivative sequence for normalized xi"
representationLabel ClassicalLiSequence = "independently defined classical Li coefficient sequence"
representationLabel ClassicalLiRealSequence = "classical Li coefficients with proved real-valuedness"
representationLabel NegativeMobiusXi = "xi(-z/(1-z)) viewpoint"
representationLabel StandardLiMobiusXi = "xi(1/(1-z)) viewpoint"

data RepresentationKind
  = ExactRepresentation
  | EquivalentTheorem
  | SufficientReduction
  | InformationLoss
  | ConjecturalBridge
  deriving (Eq, Ord, Show)

data Property
  = CriticalLineZeros
  | AllLiCoefficientsNonnegative
  | WeilLiValuesNonnegative
  deriving (Eq, Ord, Show)

data PropertyTransport = PropertyTransport
  { transportedFrom :: Property
  , transportedTo :: Property
  , transportStatement :: String
  } deriving (Eq, Show)

data Reconstruction
  = ExactInverse String
  | ReconstructionUpTo String
  | NoReconstruction String
  deriving (Eq, Show)

-- Symbolic declarations only. They are not evaluators for xi.
data SymbolicObject
  = XiSymbol
  | MobiusSubstitution
  | PhiSymbol
  | LogDerivative SymbolicObject
  | TaylorCoefficients SymbolicObject
  | ZeroSumFormula String
  deriving (Eq, Show)

data RepresentationEdge (a :: Representation) (b :: Representation) = RepresentationEdge
  { edgeFrom :: SRepresentation a
  , edgeTo :: SRepresentation b
  , edgeName :: String
  , edgeKind :: RepresentationKind
  , edgeTrust :: Trust
  , edgeCost :: Int
  , edgeReference :: Reference
  , edgeTransform :: String
  , edgeReconstruction :: Reconstruction
  , edgePropertyTransport :: Maybe PropertyTransport
  }

representationEdge
  :: SRepresentation a -> SRepresentation b -> String -> RepresentationKind
  -> Trust -> Int -> Reference -> String -> Reconstruction
  -> Maybe PropertyTransport -> RepresentationEdge a b
representationEdge = RepresentationEdge

data RuntimeRepresentationEdge = RuntimeRepresentationEdge
  { rreFrom :: Representation
  , rreTo :: Representation
  , rreName :: String
  , rreKind :: RepresentationKind
  , rreTrust :: Trust
  , rreCost :: Int
  , rreReference :: Reference
  , rreTransform :: String
  , rreReconstruction :: Reconstruction
  , rrePropertyTransport :: Maybe PropertyTransport
  } deriving (Eq, Show)

eraseRepresentationEdge :: RepresentationEdge a b -> RuntimeRepresentationEdge
eraseRepresentationEdge edge = RuntimeRepresentationEdge
  { rreFrom = representationValue (edgeFrom edge)
  , rreTo = representationValue (edgeTo edge)
  , rreName = edgeName edge
  , rreKind = edgeKind edge
  , rreTrust = edgeTrust edge
  , rreCost = edgeCost edge
  , rreReference = edgeReference edge
  , rreTransform = edgeTransform edge
  , rreReconstruction = edgeReconstruction edge
  , rrePropertyTransport = edgePropertyTransport edge
  }
