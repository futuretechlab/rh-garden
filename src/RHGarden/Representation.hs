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
  | XiZeros
  | NontrivialZetaZero
  | XiZero
  | MobiusVariable
  | XiAfterMobius
  | LogXiMobius
  | LiGeneratingSeries
  | LiSequence
  | WeilLiTestFunctions
  | WeilQuadraticValues
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
  SXiZeros :: SRepresentation 'XiZeros
  SNontrivialZetaZero :: SRepresentation 'NontrivialZetaZero
  SXiZero :: SRepresentation 'XiZero
  SMobiusVariable :: SRepresentation 'MobiusVariable
  SXiAfterMobius :: SRepresentation 'XiAfterMobius
  SLogXiMobius :: SRepresentation 'LogXiMobius
  SLiGeneratingSeries :: SRepresentation 'LiGeneratingSeries
  SLiSequence :: SRepresentation 'LiSequence
  SWeilLiTestFunctions :: SRepresentation 'WeilLiTestFunctions
  SWeilQuadraticValues :: SRepresentation 'WeilQuadraticValues
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
representationValue SXiZeros = XiZeros
representationValue SNontrivialZetaZero = NontrivialZetaZero
representationValue SXiZero = XiZero
representationValue SMobiusVariable = MobiusVariable
representationValue SXiAfterMobius = XiAfterMobius
representationValue SLogXiMobius = LogXiMobius
representationValue SLiGeneratingSeries = LiGeneratingSeries
representationValue SLiSequence = LiSequence
representationValue SWeilLiTestFunctions = WeilLiTestFunctions
representationValue SWeilQuadraticValues = WeilQuadraticValues
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
representationLabel XiZeros = "multiset of nontrivial xi zeros"
representationLabel NontrivialZetaZero = "a nontrivial Riemann-zeta zero s"
representationLabel XiZero = "the corresponding zero xi(s)=0"
representationLabel MobiusVariable = "Mobius coordinate m(z)=-z/(1-z)"
representationLabel XiAfterMobius = "phi(z)=xi(-z/(1-z))"
representationLabel LogXiMobius = "logarithmic derivative d/dz log phi(z)"
representationLabel LiGeneratingSeries = "Li generating series sum_{n>=1} lambda_n z^(n-1)"
representationLabel LiSequence = "Li coefficient sequence (lambda_n)_{n>=1}"
representationLabel WeilLiTestFunctions = "Lagarias Li test functions G_n(s)=1-(1-1/s)^n"
representationLabel WeilQuadraticValues = "Weil quadratic-functional values associated to Li coefficients"
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
  | WeilFormNonnegative
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
