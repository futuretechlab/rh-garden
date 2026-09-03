{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module RHGarden.Core
  ( Criterion(..)
  , SCriterion(..)
  , criterionValue
  , criterionLabel
  , Trust
  , leanCheckedTrust
  , exactExecutableTrust
  , literatureCertifiedTrust
  , conjecturalTrust
  , Relation(..)
  , ObligationProperty(..)
  , Preservation(..)
  , Reference(..)
  , Reduction
  , leanEquiv
  , literatureEquiv
  , literatureSufficient
  , conjecturalReduction
  , RuntimeReduction(..)
  , eraseReduction
  , admissibleInKernelMode
  , admissibleInLiteratureMode
  , Proof
  , submissionReady
  ) where

-- | A proposition/viewpoint that may serve as a proof obligation.
--
-- The constructors intentionally mix analytic, coefficient, functional-analytic,
-- arithmetic, and spectral formulations.  The graph is about moving between
-- representations of the same underlying mathematical content.
data Criterion
  = RH
  | XiRiemannHypothesis
  | XiZerosReal
  | LiPositive
  | WeilLiPositive
  | WeilFormPSD
  | NymanBeurlingDense
  | LagariasInequality
  | SelfAdjointXiRealization
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Singleton witnesses let a bridge's endpoints appear in its Haskell type.
data SCriterion (c :: Criterion) where
  SRH                     :: SCriterion 'RH
  SXiRiemannHypothesis    :: SCriterion 'XiRiemannHypothesis
  SXiZerosReal            :: SCriterion 'XiZerosReal
  SLiPositive             :: SCriterion 'LiPositive
  SWeilLiPositive         :: SCriterion 'WeilLiPositive
  SWeilFormPSD            :: SCriterion 'WeilFormPSD
  SNymanBeurlingDense     :: SCriterion 'NymanBeurlingDense
  SLagariasInequality     :: SCriterion 'LagariasInequality
  SSelfAdjointXiRealization :: SCriterion 'SelfAdjointXiRealization

deriving instance Show (SCriterion c)

criterionValue :: SCriterion c -> Criterion
criterionValue SRH                       = RH
criterionValue SXiRiemannHypothesis      = XiRiemannHypothesis
criterionValue SXiZerosReal              = XiZerosReal
criterionValue SLiPositive               = LiPositive
criterionValue SWeilLiPositive           = WeilLiPositive
criterionValue SWeilFormPSD              = WeilFormPSD
criterionValue SNymanBeurlingDense       = NymanBeurlingDense
criterionValue SLagariasInequality       = LagariasInequality
criterionValue SSelfAdjointXiRealization = SelfAdjointXiRealization

criterionLabel :: Criterion -> String
criterionLabel RH = "Riemann Hypothesis"
criterionLabel XiRiemannHypothesis = "Every zero s of the entire xi function has re(s)=1/2"
criterionLabel XiZerosReal = "All zeros of Xi(t)=xi(1/2+it) are real"
criterionLabel LiPositive = "Li coefficients lambda_n are nonnegative for every n>=1"
criterionLabel WeilLiPositive = "Diagonal Weil values are nonnegative on every Li test G_n"
criterionLabel WeilFormPSD = "Full Weil form is positive semidefinite on its complete test-function space"
criterionLabel NymanBeurlingDense = "Nyman-Beurling closure/density criterion"
criterionLabel LagariasInequality = "Lagarias divisor-sum inequality for every n>=1"
criterionLabel SelfAdjointXiRealization =
  "Self-adjoint operator whose spectrum is exactly the Xi zero ordinates"

data Trust
  = LeanChecked
  | ExactExecutable
  | LiteratureCertified
  | Conjectural
  deriving (Eq, Ord, Show)

leanCheckedTrust, exactExecutableTrust, literatureCertifiedTrust, conjecturalTrust :: Trust
leanCheckedTrust = LeanChecked
exactExecutableTrust = ExactExecutable
literatureCertifiedTrust = LiteratureCertified
conjecturalTrust = Conjectural

data Relation
  = Equivalent
  | SufficientCondition
  deriving (Eq, Ord, Show)

data ObligationProperty
  = NontrivialZerosOnCriticalLine
  | XiZerosHaveRealOrdinates
  | EveryLiCoefficientNonnegative
  | WeilLiDiagonalNonnegative
  deriving (Eq, Ord, Show)

data Preservation = Preservation
  { preservationFrom :: ObligationProperty
  , preservationTo :: ObligationProperty
  , preservationCertificate :: String
  } deriving (Eq, Show)

data Reference = Reference
  { refShort :: String
  , refCitation :: String
  } deriving (Eq, Ord, Show)

-- | Goal-reduction edge.
--
-- Reduction a b means: to prove proposition a, it is lawful (under the stated
-- relation) to replace it by the obligation b.
--
-- The constructor is deliberately not exported.  New edges should be made via
-- an explicit trust-labelled smart constructor, preventing silent mixing of
-- theorem-backed and conjectural steps.
data Reduction (a :: Criterion) (b :: Criterion) = Reduction
  { reductionFrom      :: SCriterion a
  , reductionTo        :: SCriterion b
  , reductionName      :: String
  , reductionRelation  :: Relation
  , reductionTrust     :: Trust
  , reductionCost      :: Int
  , reductionReference :: Reference
  , reductionNote      :: String
  }

leanEquiv
  :: SCriterion a
  -> SCriterion b
  -> String
  -> Int
  -> Reference
  -> String
  -> Reduction a b
leanEquiv a b name cost ref note =
  Reduction a b name Equivalent LeanChecked cost ref note

literatureEquiv
  :: SCriterion a
  -> SCriterion b
  -> String
  -> Int
  -> Reference
  -> String
  -> Reduction a b
literatureEquiv a b name cost ref note =
  Reduction a b name Equivalent LiteratureCertified cost ref note

literatureSufficient
  :: SCriterion a
  -> SCriterion b
  -> String
  -> Int
  -> Reference
  -> String
  -> Reduction a b
literatureSufficient a b name cost ref note =
  Reduction a b name SufficientCondition LiteratureCertified cost ref note

conjecturalReduction
  :: SCriterion a
  -> SCriterion b
  -> String
  -> Relation
  -> Int
  -> Reference
  -> String
  -> Reduction a b
conjecturalReduction a b name relation cost ref note =
  Reduction a b name relation Conjectural cost ref note

-- | Existentially erased edge used by the dynamic route planner.
data RuntimeReduction = RuntimeReduction
  { rrFrom      :: Criterion
  , rrTo        :: Criterion
  , rrName      :: String
  , rrRelation  :: Relation
  , rrTrust     :: Trust
  , rrCost      :: Int
  , rrReference :: Reference
  , rrNote      :: String
  , rrPreservation :: Maybe Preservation
  } deriving (Eq, Show)

eraseReduction :: Reduction a b -> RuntimeReduction
eraseReduction r = RuntimeReduction
  { rrFrom      = criterionValue (reductionFrom r)
  , rrTo        = criterionValue (reductionTo r)
  , rrName      = reductionName r
  , rrRelation  = reductionRelation r
  , rrTrust     = reductionTrust r
  , rrCost      = reductionCost r
  , rrReference = reductionReference r
  , rrNote      = reductionNote r
  , rrPreservation = criterionPreservation
      (criterionValue (reductionFrom r)) (criterionValue (reductionTo r))
  }

criterionPreservation :: Criterion -> Criterion -> Maybe Preservation
criterionPreservation RH XiZerosReal = Just (Preservation
  NontrivialZerosOnCriticalLine XiZerosHaveRealOrdinates
  "Under s=1/2+it, the critical-line property is equivalent to reality of every Xi zero parameter; literature-certified, not kernel checked.")
criterionPreservation XiZerosReal RH = Just (Preservation
  XiZerosHaveRealOrdinates NontrivialZerosOnCriticalLine
  "Inverse critical-line parametrization; literature-certified, not kernel checked.")
criterionPreservation RH LiPositive = Just (Preservation
  NontrivialZerosOnCriticalLine EveryLiCoefficientNonnegative
  "Li's criterion transports the universal zero-location property to forall n>=1, lambda_n>=0; literature-certified, not kernel checked.")
criterionPreservation LiPositive RH = Just (Preservation
  EveryLiCoefficientNonnegative NontrivialZerosOnCriticalLine
  "Reverse direction of Li's criterion; literature-certified, not kernel checked.")
criterionPreservation LiPositive WeilLiPositive = Just (Preservation
  EveryLiCoefficientNonnegative WeilLiDiagonalNonnegative
  "The LeanChecked identity W(G_n,G_n)=2*lambda_n transports nonnegativity coefficientwise.")
criterionPreservation WeilLiPositive LiPositive = Just (Preservation
  WeilLiDiagonalNonnegative EveryLiCoefficientNonnegative
  "Divide the LeanChecked diagonal identity by the positive scalar 2.")
criterionPreservation _ _ = Nothing

admissibleInKernelMode :: RuntimeReduction -> Bool
admissibleInKernelMode r = rrTrust r == LeanChecked

admissibleInLiteratureMode :: RuntimeReduction -> Bool
admissibleInLiteratureMode r = rrTrust r /= Conjectural

-- | Opaque placeholder for a future kernel proof term.  This module exports no
-- constructor and Evidence exports no promotion function.
data Proof (c :: Criterion) = KernelProofInternal

submissionReady :: Maybe (Proof 'RH) -> Bool
submissionReady Nothing = False
submissionReady (Just KernelProofInternal) = True
