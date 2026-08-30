module RHGarden.Mobius
  ( ExactAlgebraCertificate
  , certificateStatement
  , mobiusFunction
  , expectedMobiusDerivative
  , checkMobiusDerivative
  , renderMobiusCheck
  ) where

import RHGarden.Algebra

-- The constructor is private: a caller can inspect a certificate but cannot
-- manufacture one.  This certifies only the finite polynomial identity below.
newtype ExactAlgebraCertificate = ExactAlgebraCertificate String
  deriving (Eq, Show)

certificateStatement :: ExactAlgebraCertificate -> String
certificateStatement (ExactAlgebraCertificate statement) = statement

mobiusFunction :: RationalFunction
mobiusFunction = requireRationalFunction (scale (-1) variable) (add (constant 1) (scale (-1) variable))

expectedMobiusDerivative :: RationalFunction
expectedMobiusDerivative =
  requireRationalFunction
    (constant (-1))
    (multiply oneMinusZ oneMinusZ)
  where
    oneMinusZ = add (constant 1) (scale (-1) variable)

checkMobiusDerivative :: Maybe ExactAlgebraCertificate
checkMobiusDerivative
  | equalByCrossMultiplication (differentiateRational mobiusFunction) expectedMobiusDerivative =
      Just (ExactAlgebraCertificate "m(z)=-z/(1-z) has m'(z)=-1/(1-z)^2 by exact Rational polynomial cross multiplication")
  | otherwise = Nothing

renderMobiusCheck :: String
renderMobiusCheck = unlines
  [ "Exact Mobius derivative check"
  , "m(z) = -z/(1-z)"
  , "claimed derivative = -1/(1-z)^2"
  , case checkMobiusDerivative of
      Just certificate -> "ExactExecutable: " ++ certificateStatement certificate
      Nothing -> "FAILED: exact cross multiplication did not establish the identity"
  , "Scope: this certificate proves only the finite rational-function identity; it proves no analytic fact about xi or zeta."
  ]

requireRationalFunction :: Polynomial -> Polynomial -> RationalFunction
requireRationalFunction p q =
  case rationalFunction p q of
    Just value -> value
    Nothing -> error "internal invariant: a statically constructed denominator was zero"
