module RHGarden.Algebra
  ( Polynomial
  , polynomial
  , coefficients
  , constant
  , variable
  , add
  , multiply
  , scale
  , derivative
  , RationalFunction
  , rationalFunction
  , numerator
  , denominator
  , differentiateRational
  , equalByCrossMultiplication
  ) where

import Data.List (dropWhileEnd)

-- | Dense coefficients in ascending degree order, normalized by deleting
-- trailing zeroes.  Rational uses exact Integer numerator/denominator data.
newtype Polynomial = Polynomial [Rational]
  deriving (Show)

instance Eq Polynomial where
  Polynomial xs == Polynomial ys = xs == ys

polynomial :: [Rational] -> Polynomial
polynomial = Polynomial . dropWhileEnd (== 0)

coefficients :: Polynomial -> [Rational]
coefficients (Polynomial xs) = xs

constant :: Rational -> Polynomial
constant x = polynomial [x]

variable :: Polynomial
variable = polynomial [0, 1]

add :: Polynomial -> Polynomial -> Polynomial
add (Polynomial xs) (Polynomial ys) = polynomial (zipWithDefault (+) xs ys)

scale :: Rational -> Polynomial -> Polynomial
scale scalar (Polynomial xs) = polynomial (map (scalar *) xs)

multiply :: Polynomial -> Polynomial -> Polynomial
multiply (Polynomial xs) (Polynomial ys) =
  polynomial
    [ sum [ x * y | (i, x) <- zip [0 :: Int ..] xs
                    , (j, y) <- zip [0 :: Int ..] ys
                    , i + j == degree ]
    | degree <- [0 .. length xs + length ys - 2]
    ]

derivative :: Polynomial -> Polynomial
derivative (Polynomial xs) =
  polynomial [fromIntegral degree * coefficient | (degree, coefficient) <- zip [1 :: Int ..] (drop 1 xs)]

zipWithDefault :: (a -> a -> a) -> [a] -> [a] -> [a]
zipWithDefault _ [] ys = ys
zipWithDefault _ xs [] = xs
zipWithDefault f (x:xs) (y:ys) = f x y : zipWithDefault f xs ys

-- | A deliberately un-reduced rational function. Equality is checked exactly
-- by cross multiplication, so polynomial gcd machinery is unnecessary here.
data RationalFunction = RationalFunction Polynomial Polynomial
  deriving (Eq, Show)

rationalFunction :: Polynomial -> Polynomial -> Maybe RationalFunction
rationalFunction _ denominatorPolynomial | denominatorPolynomial == polynomial [] = Nothing
rationalFunction numeratorPolynomial denominatorPolynomial =
  Just (RationalFunction numeratorPolynomial denominatorPolynomial)

numerator :: RationalFunction -> Polynomial
numerator (RationalFunction p _) = p

denominator :: RationalFunction -> Polynomial
denominator (RationalFunction _ q) = q

differentiateRational :: RationalFunction -> RationalFunction
differentiateRational (RationalFunction p q) =
  RationalFunction
    (add (multiply (derivative p) q) (scale (-1) (multiply p (derivative q))))
    (multiply q q)

equalByCrossMultiplication :: RationalFunction -> RationalFunction -> Bool
equalByCrossMultiplication (RationalFunction p q) (RationalFunction r s) =
  multiply p s == multiply r q
