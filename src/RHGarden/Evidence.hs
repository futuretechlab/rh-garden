module RHGarden.Evidence
  ( LagariasCheck(..)
  , checkLagariasPrefix
  , renderLagariasCheck
  ) where

-- This module is intentionally named Evidence, not Proof.
-- Floating-point finite checks are never admitted as theorem certificates.

data LagariasCheck = LagariasCheck
  { checkedThrough :: Int
  , minimumMarginN :: Int
  , minimumMargin  :: Double
  , failures       :: [(Int, Double, Double)]
  } deriving (Eq, Show)

harmonicNumbers :: Int -> [Double]
harmonicNumbers n = drop 1 $ scanl (\h k -> h + 1 / fromIntegral k) 0 [1..n]

divisorSums :: Int -> [Integer]
divisorSums n =
  [ sigma k | k <- [1..n] ]
  where
    sigma k = sum
      [ if d * d == k then fromIntegral d
        else fromIntegral d + fromIntegral (k `div` d)
      | d <- [1..integerSqrt k]
      , k `mod` d == 0
      ]

integerSqrt :: Int -> Int
integerSqrt k = floor (sqrt (fromIntegral k :: Double))

lagariasBound :: Double -> Double
lagariasBound h = h + exp h * log h

checkLagariasPrefix :: Int -> LagariasCheck
checkLagariasPrefix n
  | n < 1 = error "checkLagariasPrefix: n must be >= 1"
  | otherwise =
      let hs = harmonicNumbers n
          ss = divisorSums n
          rows =
            [ (k, fromIntegral sig, lagariasBound h)
            | (k, h, sig) <- zip3 [1..] hs ss
            ]
          margins = [ (k, bound - sig) | (k, sig, bound) <- rows ]
          (minN, minM) = foldl1 chooseMin margins
          bad = [ (k, sig, bound) | (k, sig, bound) <- rows, sig > bound + 1.0e-12 ]
      in LagariasCheck n minN minM bad
  where
    chooseMin a@(_, x) b@(_, y)
      | x <= y = a
      | otherwise = b

renderLagariasCheck :: LagariasCheck -> String
renderLagariasCheck r = unlines
  [ "Finite Lagarias evidence check (NOT A PROOF)"
  , "checked n = 1.." ++ show (checkedThrough r)
  , "smallest numerical margin at n = " ++ show (minimumMarginN r)
  , "smallest margin bound-sigma = " ++ show (minimumMargin r)
  , if null (failures r)
      then "no floating-point counterexample found in this finite prefix"
      else "candidate failures: " ++ show (take 20 (failures r))
  , "Important: the theorem quantifies over every positive integer; a finite prefix cannot discharge it."
  ]
