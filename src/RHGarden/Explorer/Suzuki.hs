module RHGarden.Explorer.Suzuki
  ( CandidateStatus(..)
  , ExplorerOptions(..)
  , ExplorerReport(..)
  , OmegaSummary(..)
  , CellMinimum(..)
  , CandidateCertificate(..)
  , defaultExplorerOptions
  , parseExplorerOptions
  , exploreSuzuki
  , renderExplorerAscii
  , renderExplorerCsv
  , renderExplorerJson
  , renderCertificatesJson
  , runSuzukiExplorer
  , suzukiPsiNumeric
  ) where

import Data.Char (toLower)
import Data.List (intercalate, isSuffixOf, maximumBy, minimumBy, nubBy, sort, sortOn)
import Data.Ord (comparing)
import Numeric (showFFloat)
import Text.Read (readMaybe)

-- | Discovery statuses deliberately exclude words such as "proved" or
-- "LeanChecked".  Numerical output can only become formal evidence after a
-- separate exact Lean certificate is constructed.
data CandidateStatus
  = Candidate
  | NumericallyPassed
  | NumericallyFailed
  deriving (Eq, Ord, Show, Read)

data OutputFormat = OutputAscii | OutputCsv | OutputJson
  deriving (Eq, Ord, Show, Read)

data ExplorerOptions = ExplorerOptions
  { explorerOmegas :: [Double]
  , explorerOmegaMin :: Maybe Double
  , explorerOmegaMax :: Maybe Double
  , explorerOmegaCount :: Maybe Int
  , explorerTMin :: Double
  , explorerTMax :: Double
  , explorerSamples :: Int
  , explorerPrimeCells :: Bool
  , explorerOutput :: Maybe FilePath
  , explorerOutputFormat :: OutputFormat
  , explorerCertificateOutput :: Maybe FilePath
  } deriving (Eq, Show)

data PrimeMetadata = PrimeMetadata
  { metadataPreviousPrime :: Maybe Int
  , metadataNextPrime :: Maybe Int
  , metadataPrimeGap :: Maybe Int
  , metadataChebyshevTheta :: Double
  , metadataChebyshevPsi :: Double
  , metadataPsiMinusN :: Double
  , metadataLeftPrimePower :: Bool
  , metadataRightPrimePower :: Bool
  } deriving (Eq, Show)

data CellMinimum = CellMinimum
  { cellOmega :: Double
  , cellIndex :: Int
  , cellLeft :: Double
  , cellRight :: Double
  , cellCandidateT :: Double
  , cellCandidateValue :: Double
  , cellDerivative :: Double
  , cellPsiOverT :: Double
  , cellPsiOverTSq :: Double
  , cellExpNegHalfPsi :: Double
  , cellExpNegOmegaPsi :: Double
  , cellOmegaTimesT :: Double
  , cellMetadata :: PrimeMetadata
  } deriving (Eq, Show)

data OmegaSummary = OmegaSummary
  { summaryOmega :: Double
  , summaryMinimum :: Double
  , summaryArgmin :: Double
  , summaryCell :: Int
  , summaryCrossCheckError :: Double
  } deriving (Eq, Show)

data CandidateCertificate = CandidateCertificate
  { certificateOmega :: Double
  , certificateLeft :: Double
  , certificateRight :: Double
  , certificatePrimeCell :: Int
  , certificateBasis :: [String]
  , certificateCoefficients :: [(Integer, Integer)]
  , certificateClaimedMinimum :: Double
  , certificateDiscoveryPrecision :: Double
  , certificateStatus :: CandidateStatus
  } deriving (Eq, Show)

data ExplorerReport = ExplorerReport
  { reportOptions :: ExplorerOptions
  , reportSummaries :: [OmegaSummary]
  , reportCellMinima :: [CellMinimum]
  , reportCertificates :: [CandidateCertificate]
  } deriving (Eq, Show)

data PrimeEvent = PrimeEvent
  { eventN :: Int
  , eventLogN :: Double
  , eventMangoldt :: Double
  , eventWeight :: Double
  } deriving (Eq, Show)

data BasePoint = BasePoint
  { baseT :: Double
  , baseArchimedean :: Double
  , basePrime :: Double
  , basePsi :: Double
  , basePsiDerivative :: Double
  } deriving (Eq, Show)

data ShiftPoint = ShiftPoint
  { shiftT :: Double
  , shiftValue :: Double
  , shiftDerivative :: Double
  , shiftCrossValue :: Double
  } deriving (Eq, Show)

defaultExplorerOptions :: ExplorerOptions
defaultExplorerOptions = ExplorerOptions
  { explorerOmegas = []
  , explorerOmegaMin = Nothing
  , explorerOmegaMax = Nothing
  , explorerOmegaCount = Nothing
  , explorerTMin = 0
  , explorerTMax = 6
  , explorerSamples = 801
  , explorerPrimeCells = False
  , explorerOutput = Nothing
  , explorerOutputFormat = OutputAscii
  , explorerCertificateOutput = Nothing
  }

parseExplorerOptions :: [String] -> Either String ExplorerOptions
parseExplorerOptions = go defaultExplorerOptions
  where
    go options [] = validateOptions options
    go options ("--omega" : value : rest) =
      parseDouble "--omega" value >>= \x ->
        go options { explorerOmegas = explorerOmegas options ++ [x] } rest
    go options ("--omega-min" : value : rest) =
      parseDouble "--omega-min" value >>= \x ->
        go options { explorerOmegaMin = Just x } rest
    go options ("--omega-max" : value : rest) =
      parseDouble "--omega-max" value >>= \x ->
        go options { explorerOmegaMax = Just x } rest
    go options ("--omega-count" : value : rest) =
      parseInt "--omega-count" value >>= \x ->
        go options { explorerOmegaCount = Just x } rest
    go options ("--t-min" : value : rest) =
      parseDouble "--t-min" value >>= \x ->
        go options { explorerTMin = x } rest
    go options ("--t-max" : value : rest) =
      parseDouble "--t-max" value >>= \x ->
        go options { explorerTMax = x } rest
    go options ("--samples" : value : rest) =
      parseInt "--samples" value >>= \x ->
        go options { explorerSamples = x } rest
    go options ("--prime-cells" : rest) =
      go options { explorerPrimeCells = True } rest
    go options ("--output" : path : rest) =
      go options { explorerOutput = Just path,
        explorerOutputFormat = inferFormat path (explorerOutputFormat options) } rest
    go options ("--format" : value : rest) =
      parseFormat value >>= \format ->
        go options { explorerOutputFormat = format } rest
    go options ("--certificate-output" : path : rest) =
      go options { explorerCertificateOutput = Just path } rest
    go _ (flag : _) = Left ("unknown or incomplete Suzuki Explorer option: " ++ flag)

    parseDouble flag text = maybe
      (Left (flag ++ " expects a finite floating-point value"))
      (\x -> if isFinite x then Right x else Left (flag ++ " must be finite"))
      (readMaybe text)
    parseInt flag text = maybe
      (Left (flag ++ " expects an integer")) Right (readMaybe text)

parseFormat :: String -> Either String OutputFormat
parseFormat text = case map toLower text of
  "ascii" -> Right OutputAscii
  "csv" -> Right OutputCsv
  "json" -> Right OutputJson
  _ -> Left "--format expects ascii, csv, or json"

inferFormat :: FilePath -> OutputFormat -> OutputFormat
inferFormat path fallback
  | ".csv" `isSuffixOf` lower = OutputCsv
  | ".json" `isSuffixOf` lower = OutputJson
  | otherwise = fallback
  where lower = map toLower path

validateOptions :: ExplorerOptions -> Either String ExplorerOptions
validateOptions options
  | explorerTMin options < 0 = Left "--t-min must be nonnegative"
  | explorerTMax options <= explorerTMin options = Left "--t-max must exceed --t-min"
  | explorerSamples options < 3 = Left "--samples must be at least 3"
  | explorerSamples options > 200000 = Left "--samples is capped at 200000"
  | otherwise = case
      (explorerOmegaMin options, explorerOmegaMax options,
        explorerOmegaCount options) of
      (Nothing, Nothing, Nothing) -> Right options
      (Just lo, Just hi, Just count)
        | count < 1 -> Left "--omega-count must be positive"
        | hi < lo -> Left "--omega-max must not be below --omega-min"
        | otherwise -> Right options
      _ -> Left "--omega-min, --omega-max, and --omega-count must be supplied together"

resolvedOmegas :: ExplorerOptions -> [Double]
resolvedOmegas options = case
    (explorerOmegaMin options, explorerOmegaMax options,
      explorerOmegaCount options) of
  (Just lo, Just hi, Just count) -> linearGrid count lo hi
  _ | not (null (explorerOmegas options)) -> explorerOmegas options
    | otherwise -> [0.5, 0.25, 0.125, 0]

exploreSuzuki :: ExplorerOptions -> Either String ExplorerReport
exploreSuzuki options = do
  checked <- validateOptions options
  let nMaxDouble = exp (explorerTMax checked)
  if nMaxDouble > 2000000
    then Left "t-max creates more than 2,000,000 arithmetic cells; use a smaller exploratory range"
    else pure ()
  let nMax = max 1 (floor nMaxDouble)
      primes = primesUpTo (nMax + 100)
      events = primeEvents nMax primes
      nodes = explorationNodes checked nMax
      base = buildBasePoints events nodes
      omegaResults = map (exploreOmega checked primes events base) (resolvedOmegas checked)
      summaries = [summary | (summary, _, _) <- omegaResults]
      cells = concat [minima | (_, minima, _) <- omegaResults]
      certificates = concat [certs | (_, _, certs) <- omegaResults]
  pure ExplorerReport
    { reportOptions = checked
    , reportSummaries = summaries
    , reportCellMinima = cells
    , reportCertificates = certificates
    }

runSuzukiExplorer :: ExplorerOptions -> IO ()
runSuzukiExplorer options = case exploreSuzuki options of
  Left err -> putStrLn ("Suzuki Explorer error: " ++ err)
  Right report -> do
    putStr (renderExplorerAscii report)
    case explorerOutput options of
      Nothing -> pure ()
      Just path -> do
        writeFile path (renderSelected (explorerOutputFormat options) report)
        putStrLn ("Wrote NumericalEvidence report to " ++ path)
    case explorerCertificateOutput options of
      Nothing -> pure ()
      Just path -> do
        writeFile path (renderCertificatesJson report)
        putStrLn ("Wrote candidate-only certificate data to " ++ path)

renderSelected :: OutputFormat -> ExplorerReport -> String
renderSelected OutputAscii = renderExplorerAscii
renderSelected OutputCsv = renderExplorerCsv
renderSelected OutputJson = renderExplorerJson

explorationNodes :: ExplorerOptions -> Int -> [Double]
explorationNodes options nMax = dedupeSorted $ sort $
  0 : explorerTMin options : explorerTMax options :
  linearGrid (explorerSamples options) 0 (explorerTMax options) ++
  [log (fromIntegral n) | n <- [1 .. nMax + 1],
    log (fromIntegral n) <= explorerTMax options]

dedupeSorted :: [Double] -> [Double]
dedupeSorted = nubBy (\a b -> abs (a - b) <= 1e-12)

linearGrid :: Int -> Double -> Double -> [Double]
linearGrid count lo hi
  | count <= 1 = [lo]
  | otherwise =
      [lo + fromIntegral k * (hi - lo) / fromIntegral (count - 1)
        | k <- [0 .. count - 1]]

primesUpTo :: Int -> [Int]
primesUpTo limit = takeWhile (<= limit) allPrimes

allPrimes :: [Int]
allPrimes = 2 : filter isPrime [3,5 ..]
  where
    isPrime n = all (\p -> n `mod` p /= 0)
      (takeWhile (\p -> p * p <= n) allPrimes)

primeEvents :: Int -> [Int] -> [PrimeEvent]
primeEvents limit primes = sortOn eventN
  [ PrimeEvent n (log (fromIntegral n)) (log (fromIntegral p))
      (log (fromIntegral p) / sqrt (fromIntegral n))
  | p <- takeWhile (<= limit) primes
  , n <- takeWhile (<= limit) (iterate (* p) p)
  ]

primeContribution :: [PrimeEvent] -> Double -> Double
primeContribution events t = foldl' addEvent 0
  (takeWhile (\event -> eventLogN event <= t + 1e-13) events)
  where
    addEvent total event = total + eventWeight event * (t - eventLogN event)

primeSlope :: [PrimeEvent] -> Double -> Double
primeSlope events t = sum
  [eventWeight event | event <- takeWhile (\event -> eventLogN event <= t + 1e-13) events]

shiftedPrimeContributionNumeric :: [PrimeEvent] -> Double -> Double -> Double
shiftedPrimeContributionNumeric events omega t = foldl' addEvent 0
  (takeWhile (\event -> eventLogN event <= t + 1e-13) events)
  where
    addEvent total event = total + eventWeight event *
      exp (-omega * eventLogN event) * (t - eventLogN event)

eulerGamma :: Double
eulerGamma = 0.5772156649015328606

digammaQuarter :: Double
digammaQuarter = -eulerGamma - pi / 2 - 3 * log 2

suzukiDerivativeConstant :: Double
suzukiDerivativeConstant = (digammaQuarter - log pi) / 2 + pi / 2

artanhExpNegHalf :: Double -> Double
artanhExpNegHalf t
  | t <= 0 = 1 / 0
  | t < 1e-8 = 0.5 * log (4 / t)
  | otherwise =
      let q = exp (-t / 2)
      in 0.5 * (log (1 + q) - log (1 - q))

archimedeanDerivative :: Double -> Double
archimedeanDerivative t =
  2 * (exp (t / 2) - exp (-t / 2)) + suzukiDerivativeConstant -
    atan (exp (t / 2)) + artanhExpNegHalf t

integrateArchDerivative :: Double -> Double -> Double
integrateArchDerivative a b
  | b <= a = 0
  | a <= 0 = adaptiveSimpson 1e-11 18 transformed 0 1
  | otherwise = adaptiveSimpson 1e-11 18 archimedeanDerivative a b
  where
    transformed x
      | x <= 0 = 0
      | otherwise =
          let t = b * x * x
          in archimedeanDerivative t * 2 * b * x

buildBasePoints :: [PrimeEvent] -> [Double] -> [BasePoint]
buildBasePoints events nodes = reverse points
  where
    (_, points) = foldl' step (0, []) nodes
    step (_, []) t =
      let arch = if t <= 0 then 0 else integrateArchDerivative 0 t
          prime = primeContribution events t
          psi = arch - prime
          derivative = if t <= 0 then 1 / 0
            else archimedeanDerivative t - primeSlope events t
      in (arch, [BasePoint t arch prime psi derivative])
    step (previousArch, previousPoint : rest) t =
      let arch = previousArch + integrateArchDerivative (baseT previousPoint) t
          prime = primeContribution events t
          psi = arch - prime
          derivative = if t <= 0 then 1 / 0
            else archimedeanDerivative t - primeSlope events t
      in (arch, BasePoint t arch prime psi derivative : previousPoint : rest)

suzukiPsiNumeric :: Double -> Double
suzukiPsiNumeric t
  | t == 0 = 0
  | t < 0 = suzukiPsiNumeric (-t)
  | exp t > 2000000 = 0 / 0
  | otherwise =
      let events = primeEvents (max 1 (floor (exp t)))
            (primesUpTo (max 2 (floor (exp t))))
      in integrateArchDerivative 0 t - primeContribution events t

exploreOmega :: ExplorerOptions -> [Int] -> [PrimeEvent] -> [BasePoint]
  -> Double -> (OmegaSummary, [CellMinimum], [CandidateCertificate])
exploreOmega options primes events base omega =
  let shifted = buildShiftPoints events base omega
      relevant = filter (inRequestedRange options . shiftT) shifted
      global = minimumBy (comparing shiftValue) relevant
      cells = cellMinima options primes events omega relevant
      certificates = map (affineCandidateCertificate options relevant) cells
      summary = OmegaSummary omega (shiftValue global) (shiftT global)
        (cellForT (shiftT global)) (maximum (0 : map crossError shifted))
  in (summary, cells, certificates)
  where crossError point = abs (shiftValue point - shiftCrossValue point)

inRequestedRange :: ExplorerOptions -> Double -> Bool
inRequestedRange options t =
  explorerTMin options - 1e-12 <= t && t <= explorerTMax options + 1e-12

buildShiftPoints :: [PrimeEvent] -> [BasePoint] -> Double -> [ShiftPoint]
buildShiftPoints events base omega = reverse points
  where
    (_, _, _, _, _, _, points) =
      foldl' step (0, 0, 0, 0, 0, Nothing, []) base
    step (_, _, _, _, _, Nothing, []) point =
      let t = baseT point
          value = basePsi point
          crossValue = baseArchimedean point - basePrime point
      in (0, 0, 0, 0, t, Just point,
        [ShiftPoint t value (basePsiDerivative point) crossValue])
    step (j0, j1, archJ0, archJ1, _, Just previous, acc) point =
      let t0 = baseT previous
          t1 = baseT point
          dt = t1 - t0
          g0 = exp (-omega * t0) * basePsi previous
          g1 = exp (-omega * t1) * basePsi point
          h0 = t0 * g0
          h1 = t1 * g1
          nextJ0 = j0 + dt * (g0 + g1) / 2
          nextJ1 = j1 + dt * (h0 + h1) / 2
          archG0 = exp (-omega * t0) * baseArchimedean previous
          archG1 = exp (-omega * t1) * baseArchimedean point
          nextArchJ0 = archJ0 + dt * (archG0 + archG1) / 2
          nextArchJ1 = archJ1 + dt * (t0 * archG0 + t1 * archG1) / 2
          value = g1 + 2 * omega * nextJ0 +
            omega * omega * (t1 * nextJ0 - nextJ1)
          derivative = exp (-omega * t1) *
            (basePsiDerivative point + omega * basePsi point) +
              omega * omega * nextJ0
          archValue = archG1 + 2 * omega * nextArchJ0 +
            omega * omega * (t1 * nextArchJ0 - nextArchJ1)
          crossValue = archValue - shiftedPrimeContributionNumeric events omega t1
      in (nextJ0, nextJ1, nextArchJ0, nextArchJ1, t1, Just point,
        ShiftPoint t1 value derivative crossValue : acc)
    step state _ = state

cellMinima :: ExplorerOptions -> [Int] -> [PrimeEvent] -> Double
  -> [ShiftPoint] -> [CellMinimum]
cellMinima options primes events omega points =
  let firstCell = max 1 (floor (exp (explorerTMin options)))
      lastCell = max firstCell (floor (exp (explorerTMax options)))
      indices = [firstCell .. lastCell]
      cells = mapMaybeCell (minimumOnCell options primes events omega points) indices
  in if explorerPrimeCells options then cells else take 24 (sortOn cellCandidateValue cells)

mapMaybeCell :: (a -> Maybe b) -> [a] -> [b]
mapMaybeCell f = foldr (\x rest -> maybe rest (: rest) (f x)) []

minimumOnCell :: ExplorerOptions -> [Int] -> [PrimeEvent] -> Double
  -> [ShiftPoint] -> Int -> Maybe CellMinimum
minimumOnCell options primes events omega points n =
  let left = max (explorerTMin options) (log (fromIntegral n))
      right = min (explorerTMax options) (log (fromIntegral (n + 1)))
      inside = filter (\point -> left - 1e-12 <= shiftT point &&
        shiftT point <= right + 1e-12) points
      candidates = inside ++ derivativeRootCandidates inside
  in if right < left || null candidates then Nothing else
      let best = minimumBy (comparing shiftValue) candidates
          t = shiftT best
          value = shiftValue best
          metadata = primeMetadata primes events n
      in Just CellMinimum
        { cellOmega = omega
        , cellIndex = n
        , cellLeft = left
        , cellRight = right
        , cellCandidateT = t
        , cellCandidateValue = value
        , cellDerivative = shiftDerivative best
        , cellPsiOverT = safeDivide value t
        , cellPsiOverTSq = safeDivide value (t * t)
        , cellExpNegHalfPsi = exp (-t / 2) * value
        , cellExpNegOmegaPsi = exp (-omega * t) * value
        , cellOmegaTimesT = omega * t
        , cellMetadata = metadata
        }

derivativeRootCandidates :: [ShiftPoint] -> [ShiftPoint]
derivativeRootCandidates points = mapMaybeCell root (zip points (drop 1 points))
  where
    root (left, right)
      | not (isFinite dl && isFinite dr) = Nothing
      | dl == dr = Nothing
      | dl * dr > 0 = Nothing
      | otherwise =
          let ratio = max 0 (min 1 ((-dl) / (dr - dl)))
              t = shiftT left + ratio * (shiftT right - shiftT left)
              value = shiftValue left + ratio * (shiftValue right - shiftValue left)
              crossValue = shiftCrossValue left +
                ratio * (shiftCrossValue right - shiftCrossValue left)
          in Just (ShiftPoint t value 0 crossValue)
      where
        dl = shiftDerivative left
        dr = shiftDerivative right

cellForT :: Double -> Int
cellForT t = max 1 (floor (exp (max 0 t)))

primeMetadata :: [Int] -> [PrimeEvent] -> Int -> PrimeMetadata
primeMetadata primes events n = PrimeMetadata
  { metadataPreviousPrime = previous
  , metadataNextPrime = next
  , metadataPrimeGap = (-) <$> next <*> previous
  , metadataChebyshevTheta = sum [log (fromIntegral p) | p <- primes, p <= n]
  , metadataChebyshevPsi = psiValue
  , metadataPsiMinusN = psiValue - fromIntegral n
  , metadataLeftPrimePower = any ((== n) . eventN) events
  , metadataRightPrimePower = any ((== n + 1) . eventN) events
  }
  where
    previous = lastMaybe (takeWhile (<= n) primes)
    next = firstMaybe (dropWhile (<= n) primes)
    psiValue = sum [eventMangoldt event | event <- events, eventN event <= n]

firstMaybe :: [a] -> Maybe a
firstMaybe [] = Nothing
firstMaybe (x : _) = Just x

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just (last xs)

affineCandidateCertificate :: ExplorerOptions -> [ShiftPoint] -> CellMinimum
  -> CandidateCertificate
affineCandidateCertificate options points minimumValue =
  let precision = max 1e-12
        ((explorerTMax options - explorerTMin options) /
          fromIntegral (explorerSamples options - 1))
      samples = filter (\point -> cellLeft minimumValue - 1e-12 <= shiftT point &&
        shiftT point <= cellRight minimumValue + 1e-12) points
      derivativeScale = maximum (1 :
        [abs (shiftDerivative point) | point <- samples,
          isFinite (shiftDerivative point)])
      slopes = linearGrid 129 (-derivativeScale) derivativeScale
      safety = max 1e-12 (precision * precision)
      fit trialSlope =
        let trialIntercept = minimum
              [shiftValue point - trialSlope * shiftT point | point <- samples] - safety
            trialMinimum = min
              (trialIntercept + trialSlope * cellLeft minimumValue)
              (trialIntercept + trialSlope * cellRight minimumValue)
        in (trialMinimum, trialIntercept, trialSlope)
      (_, rawIntercept, rawSlope) = maximumBy (comparing first3) (map fit slopes)
      (interceptNumerator, denominator) = rationalDown rawIntercept
      (slopeNumerator, _) = rationalDown rawSlope
      intercept = fromIntegral interceptNumerator / fromIntegral denominator
      slope = fromIntegral slopeNumerator / fromIntegral denominator
      residual = minimum
        [shiftValue point - (intercept + slope * shiftT point) | point <- samples]
      lineMinimum = min
        (intercept + slope * cellLeft minimumValue)
        (intercept + slope * cellRight minimumValue)
      status
        | lineMinimum >= 0 && residual >= negate safety = NumericallyPassed
        | cellCandidateValue minimumValue < -10 * precision = NumericallyFailed
        | otherwise = Candidate
  in CandidateCertificate
    { certificateOmega = cellOmega minimumValue
    , certificateLeft = cellLeft minimumValue
    , certificateRight = cellRight minimumValue
    , certificatePrimeCell = cellIndex minimumValue
    , certificateBasis = ["1", "t"]
    , certificateCoefficients =
        [(interceptNumerator, denominator), (slopeNumerator, denominator)]
    , certificateClaimedMinimum = lineMinimum
    , certificateDiscoveryPrecision = precision
    , certificateStatus = status
    }

first3 :: (a, b, c) -> a
first3 (x, _, _) = x

rationalDown :: Double -> (Integer, Integer)
rationalDown value = (floor (value * fromIntegral denominator), denominator)
  where denominator = 1000000

safeDivide :: Double -> Double -> Double
safeDivide numerator denominator
  | denominator == 0 = 0 / 0
  | otherwise = numerator / denominator

adaptiveSimpson :: Double -> Int -> (Double -> Double) -> Double -> Double -> Double
adaptiveSimpson tolerance maxDepth f a b = recurse maxDepth a b fa fm fb whole
  where
    midpoint = (a + b) / 2
    fa = f a
    fm = f midpoint
    fb = f b
    whole = simpsonValues a b fa fm fb
    recurse depth left right fLeft fMid fRight estimate =
      let middle = (left + right) / 2
          leftMid = (left + middle) / 2
          rightMid = (middle + right) / 2
          fLeftMid = f leftMid
          fRightMid = f rightMid
          leftEstimate = simpsonValues left middle fLeft fLeftMid fMid
          rightEstimate = simpsonValues middle right fMid fRightMid fRight
          delta = leftEstimate + rightEstimate - estimate
      in if depth <= 0 || abs delta <= 15 * tolerance
          then leftEstimate + rightEstimate + delta / 15
          else recurse (depth - 1) left middle fLeft fLeftMid fMid leftEstimate +
            recurse (depth - 1) middle right fMid fRightMid fRight rightEstimate

simpsonValues :: Double -> Double -> Double -> Double -> Double -> Double
simpsonValues a b fa fm fb = (b - a) * (fa + 4 * fm + fb) / 6

isFinite :: Double -> Bool
isFinite x = not (isNaN x || isInfinite x)

renderExplorerAscii :: ExplorerReport -> String
renderExplorerAscii report = unlines $
  [ "Suzuki positivity explorer (NumericalEvidence only)"
  , "----------------------------------------------------"
  , "Finite-range numerical positivity is not sufficient evidence for RH."
  , ""
  , "omega       min Psi_omega       t*          cell      cross-check"
  , "------------------------------------------------------------------"
  ] ++ map renderSummary (reportSummaries report) ++
  [ ""
  , "Most dangerous prime cells (candidate minima):"
  , "omega       cell       left          right         min Psi        t*"
  , "------------------------------------------------------------------------"
  ] ++ map renderCell (take 16 (sortOn cellCandidateValue (reportCellMinima report))) ++
  [ ""
  , "Candidate certificate statuses are sampled numerical results only."
  ]
  where
    renderSummary summary = intercalate "  "
      [pad 10 (fmt 6 (summaryOmega summary))
      , pad 19 (fmt 10 (summaryMinimum summary))
      , pad 11 (fmt 6 (summaryArgmin summary))
      , pad 9 (show (summaryCell summary))
      , fmt 4 (summaryCrossCheckError summary)]
    renderCell cell = intercalate "  "
      [pad 10 (fmt 6 (cellOmega cell))
      , pad 10 (show (cellIndex cell))
      , pad 13 (fmt 7 (cellLeft cell))
      , pad 13 (fmt 7 (cellRight cell))
      , pad 14 (fmt 8 (cellCandidateValue cell))
      , fmt 7 (cellCandidateT cell)]

renderExplorerCsv :: ExplorerReport -> String
renderExplorerCsv report = unlines $
  ["trust,status,omega,cell,t_left,t_right,t_candidate,psi,derivative,psi_over_t,psi_over_t2,exp_neg_half_psi,exp_neg_omega_psi,omega_t,prime_gap,theta,chebyshev_psi,psi_minus_n,left_prime_power,right_prime_power"] ++
  map renderCellCsv (reportCellMinima report)
  where
    renderCellCsv cell = intercalate ","
      ["NumericalEvidence"
      ,statusText (statusForCell cell)
      ,num (cellOmega cell), show (cellIndex cell), num (cellLeft cell)
      ,num (cellRight cell), num (cellCandidateT cell), num (cellCandidateValue cell)
      ,num (cellDerivative cell), num (cellPsiOverT cell), num (cellPsiOverTSq cell)
      ,num (cellExpNegHalfPsi cell), num (cellExpNegOmegaPsi cell)
      ,num (cellOmegaTimesT cell), maybe "" show (metadataPrimeGap metadata)
      ,num (metadataChebyshevTheta metadata), num (metadataChebyshevPsi metadata)
      ,num (metadataPsiMinusN metadata), boolText (metadataLeftPrimePower metadata)
      ,boolText (metadataRightPrimePower metadata)]
      where metadata = cellMetadata cell
    statusForCell cell = case filter matches (reportCertificates report) of
      certificate : _ -> certificateStatus certificate
      [] -> Candidate
      where
        matches certificate = certificateOmega certificate == cellOmega cell &&
          certificatePrimeCell certificate == cellIndex cell

renderExplorerJson :: ExplorerReport -> String
renderExplorerJson report = unlines
  ["{"
  ,"  \"trust\": \"NumericalEvidence\","
  ,"  \"warning\": \"Numerical positivity over any finite range is not evidence sufficient for RH.\","
  ,"  \"summaries\": ["
  ,intercalate ",\n" (map (indent 4 . summaryJson) (reportSummaries report))
  ,"  ],"
  ,"  \"cell_minima\": ["
  ,intercalate ",\n" (map (indent 4 . cellJson) (reportCellMinima report))
  ,"  ]"
  ,"}"
  ]

renderCertificatesJson :: ExplorerReport -> String
renderCertificatesJson report = unlines
  ["{"
  ,"  \"trust\": \"NumericalEvidence\","
  ,"  \"warning\": \"Candidate coefficients require independent rationalization and Lean verification.\","
  ,"  \"certificates\": ["
  ,intercalate ",\n" (map (indent 4 . certificateJson) (reportCertificates report))
  ,"  ]"
  ,"}"
  ]

summaryJson :: OmegaSummary -> String
summaryJson summary = "{" ++ intercalate ", "
  [jsonField "omega" (num (summaryOmega summary))
  ,jsonField "minimum" (num (summaryMinimum summary))
  ,jsonField "minimizing_t" (num (summaryArgmin summary))
  ,jsonField "prime_cell" (show (summaryCell summary))
  ,jsonField "cross_check_error" (num (summaryCrossCheckError summary))] ++ "}"

cellJson :: CellMinimum -> String
cellJson cell = "{" ++ intercalate ", "
  [jsonField "omega" (num (cellOmega cell))
  ,jsonField "prime_cell" (show (cellIndex cell))
  ,jsonField "t_left" (num (cellLeft cell))
  ,jsonField "t_right" (num (cellRight cell))
  ,jsonField "minimizing_t_candidate" (num (cellCandidateT cell))
  ,jsonField "minimum_candidate" (num (cellCandidateValue cell))
  ,jsonField "derivative" (num (cellDerivative cell))
  ,jsonField "psi_over_t" (num (cellPsiOverT cell))
  ,jsonField "psi_over_t2" (num (cellPsiOverTSq cell))
  ,jsonField "exp_neg_half_psi" (num (cellExpNegHalfPsi cell))
  ,jsonField "exp_neg_omega_psi" (num (cellExpNegOmegaPsi cell))
  ,jsonField "omega_times_t" (num (cellOmegaTimesT cell))
  ,jsonField "prime_gap" (maybe "null" show (metadataPrimeGap metadata))
  ,jsonField "chebyshev_theta" (num (metadataChebyshevTheta metadata))
  ,jsonField "chebyshev_psi" (num (metadataChebyshevPsi metadata))
  ,jsonField "chebyshev_psi_minus_n" (num (metadataPsiMinusN metadata))
  ,jsonField "left_boundary_prime_power" (jsonBool (metadataLeftPrimePower metadata))
  ,jsonField "right_boundary_prime_power" (jsonBool (metadataRightPrimePower metadata))] ++ "}"
  where metadata = cellMetadata cell

certificateJson :: CandidateCertificate -> String
certificateJson certificate = "{" ++ intercalate ", "
  [jsonStringField "trust" "NumericalEvidence"
  ,jsonStringField "status" (statusText (certificateStatus certificate))
  ,jsonField "omega" (num (certificateOmega certificate))
  ,jsonField "t_interval" ("[" ++ num (certificateLeft certificate) ++ ", " ++
      num (certificateRight certificate) ++ "]")
  ,jsonField "prime_cell" (show (certificatePrimeCell certificate))
  ,jsonField "basis" ("[" ++ intercalate ", "
      (map jsonString (certificateBasis certificate)) ++ "]")
  ,jsonField "coefficients" ("[" ++ intercalate ", "
      (map rationalJson (certificateCoefficients certificate)) ++ "]")
  ,jsonField "claimed_lower_bound" (num (certificateClaimedMinimum certificate))
  ,jsonField "discovery_precision" (num (certificateDiscoveryPrecision certificate))] ++ "}"

rationalJson :: (Integer, Integer) -> String
rationalJson (numerator, denominator) = "{" ++ intercalate ", "
  [jsonField "numerator" (show numerator), jsonField "denominator" (show denominator)] ++ "}"

jsonField :: String -> String -> String
jsonField name value = jsonString name ++ ": " ++ value

jsonStringField :: String -> String -> String
jsonStringField name value = jsonField name (jsonString value)

jsonString :: String -> String
jsonString text = show text

jsonBool :: Bool -> String
jsonBool True = "true"
jsonBool False = "false"

boolText :: Bool -> String
boolText True = "true"
boolText False = "false"

statusText :: CandidateStatus -> String
statusText Candidate = "candidate"
statusText NumericallyPassed = "numerically_passed"
statusText NumericallyFailed = "numerically_failed"

indent :: Int -> String -> String
indent count text = replicate count ' ' ++ text

num :: Double -> String
num value
  | isNaN value || isInfinite value = "null"
  | otherwise = showFFloat (Just 12) value ""

fmt :: Int -> Double -> String
fmt digits value
  | isNaN value = "nan"
  | isInfinite value = if value > 0 then "inf" else "-inf"
  | otherwise = showFFloat (Just digits) value ""

pad :: Int -> String -> String
pad width text = take width (text ++ repeat ' ')
