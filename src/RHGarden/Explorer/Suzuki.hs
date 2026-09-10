module RHGarden.Explorer.Suzuki
  ( CandidateStatus(..)
  , ExplorerMode(..)
  , ExplorerOptions(..)
  , ExplorerReport(..)
  , OmegaSummary(..)
  , CellMinimum(..)
  , CriticalPoint(..)
  , CriticalClassification(..)
  , BranchPoint(..)
  , EnvelopeCrossing(..)
  , BifurcationEvent(..)
  , CellMargin(..)
  , BlockMargin(..)
  , DualDynamics(..)
  , BusyPeriod(..)
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
  , psiShiftedNumeric
  , dPsiDt
  , d2PsiDt2
  ) where

import Data.Char (toLower)
import Data.List (intercalate, isSuffixOf, maximumBy, minimumBy,
  nubBy, sort, sortOn)
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

data ExplorerMode
  = ScanMode
  | BranchesMode
  | CrossingsMode
  | CellMode
  | ClusterMode
  | CertificateStatusMode
  | MarginsMode
  | BlocksMode
  | DualMode
  | RootsMode
  | BusyMode
  deriving (Eq, Ord, Show, Read)

data ExplorerOptions = ExplorerOptions
  { explorerMode :: ExplorerMode
  , explorerOmegas :: [Double]
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
  , explorerCellMin :: Maybe Int
  , explorerCellMax :: Maybe Int
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
  , cellSecondDerivative :: Double
  , cellDistanceAboveBest :: Double
  , cellPsiOverT :: Double
  , cellPsiOverTSq :: Double
  , cellExpNegHalfPsi :: Double
  , cellExpNegOmegaPsi :: Double
  , cellOmegaTimesT :: Double
  , cellMetadata :: PrimeMetadata
  } deriving (Eq, Show)

data CriticalClassification
  = LocalMinimum
  | LocalMaximum
  | CriticalUncertain
  deriving (Eq, Ord, Show, Read)

data CriticalPoint = CriticalPoint
  { criticalOmega :: Double
  , criticalCell :: Int
  , criticalT :: Double
  , criticalValue :: Double
  , criticalDerivative :: Double
  , criticalSecondDerivative :: Double
  , criticalMixedDerivative :: Double
  , criticalClassification :: CriticalClassification
  } deriving (Eq, Show)

data BranchPoint = BranchPoint
  { branchId :: String
  , branchCell :: Int
  , branchOmega :: Double
  , branchT :: Double
  , branchMinimum :: Double
  , branchCurvature :: Double
  , branchDtDomega :: Double
  } deriving (Eq, Show)

data EnvelopeCrossing = EnvelopeCrossing
  { crossingOmega :: Double
  , crossingCellA :: Int
  , crossingCellB :: Int
  , crossingTA :: Double
  , crossingTB :: Double
  , crossingCommonMinimum :: Double
  } deriving (Eq, Show)

data BifurcationEvent = BifurcationEvent
  { bifurcationOmega :: Double
  , bifurcationCell :: Int
  , bifurcationT :: Double
  , bifurcationKind :: String
  , bifurcationCurvature :: Double
  } deriving (Eq, Show)

data OmegaSummary = OmegaSummary
  { summaryOmega :: Double
  , summaryMinimum :: Double
  , summaryArgmin :: Double
  , summaryCell :: Int
  , summaryCrossCheckError :: Double
  , summaryDerivativeCheckError :: Double
  } deriving (Eq, Show)

-- | Numerical evaluation of the exact two-number state
-- `(S_n,C_n)` and its restricted-dual margin.  These rows remain
-- NumericalEvidence until their inequalities are separately checked by Lean.
data CellMargin = CellMargin
  { marginCell :: Int
  , marginSlope :: Double
  , marginIntercept :: Double
  , marginDual :: Double
  , marginValue :: Double
  , marginCandidateT :: Double
  , marginMinimizerType :: String
  , marginMangoldtLeft :: Double
  , marginMangoldtRight :: Double
  , marginSinceLastEvent :: Maybe Int
  , marginToNextEvent :: Maybe Int
  } deriving (Eq, Show)

-- | Numerical evaluation of one complete constant Mangoldt-state block.
-- The event endpoints, state, slope deficits, and unique optimizer are all
-- discovery data; the corresponding abstract structure is checked in Lean.
data BlockMargin = BlockMargin
  { blockLeftEvent :: Int
  , blockRightEvent :: Int
  , blockGap :: Int
  , blockSlope :: Double
  , blockIntercept :: Double
  , blockSlopeDeficitLeft :: Double
  , blockSlopeDeficitRight :: Double
  , blockCandidateT :: Double
  , blockCandidateExpT :: Double
  , blockMarginValue :: Double
  , blockMinimizerType :: String
  , blockWinningCell :: Int
  } deriving (Eq, Show)

-- | Numerical shadow of the Lean-checked Legendre-dual event dynamics.
-- Every field remains NumericalEvidence: it is useful for discovering an
-- invariant, but it is never promoted to a formal positivity assertion.
data DualDynamics = DualDynamics
  { dualEvent :: Int
  , dualNextEvent :: Int
  , dualLambda :: Double
  , dualSlope :: Double
  , dualIntercept :: Double
  , dualOptimizer :: Double
  , dualArchDual :: Double
  , dualGlobalMargin :: Double
  , dualDeficit :: Double
  , dualArchDrift :: Double
  , dualNextImpulse :: Double
  , dualPredictedNextDeficit :: Double
  , dualActive :: Bool
  , dualBlockMargin :: Double
  , dualBlockEqualsGlobal :: Bool
  , dualEventAreaUpdate :: Double
  , dualEventValue :: Double
  , dualSafetyEnergy :: Double
  , dualSafetySlack :: Double
  , dualCurvatureLower :: Double
  , dualExactCurvature :: Double
  , dualCurvatureSafetyEnergy :: Double
  , dualExactCurvatureSafetyEnergy :: Double
  , dualCurvatureSafetySlack :: Double
  , dualLogGap :: Double
  , dualConvexRemainder :: Double
  , dualOptimizerDisplacement :: Double
  , dualKickDisplacement :: Double
  , dualKickArea :: Double
  , dualPreKickDisplacement :: Double
  , dualPostKickDisplacement :: Double
  , dualBacklogBefore :: Double
  , dualBacklogAfter :: Double
  , dualKickOverLambda :: Double
  , dualKickOverLogGap :: Double
  , dualPrimeScaleKickBound :: Double
  , dualCurvatureScaledDeficit :: Double
  , dualImpulseOverDrift :: Double
  , dualImpulseOverLogGap :: Double
  , dualDriftOverLogGap :: Double
  , dualRootOptimizer :: Double
  , dualNextRootOptimizer :: Double
  , dualSqrtEvent :: Double
  , dualSqrtNextEvent :: Double
  , dualRootDisplacement :: Double
  , dualRootRatio :: Double
  , dualRootKick :: Double
  , dualRootKickLower :: Double
  , dualRootKickUpper :: Double
  , dualSqrtGap :: Double
  , dualRootKickOverGap :: Double
  , dualNormalizedRootImpulse :: Double
  , dualCrudeGapCondition :: Bool
  } deriving (Eq, Show)

-- | A maximal numerically detected interval on which the right-continuous
-- root-slope discrepancy is negative.  A period may cross several Mangoldt
-- impulses before smooth archimedean service returns the discrepancy to zero.
-- These records are NumericalEvidence only.
data BusyPeriod = BusyPeriod
  { busyStartEvent :: Int
  , busyRecoveryBeforeEvent :: Int
  , busyEventCount :: Int
  , busyRootStart :: Double
  , busyRootEnd :: Double
  , busyRootWidth :: Double
  , busyTWidth :: Double
  , busyStartingDiscrepancy :: Double
  , busyMostNegativeDiscrepancy :: Double
  , busyEndingDiscrepancy :: Double
  , busyWeightedLoss :: Double
  , busyPsiStart :: Double
  , busyPsiEnd :: Double
  , busyMinimumPsi :: Double
  , busyArrivalMass :: Double
  , busyServiceDrift :: Double
  , busyLossOverReserve :: Double
  , busyLossTimesSqrtStart :: Double
  , busyLossOverInitialBacklogSq :: Double
  , busyMaxBacklogOverSqrtStart :: Double
  , busyArrivalOverService :: Double
  } deriving (Eq, Show)

data CandidateCertificate = CandidateCertificate
  { certificateOmega :: Double
  , certificateLeft :: Double
  , certificateRight :: Double
  , certificatePrimeCell :: Int
  , certificateBasis :: [String]
  , certificateCoefficients :: [(Integer, Integer)]
  , certificateStrongSample :: (Integer, Integer)
  , certificateStrongValueLower :: (Integer, Integer)
  , certificateStrongDerivAbsUpper :: (Integer, Integer)
  , certificateStrongCurvatureLower :: (Integer, Integer)
  , certificateStrongMargin :: Double
  , certificateClaimedMinimum :: Double
  , certificateDiscoveryPrecision :: Double
  , certificateStatus :: CandidateStatus
  } deriving (Eq, Show)

data ExplorerReport = ExplorerReport
  { reportOptions :: ExplorerOptions
  , reportSummaries :: [OmegaSummary]
  , reportCellMinima :: [CellMinimum]
  , reportCertificates :: [CandidateCertificate]
  , reportCriticalPoints :: [CriticalPoint]
  , reportBranches :: [BranchPoint]
  , reportCrossings :: [EnvelopeCrossing]
  , reportBifurcations :: [BifurcationEvent]
  , reportMargins :: [CellMargin]
  , reportBlockMargins :: [BlockMargin]
  , reportDualDynamics :: [DualDynamics]
  , reportBusyPeriods :: [BusyPeriod]
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
  , basePsiSecondDerivative :: Double
  } deriving (Eq, Show)

data ShiftPoint = ShiftPoint
  { shiftT :: Double
  , shiftValue :: Double
  , shiftDerivative :: Double
  , shiftSecondDerivative :: Double
  , shiftMixedDerivative :: Double
  , shiftCrossValue :: Double
  } deriving (Eq, Show)

defaultExplorerOptions :: ExplorerOptions
defaultExplorerOptions = ExplorerOptions
  { explorerMode = ScanMode
  , explorerOmegas = []
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
  , explorerCellMin = Nothing
  , explorerCellMax = Nothing
  }

parseExplorerOptions :: [String] -> Either String ExplorerOptions
parseExplorerOptions = go defaultExplorerOptions
  where
    go options [] = validateOptions options
    go options ("branches" : rest) =
      go options { explorerMode = BranchesMode } rest
    go options ("crossings" : rest) =
      go options { explorerMode = CrossingsMode } rest
    go options ("cell" : rest) =
      go options { explorerMode = CellMode, explorerPrimeCells = True } rest
    go options ("cluster" : rest) =
      go options { explorerMode = ClusterMode, explorerPrimeCells = True } rest
    go options ("certificate-status" : rest) =
      go options { explorerMode = CertificateStatusMode } rest
    go options ("margins" : rest) =
      go options { explorerMode = MarginsMode, explorerPrimeCells = True,
        explorerOmegas = [0] } rest
    go options ("blocks" : rest) =
      go options { explorerMode = BlocksMode, explorerPrimeCells = True,
        explorerOmegas = [0] } rest
    go options ("dual" : rest) =
      go options { explorerMode = DualMode, explorerPrimeCells = True,
        explorerOmegas = [0] } rest
    go options ("roots" : rest) =
      go options { explorerMode = RootsMode, explorerPrimeCells = True,
        explorerOmegas = [0] } rest
    go options ("busy" : rest) =
      go options { explorerMode = BusyMode, explorerPrimeCells = True,
        explorerOmegas = [0] } rest
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
    go options ("--cell-min" : value : rest) =
      parseInt "--cell-min" value >>= \x ->
        go options { explorerCellMin = Just x } rest
    go options ("--cell-max" : value : rest) =
      parseInt "--cell-max" value >>= \x ->
        go options { explorerCellMax = Just x } rest
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
  | maybe False (< 1) (explorerCellMin options) = Left "--cell-min must be positive"
  | maybe False (< 1) (explorerCellMax options) = Left "--cell-max must be positive"
  | case (explorerCellMin options, explorerCellMax options) of
      (Just lo, Just hi) -> hi < lo
      _ -> False = Left "--cell-max must not be below --cell-min"
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
  _ | explorerMode options `elem`
      [MarginsMode, BlocksMode, DualMode, RootsMode, BusyMode] -> [0]
    | not (null (explorerOmegas options)) -> explorerOmegas options
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
      omegaResults
        | explorerMode checked `elem` [DualMode, RootsMode, BusyMode] = []
        | otherwise = map (exploreOmega checked primes events base) (resolvedOmegas checked)
      summaries = [summary | (summary, _, _, _) <- omegaResults]
      rawCells = concat [minima | (_, minima, _, _) <- omegaResults]
      cells = map attachDistance rawCells
      certificates = concat [certs | (_, _, certs, _) <- omegaResults]
      criticals = concat [roots | (_, _, _, roots) <- omegaResults]
      branches = trackMinimumBranches criticals
      crossings = refineEnvelopeCrossings checked primes events base summaries
      bifurcations = detectBifurcations criticals
      margins = buildCellMargins events
        [cell | cell <- cells, abs (cellOmega cell) < 1e-12]
      blocks = buildBlockMargins checked events
      dualRows = buildDualDynamics checked events
      busyPeriods = buildBusyPeriods dualRows
      attachDistance cell = cell
        { cellDistanceAboveBest = cellCandidateValue cell -
            minimum [summaryMinimum summary | summary <- summaries,
              abs (summaryOmega summary - cellOmega cell) < 1e-12] }
  pure ExplorerReport
    { reportOptions = checked
    , reportSummaries = summaries
    , reportCellMinima = cells
    , reportCertificates = certificates
    , reportCriticalPoints = criticals
    , reportBranches = branches
    , reportCrossings = crossings
    , reportBifurcations = bifurcations
    , reportMargins = margins
    , reportBlockMargins = blocks
    , reportDualDynamics = dualRows
    , reportBusyPeriods = busyPeriods
    }

-- | Collapse the event stream into completed maximal negative-discrepancy
-- excursions.  Within each block the discrepancy is strictly increasing, so
-- `d_q + G(q,r) >= 0` identifies the unique smooth recovery point.  If it is
-- still negative at the next event, the next Mangoldt kick continues the same
-- busy period.
buildBusyPeriods :: [DualDynamics] -> [BusyPeriod]
buildBusyPeriods = seek
  where
    tolerance = 1e-12
    seek [] = []
    seek (row : rows)
      | dualDeficit row < (-tolerance) = case consume [row] row rows of
          Nothing -> []
          Just (period, remaining) -> period : seek remaining
      | otherwise = seek rows
    consume accumulated current remaining
      | dualDeficit current + dualArchDrift current >= (-tolerance) =
          Just (finish (reverse accumulated), remaining)
      | otherwise = case remaining of
          [] -> Nothing
          next : rest -> consume (next : accumulated) next rest
    finish rows = BusyPeriod
      { busyStartEvent = dualEvent first
      , busyRecoveryBeforeEvent = dualNextEvent final
      , busyEventCount = length rows
      , busyRootStart = rootStart
      , busyRootEnd = rootEnd
      , busyRootWidth = rootEnd - rootStart
      , busyTWidth = dualOptimizer final - log (fromIntegral (dualEvent first))
      , busyStartingDiscrepancy = startD
      , busyMostNegativeDiscrepancy = minimum (map dualDeficit rows)
      , busyEndingDiscrepancy = 0
      , busyWeightedLoss = loss
      , busyPsiStart = psiStart
      , busyPsiEnd = psiEnd
      , busyMinimumPsi = psiEnd
      , busyArrivalMass = arrival
      , busyServiceDrift = service
      , busyLossOverReserve = safeRatio loss psiStart
      , busyLossTimesSqrtStart = loss * rootStart
      , busyLossOverInitialBacklogSq = safeRatio loss (startD * startD)
      , busyMaxBacklogOverSqrtStart = safeRatio
          (maximum (map (max 0 . negate . dualDeficit) rows)) rootStart
      , busyArrivalOverService = safeRatio arrival service
      }
      where
        first = head rows
        final = last rows
        initialRows = init rows
        rootStart = dualSqrtEvent first
        rootEnd = dualRootOptimizer final
        startD = dualDeficit first
        psiStart = dualEventValue first
        psiEnd = dualBlockMargin final
        loss = psiStart - psiEnd
        arrival = sum (map dualNextImpulse initialRows)
        service = sum (map dualArchDrift initialRows) - dualDeficit final
        safeRatio numerator denominator
          | abs denominator < 1e-15 = 0 / 0
          | otherwise = numerator / denominator

buildDualDynamics :: ExplorerOptions -> [PrimeEvent] -> [DualDynamics]
buildDualDynamics options events = case events of
    [] -> []
    firstEvent : _ -> go 0 0
      (integrateArchDerivative 0 (eventLogN firstEvent)) events
  where
    go _ _ _ [] = []
    go _ _ _ [_] = []
    go preSlope preIntercept archLeft (event : nextEvent : rest) =
      let slope = preSlope + eventWeight event
          intercept = preIntercept + eventWeight event * eventLogN event
          archRight = archLeft + integrateArchDerivative
            (eventLogN event) (eventLogN nextEvent)
          remaining = go slope intercept archRight (nextEvent : rest)
      in if eventLogN nextEvent < explorerTMin options - 1e-12 ||
            eventLogN event > explorerTMax options + 1e-12
          then remaining
          else build slope intercept archLeft archRight event nextEvent : remaining
    build slope intercept archLeft archRight event nextEvent = DualDynamics
          { dualEvent = eventN event
          , dualNextEvent = eventN nextEvent
          , dualLambda = eventWeight event
          , dualSlope = slope
          , dualIntercept = intercept
          , dualOptimizer = optimizer
          , dualArchDual = archDual
          , dualGlobalMargin = globalMargin
          , dualDeficit = deficit
          , dualArchDrift = drift
          , dualNextImpulse = eventWeight nextEvent
          , dualPredictedNextDeficit = deficit + drift - eventWeight nextEvent
          , dualActive = activeBlock
          , dualBlockMargin = blockMargin
          , dualBlockEqualsGlobal = activeBlock && abs (blockMargin - globalMargin) < 2e-8
          , dualEventAreaUpdate = eventAreaUpdate
          , dualEventValue = eventValue
          , dualSafetyEnergy = safetyEnergy
          , dualSafetySlack = blockMargin - safetyEnergy
          , dualCurvatureLower = curvatureLower
          , dualExactCurvature = exactCurvature
          , dualCurvatureSafetyEnergy = curvatureSafetyEnergy
          , dualExactCurvatureSafetyEnergy = exactCurvatureSafetyEnergy
          , dualCurvatureSafetySlack = blockMargin - curvatureSafetyEnergy
          , dualLogGap = logGap
          , dualConvexRemainder = convexRemainder
          , dualOptimizerDisplacement = displacement
          , dualKickDisplacement = kickDisplacement
          , dualKickArea = kickArea
          , dualPreKickDisplacement = preKickDisplacement
          , dualPostKickDisplacement = postKickDisplacement
          , dualBacklogBefore = max (-displacement) 0
          , dualBacklogAfter = max (-postKickDisplacement) 0
          , dualKickOverLambda = safeRatio kickDisplacement (eventWeight nextEvent)
          , dualKickOverLogGap = safeRatio kickDisplacement logGap
          , dualPrimeScaleKickBound = primeScaleKickBound
          , dualCurvatureScaledDeficit = descending / fromIntegral (eventN event) ** 0.25
          , dualImpulseOverDrift = safeRatio (eventWeight nextEvent) drift
          , dualImpulseOverLogGap = safeRatio (eventWeight nextEvent) logGap
          , dualDriftOverLogGap = safeRatio drift logGap
          , dualRootOptimizer = rootOptimizer
          , dualNextRootOptimizer = nextRootOptimizer
          , dualSqrtEvent = sqrtEvent
          , dualSqrtNextEvent = sqrtNextEvent
          , dualRootDisplacement = rootDisplacement
          , dualRootRatio = safeRatio rootOptimizer sqrtEvent
          , dualRootKick = rootKick
          , dualRootKickLower = eventWeight nextEvent / 2
          , dualRootKickUpper = 3 * eventWeight nextEvent / 5
          , dualSqrtGap = sqrtGap
          , dualRootKickOverGap = safeRatio rootKick sqrtGap
          , dualNormalizedRootImpulse = safeRatio rootKick sqrtNextEvent
          , dualCrudeGapCondition = fromIntegral (eventN nextEvent - eventN event) >=
              (6 / 5) * eventMangoldt nextEvent
          }
      where
        optimizerFor s
          | s <= archimedeanDerivative (log 2) = log 2
          | otherwise =
              let hi = findArchSlopeUpper s (max (log 2 + 1) (eventLogN nextEvent))
              in bisectArchSlope 80 s (log 2) hi
        archAt t
          | t >= left = archLeft + integrateArchDerivative left t
          | otherwise = archLeft - integrateArchDerivative t left
        dualFor s = let t = optimizerFor s in s * t - archAt t
        optimizer = optimizerFor slope
        archDual = dualFor slope
        globalMargin = intercept - archDual
        left = eventLogN event
        right = eventLogN nextEvent
        logGap = right - left
        deficit = archimedeanDerivative left - slope
        drift = archimedeanDerivative right - archimedeanDerivative left
        convexRemainder = archRight - archLeft - archimedeanDerivative left * logGap
        eventValue = archLeft - slope * left + intercept
        descending = max (-deficit) 0
        safetyEnergy = eventValue - descending * descending / 2
        curvatureLower = (5 / 6) * sqrt (fromIntegral (eventN event))
        exactCurvature = archimedeanSecondDerivative left
        curvatureSafetyEnergy = eventValue -
          descending * descending / (2 * curvatureLower)
        exactCurvatureSafetyEnergy = eventValue -
          descending * descending / (2 * exactCurvature)
        displacement = left - optimizer
        activeBlock = left < optimizer && optimizer < right
        blockOptimizer
          | optimizer < left = left
          | optimizer > right = right
          | otherwise = optimizer
        blockMargin = archAt blockOptimizer -
          slope * blockOptimizer + intercept
        nextSlope = slope + eventWeight nextEvent
        nextOptimizer = optimizerFor nextSlope
        kickDisplacement = nextOptimizer - optimizer
        nextIntercept = intercept + eventWeight nextEvent * right
        nextGlobalMargin = nextIntercept - dualFor nextSlope
        eventAreaUpdate = nextGlobalMargin - globalMargin
        kickArea = eventWeight nextEvent * (right - optimizer) -
          (nextGlobalMargin - globalMargin)
        preKickDisplacement = right - optimizer
        postKickDisplacement = right - nextOptimizer
        primeScaleKickBound = (6 / 5) * eventWeight nextEvent *
          exp (preKickDisplacement / 2) / sqrt (fromIntegral (eventN nextEvent))
        rootOptimizer = exp (optimizer / 2)
        nextRootOptimizer = exp (nextOptimizer / 2)
        sqrtEvent = sqrt (fromIntegral (eventN event))
        sqrtNextEvent = sqrt (fromIntegral (eventN nextEvent))
        rootDisplacement = sqrtEvent - rootOptimizer
        rootKick = nextRootOptimizer - rootOptimizer
        sqrtGap = sqrtNextEvent - sqrtEvent
        safeRatio numerator denominator
          | abs denominator < 1e-15 = 0 / 0
          | otherwise = numerator / denominator

findArchSlopeUpper :: Double -> Double -> Double
findArchSlopeUpper slope candidate
  | archimedeanDerivative candidate >= slope = candidate
  | otherwise = findArchSlopeUpper slope (candidate * 2)

buildCellMargins :: [PrimeEvent] -> [CellMinimum] -> [CellMargin]
buildCellMargins events = map build
  where
    build cell =
      let n = cellIndex cell
          active = takeWhile ((<= n) . eventN) events
          slope = sum (map eventWeight active)
          intercept = sum [eventWeight event * eventLogN event | event <- active]
          t = cellCandidateT cell
          arch = if t <= 0 then 0 else integrateArchDerivative 0 t
          dual = slope * t - arch
          at k = sum [eventMangoldt event | event <- events, eventN event == k]
          previous = [eventN event | event <- events, eventN event <= n]
          following = [eventN event | event <- events, eventN event > n]
          kind
            | abs (t - cellLeft cell) < 1e-7 = "left"
            | abs (t - cellRight cell) < 1e-7 = "right"
            | otherwise = "interior"
      in CellMargin
        { marginCell = n
        , marginSlope = slope
        , marginIntercept = intercept
        , marginDual = dual
        , marginValue = intercept - dual
        , marginCandidateT = t
        , marginMinimizerType = kind
        , marginMangoldtLeft = at n
        , marginMangoldtRight = at (n + 1)
        , marginSinceLastEvent = case reverse previous of
            event : _ -> Just (n - event)
            [] -> Nothing
        , marginToNextEvent = case following of
            event : _ -> Just (event - n)
            [] -> Nothing
        }

buildBlockMargins :: ExplorerOptions -> [PrimeEvent] -> [BlockMargin]
buildBlockMargins options events = mapMaybeCell build (zip events (drop 1 events))
  where
    build (leftEvent, rightEvent)
      | right < explorerTMin options - 1e-12 = Nothing
      | left > explorerTMax options + 1e-12 = Nothing
      | otherwise = Just BlockMargin
          { blockLeftEvent = eventN leftEvent
          , blockRightEvent = eventN rightEvent
          , blockGap = eventN rightEvent - eventN leftEvent
          , blockSlope = slope
          , blockIntercept = intercept
          , blockSlopeDeficitLeft = slope - archimedeanDerivative left
          , blockSlopeDeficitRight = slope - archimedeanDerivative right
          , blockCandidateT = optimizer
          , blockCandidateExpT = exp optimizer
          , blockMarginValue = value
          , blockMinimizerType = kind
          , blockWinningCell = max (eventN leftEvent) (floor (exp optimizer))
          }
      where
        left = eventLogN leftEvent
        right = eventLogN rightEvent
        active = takeWhile ((<= eventN leftEvent) . eventN) events
        slope = sum (map eventWeight active)
        intercept = sum [eventWeight event * eventLogN event | event <- active]
        dleft = archimedeanDerivative left - slope
        dright = archimedeanDerivative right - slope
        optimizer
          | dleft >= 0 = left
          | dright <= 0 = right
          | otherwise = bisectArchSlope 70 slope left right
        kind
          | optimizer == left = "left"
          | optimizer == right = "right"
          | otherwise = "interior"
        arch = integrateArchDerivative 0 optimizer
        value = arch - slope * optimizer + intercept

bisectArchSlope :: Int -> Double -> Double -> Double -> Double
bisectArchSlope 0 _ lo hi = (lo + hi) / 2
bisectArchSlope depth slope lo hi =
  let middle = (lo + hi) / 2
  in if archimedeanDerivative middle >= slope
      then bisectArchSlope (depth - 1) slope lo middle
      else bisectArchSlope (depth - 1) slope middle hi

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

-- | Exact second derivative of the closed archimedean expression for t>0.
-- The finite Mangoldt ramp is affine on every open prime cell, so this is
-- also the cell-interior second derivative of the unshifted Psi.
archimedeanSecondDerivative :: Double -> Double
archimedeanSecondDerivative t
  | t <= 0 = 0 / 0
  | otherwise =
      let ep = exp (t / 2)
          em = exp (-t / 2)
      in ep + em - 0.5 * ep / (1 + exp t) -
          0.5 * em / (1 - exp (-t))

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
          secondDerivative = archimedeanSecondDerivative t
      in (arch, [BasePoint t arch prime psi derivative secondDerivative])
    step (previousArch, previousPoint : rest) t =
      let arch = previousArch + integrateArchDerivative (baseT previousPoint) t
          prime = primeContribution events t
          psi = arch - prime
          derivative = if t <= 0 then 1 / 0
            else archimedeanDerivative t - primeSlope events t
          secondDerivative = archimedeanSecondDerivative t
      in (arch, BasePoint t arch prime psi derivative secondDerivative : previousPoint : rest)

suzukiPsiNumeric :: Double -> Double
suzukiPsiNumeric t
  | t == 0 = 0
  | t < 0 = suzukiPsiNumeric (-t)
  | exp t > 2000000 = 0 / 0
  | otherwise =
      let events = primeEvents (max 1 (floor (exp t)))
            (primesUpTo (max 2 (floor (exp t))))
      in integrateArchDerivative 0 t - primeContribution events t

eventsForT :: Double -> [PrimeEvent]
eventsForT t = primeEvents limit (primesUpTo (max 2 limit))
  where limit = max 1 (floor (exp (max 0 t)))

integrateAcrossPrimeCells :: [PrimeEvent] -> Double
  -> (Double -> Double) -> Double
integrateAcrossPrimeCells events t f = sum
  [ adaptiveSimpson 1e-10 16 f left right
  | (left, right) <- zip boundaries (drop 1 boundaries)
  , right > left
  ]
  where
    interiorEvents = [eventLogN event | event <- events,
      0 < eventLogN event, eventLogN event < t]
    boundaries = dedupeSorted (0 : sort interiorEvents ++ [t])

-- | Independent point evaluator for the exact Volterra definition.  This
-- is intentionally separate from the grid recurrence used by the branch
-- scanner, providing a normalization cross-check.
psiShiftedNumeric :: Double -> Double -> Double
psiShiftedNumeric omega t
  | t < 0 = psiShiftedNumeric omega (-t)
  | t == 0 = 0
  | exp t > 2000000 = 0 / 0
  | otherwise =
      let events = eventsForT t
          base u = integrateArchDerivative 0 u - primeContribution events u
          weighted u = exp (-omega * u) * base u
          j0 = integrateAcrossPrimeCells events t weighted
          j1 = integrateAcrossPrimeCells events t (\u -> u * weighted u)
      in weighted t + 2 * omega * j0 +
          omega * omega * (t * j0 - j1)

-- | Closed cell-interior first derivative of the shifted function.
dPsiDt :: Double -> Double -> Double
dPsiDt omega t
  | t <= 0 = 0 / 0
  | exp t > 2000000 = 0 / 0
  | otherwise =
      let events = eventsForT t
          base u = integrateArchDerivative 0 u - primeContribution events u
          baseDerivative = archimedeanDerivative t - primeSlope events t
          j0 = integrateAcrossPrimeCells events t
            (\u -> exp (-omega * u) * base u)
      in exp (-omega * t) * (baseDerivative + omega * base t) +
          omega * omega * j0

-- | Closed cell-interior second derivative.  All Volterra terms cancel:
-- `d²/dt² (T_omega Psi) = exp(-omega*t) * Psi''`.
d2PsiDt2 :: Double -> Double -> Double
d2PsiDt2 omega t = exp (-omega * t) * archimedeanSecondDerivative t

exploreOmega :: ExplorerOptions -> [Int] -> [PrimeEvent] -> [BasePoint]
  -> Double -> (OmegaSummary, [CellMinimum], [CandidateCertificate], [CriticalPoint])
exploreOmega options primes events base omega =
  let shifted = buildShiftPoints events base omega
      relevant = filter (inRequestedRange options . shiftT) shifted
      cells = cellMinima options primes events omega relevant
      globalCell = minimumBy (comparing cellCandidateValue) cells
      certificates = map (affineCandidateCertificate options relevant) cells
      criticals = enumerateCriticalPoints omega relevant
      summary = OmegaSummary omega (cellCandidateValue globalCell)
        (cellCandidateT globalCell) (cellIndex globalCell)
        (maximum (0 : map crossError shifted))
        (derivativeCheckError shifted)
  in (summary, cells, certificates, criticals)
  where crossError point = abs (shiftValue point - shiftCrossValue point)

derivativeCheckError :: [ShiftPoint] -> Double
derivativeCheckError points = maximum (0 : map check triples)
  where
    triples = zip3 points (drop 1 points) (drop 2 points)
    check (left, middle, right)
      | not (all isFinite [shiftDerivative middle, shiftValue left,
          shiftValue right]) = 0
      | shiftT middle < 0.05 = 0
      | any (nearPrimeThreshold (2 * abs (shiftT right - shiftT left)))
          [shiftT left, shiftT middle, shiftT right] = 0
      | cellForT ((shiftT left + shiftT middle) / 2) /=
          cellForT ((shiftT middle + shiftT right) / 2) = 0
      | shiftT right == shiftT left = 0
      | otherwise = abs (shiftDerivative middle -
          (shiftValue right - shiftValue left) /
            (shiftT right - shiftT left))
    nearPrimeThreshold radius t =
      let nearest :: Int
          nearest = max 1 (round (exp t))
      in abs (t - log (fromIntegral nearest)) <= radius

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
        [ShiftPoint t value (basePsiDerivative point)
          (basePsiSecondDerivative point) (0 / 0) crossValue])
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
          secondDerivative = exp (-omega * t1) * basePsiSecondDerivative point
          mixedDerivative = exp (-omega * t1) *
            (basePsi point - t1 * basePsiDerivative point -
              t1 * omega * basePsi point) +
              2 * omega * nextJ0 - omega * omega * nextJ1
          archValue = archG1 + 2 * omega * nextArchJ0 +
            omega * omega * (t1 * nextArchJ0 - nextArchJ1)
          crossValue = archValue - shiftedPrimeContributionNumeric events omega t1
      in (nextJ0, nextJ1, nextArchJ0, nextArchJ1, t1, Just point,
        ShiftPoint t1 value derivative secondDerivative mixedDerivative crossValue : acc)
    step state _ = state

cellMinima :: ExplorerOptions -> [Int] -> [PrimeEvent] -> Double
  -> [ShiftPoint] -> [CellMinimum]
cellMinima options primes events omega points =
  let rangeFirst = max 1 (floor (exp (explorerTMin options)))
      rangeLast = max rangeFirst (floor (exp (explorerTMax options)))
      firstCell = max rangeFirst (maybe rangeFirst id (explorerCellMin options))
      lastCell = min rangeLast (maybe rangeLast id (explorerCellMax options))
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
      endpoints = filter ((> 1e-10) . shiftT)
        (case inside of
          [] -> []
          [_] -> inside
          firstPoint : rest -> [firstPoint, lastPoint rest])
      candidates = endpoints ++ uniqueCellDerivativeRootCandidates n inside
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
        , cellSecondDerivative = shiftSecondDerivative best
        , cellDistanceAboveBest = 0
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
      | shiftT right <= shiftT left = Nothing
      | isLogInteger (shiftT right) = Nothing
      | otherwise = Just (refineDerivativeRoot left right)
      where
        dl = shiftDerivative left
        dr = shiftDerivative right

-- | For cells n >= 2, the Lean-checked strict-convexity theorem implies
-- that the derivative is strictly increasing and has at most one zero.
-- Consequently its signs at the first and last interior grid points decide
-- whether an interior critical point exists.  Cell 1 retains the generic
-- scanner because the uniform curvature theorem starts at log 2.
uniqueCellDerivativeRootCandidates :: Int -> [ShiftPoint] -> [ShiftPoint]
uniqueCellDerivativeRootCandidates n points
  | n < 2 = derivativeRootCandidates points
  | otherwise =
      case interior of
        left : rest
          | not (null rest)
          , let right = last rest
          , isFinite (shiftDerivative left)
          , isFinite (shiftDerivative right)
          , shiftDerivative left <= 0
          , 0 <= shiftDerivative right
          , shiftDerivative left /= shiftDerivative right ->
              [refineDerivativeRoot left right]
        _ -> []
  where
    leftThreshold = log (fromIntegral n)
    rightThreshold = log (fromIntegral (n + 1))
    interior = filter (\point ->
      leftThreshold + 1e-12 < shiftT point &&
      shiftT point < rightThreshold - 1e-12) points

refineDerivativeRoot :: ShiftPoint -> ShiftPoint -> ShiftPoint
refineDerivativeRoot left right =
  let (lo, hi) = bisect 60 (shiftT left) (shiftT right)
      t = (lo + hi) / 2
      ratio = (t - shiftT left) / (shiftT right - shiftT left)
      value = hermiteValue left right t
      derivative = hermiteDerivative left right t
      secondDerivative = lerp ratio
        (shiftSecondDerivative left) (shiftSecondDerivative right)
      mixedDerivative = lerp ratio
        (shiftMixedDerivative left) (shiftMixedDerivative right)
      crossValue = lerp ratio (shiftCrossValue left) (shiftCrossValue right)
  in ShiftPoint t value derivative secondDerivative mixedDerivative crossValue
  where
    bisect :: Int -> Double -> Double -> (Double, Double)
    bisect 0 lo hi = (lo, hi)
    bisect depth lo hi =
      let mid = (lo + hi) / 2
          dlo = hermiteDerivative left right lo
          dm = hermiteDerivative left right mid
      in if not (isFinite dm) then (lo, hi)
         else if dlo * dm <= 0
           then bisect (depth - 1) lo mid
           else bisect (depth - 1) mid hi

hermiteValue :: ShiftPoint -> ShiftPoint -> Double -> Double
hermiteValue left right t =
  let width = shiftT right - shiftT left
      s = (t - shiftT left) / width
      s2 = s * s
      s3 = s2 * s
      h00 = 2 * s3 - 3 * s2 + 1
      h10 = s3 - 2 * s2 + s
      h01 = -2 * s3 + 3 * s2
      h11 = s3 - s2
  in h00 * shiftValue left + h10 * width * shiftDerivative left +
      h01 * shiftValue right + h11 * width * shiftDerivative right

hermiteDerivative :: ShiftPoint -> ShiftPoint -> Double -> Double
hermiteDerivative left right t =
  let width = shiftT right - shiftT left
      s = (t - shiftT left) / width
      s2 = s * s
  in ((6 * s2 - 6 * s) * shiftValue left +
      (3 * s2 - 4 * s + 1) * width * shiftDerivative left +
      (-6 * s2 + 6 * s) * shiftValue right +
      (3 * s2 - 2 * s) * width * shiftDerivative right) / width

lerp :: Double -> Double -> Double -> Double
lerp ratio left right = left + ratio * (right - left)

isLogInteger :: Double -> Bool
isLogInteger t =
  let nearest :: Int
      nearest = max 1 (round (exp t))
  in abs (t - log (fromIntegral nearest)) < 1e-11

enumerateCriticalPoints :: Double -> [ShiftPoint] -> [CriticalPoint]
enumerateCriticalPoints omega points =
  [ CriticalPoint
      { criticalOmega = omega
      , criticalCell = cellForT (shiftT root)
      , criticalT = shiftT root
      , criticalValue = shiftValue root
      , criticalDerivative = shiftDerivative root
      , criticalSecondDerivative = shiftSecondDerivative root
      , criticalMixedDerivative = shiftMixedDerivative root
      , criticalClassification = classifyRoot left right root
      }
  | cell <- [minimumCell .. maximumCell]
  , let leftThreshold = log (fromIntegral cell)
  , let rightThreshold = log (fromIntegral (cell + 1))
  , let inCell = filter (\point ->
          leftThreshold - 1e-12 <= shiftT point &&
          shiftT point <= rightThreshold + 1e-12) points
  , root <- uniqueCellDerivativeRootCandidates cell inCell
  , let neighbors = nearestBracket root inCell
  , (left, right) <- maybe [] (: []) neighbors
  ]
  where
    cells = map (cellForT . shiftT) points
    minimumCell = if null cells then 1 else minimum cells
    maximumCell = if null cells then 0 else maximum cells
    nearestBracket root candidates =
      case break ((shiftT root <) . shiftT) candidates of
        (before, right : _) | not (null before) -> Just (last before, right)
        _ -> Nothing

classifyRoot :: ShiftPoint -> ShiftPoint -> ShiftPoint -> CriticalClassification
classifyRoot left right root
  | shiftDerivative left < 0 && shiftDerivative right > 0 = LocalMinimum
  | shiftDerivative left > 0 && shiftDerivative right < 0 = LocalMaximum
  | shiftSecondDerivative root > 1e-7 = LocalMinimum
  | shiftSecondDerivative root < -1e-7 = LocalMaximum
  | otherwise = CriticalUncertain

trackMinimumBranches :: [CriticalPoint] -> [BranchPoint]
trackMinimumBranches criticals = accumulated
  where
    minima = filter ((== LocalMinimum) . criticalClassification) criticals
    omegas = dedupeSorted (sort (map criticalOmega minima))
    grouped = [(omega, sortOn (\point -> (criticalCell point, criticalT point))
      [point | point <- minima, abs (criticalOmega point - omega) < 1e-12])
      | omega <- omegas]
    (_, _, accumulated) = foldl' continue
      (([] :: [(Int, Int)]), [], []) grouped
    continue (counters, previous, completed) (omega, points) =
      let cells = sort (unique (map criticalCell points))
          (nextCounters, current) = foldl'
            (continueCell omega points previous) (counters, []) cells
      in (nextCounters, current, completed ++ current)
    continueCell omega points previous (counters, current) cell =
      let cellPoints = filter ((== cell) . criticalCell) points
          oldBranches = filter ((== cell) . branchCell) previous
          (_, matches) = foldl'
            (matchCritical omega cell) (oldBranches, []) cellPoints
          (nextCounters, newPoints) = foldl'
            (materialize cell omega) (counters, []) (reverse matches)
      in (nextCounters, current ++ newPoints)
    matchCritical omega cell (available, matches) point =
      case closestPredicted omega point available of
        Just old | predictedDistance omega point old <= branchMatchRadius cell ->
          (filter ((/= branchId old) . branchId) available,
            (point, Just old) : matches)
        _ -> (available, (point, Nothing) : matches)
    materialize cell omega (counters, points) (point, old) =
      let (identifier, nextCounters) = case old of
            Just previous -> (branchId previous, counters)
            Nothing ->
              let ordinal = maybe 1 id (lookup cell counters)
              in ("cell-" ++ show cell ++ "-" ++ show ordinal,
                  setCounter cell (ordinal + 1) counters)
          branch = BranchPoint
            { branchId = identifier
            , branchCell = cell
            , branchOmega = omega
            , branchT = criticalT point
            , branchMinimum = criticalValue point
            , branchCurvature = criticalSecondDerivative point
            , branchDtDomega = safeNegRatio
                (criticalMixedDerivative point) (criticalSecondDerivative point)
            }
      in (nextCounters, points ++ [branch])
    closestPredicted _ _ [] = Nothing
    closestPredicted omega point branches = Just
      (minimumBy (comparing (predictedDistance omega point)) branches)
    predictedDistance omega point previous = abs (criticalT point - predicted)
      where
        slope = branchDtDomega previous
        predicted
          | isFinite slope = branchT previous +
              slope * (omega - branchOmega previous)
          | otherwise = branchT previous
    branchMatchRadius cell = max 1e-5
      (0.45 * (log (fromIntegral (cell + 1)) - log (fromIntegral cell)))
    setCounter cell next counters =
      (cell, next) : filter ((/= cell) . fst) counters

safeNegRatio :: Double -> Double -> Double
safeNegRatio numerator denominator
  | abs denominator < 1e-12 = 0 / 0
  | otherwise = -numerator / denominator

unique :: Eq a => [a] -> [a]
unique = nubBy (==)

refineEnvelopeCrossings :: ExplorerOptions -> [Int] -> [PrimeEvent]
  -> [BasePoint] -> [OmegaSummary] -> [EnvelopeCrossing]
refineEnvelopeCrossings options primes events base summaries = mapMaybeCell crossing
  (zip summaries (drop 1 summaries))
  where
    crossing (leftSummary, rightSummary)
      | summaryCell leftSummary == summaryCell rightSummary = Nothing
      | otherwise = do
          let cellA = summaryCell leftSummary
              cellB = summaryCell rightSummary
          (lo, hi) <- orderBracket (summaryOmega leftSummary)
            (summaryOmega rightSummary) cellA cellB
          let omega = bisectCrossing 35 lo hi cellA cellB
          valueA <- cellAt omega cellA
          valueB <- cellAt omega cellB
          pure EnvelopeCrossing
            { crossingOmega = omega
            , crossingCellA = cellA
            , crossingCellB = cellB
            , crossingTA = cellCandidateT valueA
            , crossingTB = cellCandidateT valueB
            , crossingCommonMinimum =
                (cellCandidateValue valueA + cellCandidateValue valueB) / 2
            }
    cellAt omega cell =
      let shifted = buildShiftPoints events base omega
          relevant = filter (inRequestedRange options . shiftT) shifted
      in minimumOnCell options primes events omega relevant cell
    delta omega cellA cellB = do
      valueA <- cellAt omega cellA
      valueB <- cellAt omega cellB
      pure (cellCandidateValue valueA - cellCandidateValue valueB)
    orderBracket first second cellA cellB = do
      let lo = min first second
          hi = max first second
      dlo <- delta lo cellA cellB
      dhi <- delta hi cellA cellB
      if dlo * dhi <= 0 then pure (lo, hi) else Nothing
    bisectCrossing :: Int -> Double -> Double -> Int -> Int -> Double
    bisectCrossing 0 lo hi _ _ = (lo + hi) / 2
    bisectCrossing depth lo hi cellA cellB =
      let middle = (lo + hi) / 2
          dlo = maybe 0 id (delta lo cellA cellB)
          dmid = maybe 0 id (delta middle cellA cellB)
      in if dlo * dmid <= 0
          then bisectCrossing (depth - 1) lo middle cellA cellB
          else bisectCrossing (depth - 1) middle hi cellA cellB

detectBifurcations :: [CriticalPoint] -> [BifurcationEvent]
detectBifurcations criticals = concatMap detect criticals
  where
    detect point = foldr add []
      [ (abs (criticalSecondDerivative point) < 1e-4,
          "candidate_fold")
      , (distanceToBoundary point < 1e-4,
          "prime_cell_boundary_collision")
      ]
      where
        add (flag, kind) rest
          | flag = BifurcationEvent
              { bifurcationOmega = criticalOmega point
              , bifurcationCell = criticalCell point
              , bifurcationT = criticalT point
              , bifurcationKind = kind
              , bifurcationCurvature = criticalSecondDerivative point
              } : rest
          | otherwise = rest
    distanceToBoundary point = min
      (abs (criticalT point - log (fromIntegral (criticalCell point))))
      (abs (criticalT point - log (fromIntegral (criticalCell point + 1))))

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

lastPoint :: [a] -> a
lastPoint [x] = x
lastPoint (_ : xs) = lastPoint xs
lastPoint [] = error "lastPoint: internal nonempty-list invariant violated"

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
      strongSample = rationalNearest (cellCandidateT minimumValue)
      strongValueLower = rationalDown (cellCandidateValue minimumValue - safety)
      strongDerivAbsUpper = rationalUp
        (abs (cellDerivative minimumValue) + safety)
      strongCurvatureLower = rationalDown
        (max 0 (cellSecondDerivative minimumValue - safety))
      strongValue = rationalValue strongValueLower
      strongDeriv = rationalValue strongDerivAbsUpper
      strongCurvature = rationalValue strongCurvatureLower
      strongMargin
        | strongCurvature > 0 =
            strongValue - strongDeriv * strongDeriv / (2 * strongCurvature)
        | otherwise = -1e300
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
    , certificateStrongSample = strongSample
    , certificateStrongValueLower = strongValueLower
    , certificateStrongDerivAbsUpper = strongDerivAbsUpper
    , certificateStrongCurvatureLower = strongCurvatureLower
    , certificateStrongMargin = strongMargin
    , certificateClaimedMinimum = lineMinimum
    , certificateDiscoveryPrecision = precision
    , certificateStatus = status
    }

first3 :: (a, b, c) -> a
first3 (x, _, _) = x

rationalDown :: Double -> (Integer, Integer)
rationalDown value = (floor (value * fromIntegral denominator), denominator)
  where denominator = 1000000

rationalUp :: Double -> (Integer, Integer)
rationalUp value = (ceiling (value * fromIntegral denominator), denominator)
  where denominator = 1000000

rationalNearest :: Double -> (Integer, Integer)
rationalNearest value = (round (value * fromIntegral denominator), denominator)
  where denominator = 1000000

rationalValue :: (Integer, Integer) -> Double
rationalValue (numerator, denominator) =
  fromIntegral numerator / fromIntegral denominator

safeDivide :: Double -> Double -> Double
safeDivide numerator denominator
  | denominator == 0 = 0 / 0
  | otherwise = numerator / denominator

linearFit :: [(Double, Double)] -> Maybe (Double, Double, Double)
linearFit pairs
  | length pairs < 2 || abs denominator < 1e-15 = Nothing
  | otherwise = Just (intercept, slope, rmse)
  where
    count = fromIntegral (length pairs)
    meanX = sum (map fst pairs) / count
    meanY = sum (map snd pairs) / count
    denominator = sum [(x - meanX) * (x - meanX) | (x, _) <- pairs]
    slope = sum [(x - meanX) * (y - meanY) | (x, y) <- pairs] / denominator
    intercept = meanY - slope * meanX
    rmse = sqrt (sum
      [(y - (intercept + slope * x)) ^ (2 :: Int) | (x, y) <- pairs] / count)

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
  , "omega       min Psi_omega       t*          cell      value-xcheck   deriv-xcheck"
  , "--------------------------------------------------------------------------------"
  ] ++ map renderSummary (reportSummaries report) ++
  [ ""
  , "Most dangerous prime cells (candidate minima):"
  , "omega       cell       left          right         min Psi        t*"
  , "------------------------------------------------------------------------"
  ] ++ map renderCell (take 16 (sortOn cellCandidateValue (reportCellMinima report))) ++
  modeSpecific ++
  [ ""
  , "Candidate certificate statuses are sampled numerical results only."
  , "Lean-certified cells: unshifted cell 2, [log 2, log 3]."
  , "Separate local coverage: [0,q] for some certified rational q>0; the gap to log 2 is open."
  , "Tail status: unknown."
  ]
  where
    renderSummary summary = intercalate "  "
      [pad 10 (fmt 6 (summaryOmega summary))
      , pad 19 (fmt 10 (summaryMinimum summary))
      , pad 11 (fmt 6 (summaryArgmin summary))
      , pad 9 (show (summaryCell summary))
      , pad 14 (fmt 4 (summaryCrossCheckError summary))
      , fmt 4 (summaryDerivativeCheckError summary)]
    renderCell cell = intercalate "  "
      [pad 10 (fmt 6 (cellOmega cell))
      , pad 10 (show (cellIndex cell))
      , pad 13 (fmt 7 (cellLeft cell))
      , pad 13 (fmt 7 (cellRight cell))
      , pad 14 (fmt 8 (cellCandidateValue cell))
      , fmt 7 (cellCandidateT cell)]
    modeSpecific = case explorerMode (reportOptions report) of
      BranchesMode -> branchSection ++ crossingSection ++ scalingSection ++ bifurcationSection
      CrossingsMode -> crossingSection
      CellMode -> criticalSection
      ClusterMode -> clusterSection ++ criticalSection
      CertificateStatusMode -> certificateStatusSection
      MarginsMode -> marginSection
      BlocksMode -> blockSection
      DualMode -> dualSection
      RootsMode -> rootSection
      BusyMode -> busySection
      ScanMode -> []
    marginSection =
      [ ""
      , "Mangoldt-state cell margins (NumericalEvidence):"
      , "cell   S_n          C_n          D_n(S_n)     margin       t*          type      since  next   Lambda(n)  Lambda(n+1)"
      , "--------------------------------------------------------------------------------------------------------------------"
      ] ++ map renderMargin
        (take 20 (sortOn marginValue (reportMargins report)))
    blockSection =
      [ ""
      , "Mangoldt event blocks (NumericalEvidence):"
      , "q      r      gap    S_q          C_q          deficit(q)   deficit(r)   margin       t*          exp(t*)     type      cell"
      , "------------------------------------------------------------------------------------------------------------------------------"
      ] ++ map renderBlock
        (take 30 (sortOn blockMarginValue (reportBlockMargins report)))
    dualSection =
      [ ""
      , "Kicked convex-flow event dynamics (NumericalEvidence):"
      , "Rows are ranked by curvature safety energy; finite scans do not establish a global invariant."
      , "q      r      B_q          d_q          Esharp       block M      slack        m_q          x_q          h            dT/h        active"
      , "--------------------------------------------------------------------------------------------------------------------------------------------"
      ] ++ map renderDual dualRowsForDisplay ++ lyapunovSection
    rootSection =
      [ ""
      , "Square-root optimizer dynamics (NumericalEvidence):"
      , "Rows are ranked by root kick / square-root gap; finite scans do not establish an invariant."
      , "q       r       u*          sqrt(q)     sqrt(r)     rho         x_root      du          [lambda/2,3lambda/5]      sqrt-gap    du/gap     active"
      , "----------------------------------------------------------------------------------------------------------------------------------------------------------"
      ] ++ map renderRoot rootRowsForDisplay ++ rootSummarySection ++
        rootPotentialSection
    busySection =
      [ ""
      , "Root-discrepancy busy periods (NumericalEvidence):"
      , "Each row is one completed maximal negative excursion; finite scans do not establish RH."
      , "start    recover<  events  root width    t width       D_start       D_min         loss          Psi_start     Psi_min       loss/reserve  arrivals/service"
      , "----------------------------------------------------------------------------------------------------------------------------------------------------------"
      ] ++ map renderBusy busyRowsForDisplay ++ busySummarySection
    criticalSection =
      [ ""
      , "Detected interior critical points:"
      , "omega      cell    t*           Psi          dPsi         d2Psi        class"
      , "----------------------------------------------------------------------------"
      ] ++ map renderCritical criticalPointsForMode
    branchSection =
      [ ""
      , "Continued local-minimum branches (cell/order IDs):"
      , "branch          omega      cell    t*          minimum       curvature     dt/domega"
      , "------------------------------------------------------------------------------------"
      ] ++ map renderBranch
        [point | point <- reportBranches report,
          branchCell point `elem` envelopeCells]
    crossingSection =
      [ ""
      , "Candidate lower-envelope crossings:"
      , "omega*       cell A -> cell B    t_A         t_B         common minimum"
      , "------------------------------------------------------------------------"
      ] ++ map renderCrossing (reportCrossings report)
    scalingSection =
      [ ""
      , "Low-complexity envelope scaling fits (discovery diagnostics):"
      ] ++ renderFits
    bifurcationSection =
      [ ""
      , "Candidate folds / prime-boundary collisions:"
      ] ++ map renderBifurcation (reportBifurcations report)
    clusterSection =
      [ ""
      , "Requested cell cluster ranked by candidate minimum:"
      , "rank   cell    t*           Psi             curvature       above best"
      , "------------------------------------------------------------------------"
      ] ++ zipWith renderCluster [1 :: Int ..]
        (take 20 (sortOn cellCandidateValue (reportCellMinima report)))
    certificateStatusSection =
      [ ""
      , "Certificate coverage:"
      , "  [0,q]            LeanChecked for some explicit existential rational q>0"
      , "  [q,log 2]        unknown"
      , "  [log 2,log 3]    LeanChecked (unshifted prime cell 2)"
      , "  [log 3,infty)    unknown (SuzukiPsiTailCertificate remains open)"
      ]
    envelopeCells = unique
      (map summaryCell (reportSummaries report) ++
        concat [[crossingCellA crossing, crossingCellB crossing]
          | crossing <- reportCrossings report])
    criticalPointsForMode =
      [point | point <- reportCriticalPoints report,
        maybe True (<= criticalCell point) (explorerCellMin (reportOptions report)),
        maybe True (criticalCell point <=) (explorerCellMax (reportOptions report))]
    envelopeRows =
      [(summaryOmega summary, summaryArgmin summary,
        log (fromIntegral (summaryCell summary)))
      | summary <- reportSummaries report, summaryOmega summary > 0]
    renderFits =
      renderFit "log(cell) ~ a + b/omega"
        [(1 / omega, logCell) | (omega, _, logCell) <- envelopeRows] ++
      renderFit "log(cell) ~ a + b*log(1/omega)"
        [(log (1 / omega), logCell) | (omega, _, logCell) <- envelopeRows] ++
      renderFit "t* ~ a + b*log(cell)"
        [(logCell, t) | (_, t, logCell) <- envelopeRows]
    renderFit label pairs = case linearFit pairs of
      Nothing -> ["  " ++ label ++ ": insufficient variation"]
      Just (intercept, slope, residual) ->
        ["  " ++ label ++ ": a=" ++ fmt 6 intercept ++
          " b=" ++ fmt 6 slope ++ " rmse=" ++ fmt 6 residual]
    renderCritical point = intercalate "  "
      [ pad 10 (fmt 6 (criticalOmega point))
      , pad 7 (show (criticalCell point))
      , pad 12 (fmt 8 (criticalT point))
      , pad 12 (fmt 8 (criticalValue point))
      , pad 12 (fmt 4 (criticalDerivative point))
      , pad 12 (fmt 6 (criticalSecondDerivative point))
      , classificationText (criticalClassification point)]
    renderBranch point = intercalate "  "
      [ pad 15 (branchId point)
      , pad 10 (fmt 6 (branchOmega point))
      , pad 7 (show (branchCell point))
      , pad 11 (fmt 7 (branchT point))
      , pad 13 (fmt 8 (branchMinimum point))
      , pad 13 (fmt 7 (branchCurvature point))
      , fmt 7 (branchDtDomega point)]
    renderCrossing crossing = intercalate "  "
      [ pad 12 (fmt 8 (crossingOmega crossing))
      , pad 18 (show (crossingCellA crossing) ++ " -> " ++
          show (crossingCellB crossing))
      , pad 11 (fmt 7 (crossingTA crossing))
      , pad 11 (fmt 7 (crossingTB crossing))
      , fmt 9 (crossingCommonMinimum crossing)]
    renderBifurcation event = intercalate "  "
      [fmt 7 (bifurcationOmega event), show (bifurcationCell event),
       fmt 8 (bifurcationT event), bifurcationKind event,
       "curvature=" ++ fmt 7 (bifurcationCurvature event)]
    renderCluster rank cell = intercalate "  "
      [pad 6 (show rank), pad 7 (show (cellIndex cell)),
       pad 12 (fmt 8 (cellCandidateT cell)),
       pad 15 (fmt 10 (cellCandidateValue cell)),
       pad 15 (fmt 8 (cellSecondDerivative cell)),
       fmt 10 (cellDistanceAboveBest cell)]
    renderMargin row = intercalate "  "
      [ pad 6 (show (marginCell row))
      , pad 12 (fmt 7 (marginSlope row))
      , pad 12 (fmt 7 (marginIntercept row))
      , pad 12 (fmt 7 (marginDual row))
      , pad 12 (fmt 8 (marginValue row))
      , pad 11 (fmt 7 (marginCandidateT row))
      , pad 9 (marginMinimizerType row)
      , pad 6 (maybe "-" show (marginSinceLastEvent row))
      , pad 6 (maybe "-" show (marginToNextEvent row))
      , pad 10 (fmt 5 (marginMangoldtLeft row))
      , fmt 5 (marginMangoldtRight row)]
    renderBlock row = intercalate "  "
      [ pad 6 (show (blockLeftEvent row))
      , pad 6 (show (blockRightEvent row))
      , pad 6 (show (blockGap row))
      , pad 12 (fmt 7 (blockSlope row))
      , pad 12 (fmt 7 (blockIntercept row))
      , pad 12 (fmt 7 (blockSlopeDeficitLeft row))
      , pad 12 (fmt 7 (blockSlopeDeficitRight row))
      , pad 12 (fmt 8 (blockMarginValue row))
      , pad 11 (fmt 7 (blockCandidateT row))
      , pad 11 (fmt 4 (blockCandidateExpT row))
      , pad 9 (blockMinimizerType row)
      , show (blockWinningCell row)]
    renderDual row = intercalate "  "
      [ pad 6 (show (dualEvent row))
      , pad 6 (show (dualNextEvent row))
      , pad 12 (fmt 8 (dualEventValue row))
      , pad 12 (fmt 8 (dualDeficit row))
      , pad 12 (fmt 8 (dualCurvatureSafetyEnergy row))
      , pad 12 (fmt 8 (dualBlockMargin row))
      , pad 12 (fmt 8 (dualCurvatureSafetySlack row))
      , pad 12 (fmt 6 (dualCurvatureLower row))
      , pad 12 (fmt 8 (dualOptimizerDisplacement row))
      , pad 12 (fmt 8 (dualLogGap row))
      , pad 12 (fmt 7 (dualKickOverLogGap row))
      , boolText (dualActive row)]
    renderRoot row = intercalate "  "
      [ pad 7 (show (dualEvent row))
      , pad 7 (show (dualNextEvent row))
      , pad 11 (fmt 6 (dualRootOptimizer row))
      , pad 11 (fmt 6 (dualSqrtEvent row))
      , pad 11 (fmt 6 (dualSqrtNextEvent row))
      , pad 11 (fmt 8 (dualRootRatio row))
      , pad 12 (fmt 7 (dualRootDisplacement row))
      , pad 11 (fmt 8 (dualRootKick row))
      , pad 24 ("[" ++ fmt 7 (dualRootKickLower row) ++ "," ++
          fmt 7 (dualRootKickUpper row) ++ "]")
      , pad 11 (fmt 8 (dualSqrtGap row))
      , pad 11 (fmt 7 (dualRootKickOverGap row))
      , boolText (dualActive row)]
    renderBusy period = intercalate "  "
      [ pad 8 (show (busyStartEvent period))
      , pad 9 (show (busyRecoveryBeforeEvent period))
      , pad 7 (show (busyEventCount period))
      , pad 13 (fmt 8 (busyRootWidth period))
      , pad 13 (fmt 8 (busyTWidth period))
      , pad 13 (fmt 8 (busyStartingDiscrepancy period))
      , pad 13 (fmt 8 (busyMostNegativeDiscrepancy period))
      , pad 13 (fmt 9 (busyWeightedLoss period))
      , pad 13 (fmt 9 (busyPsiStart period))
      , pad 13 (fmt 9 (busyMinimumPsi period))
      , pad 13 (fmt 7 (busyLossOverReserve period))
      , fmt 7 (busyArrivalOverService period)]
    dualRowsForDisplay = take 30 (sortOn dualCurvatureSafetyEnergy
      (reportDualDynamics report))
    rootRowsForDisplay = take 40 (reverse (sortOn dualRootKickOverGap
      (reportDualDynamics report)))
    busyRowsForDisplay = take 40 (reverse (sortOn busyLossOverReserve
      (reportBusyPeriods report)))
    busySummarySection =
      let periods = reportBusyPeriods report
          maxEvents = if null periods then Nothing else Just
            (maximumBy (comparing busyEventCount) periods)
          maxWidth = if null periods then Nothing else Just
            (maximumBy (comparing busyRootWidth) periods)
          maxFraction = if null periods then Nothing else Just
            (maximumBy (comparing busyLossOverReserve) periods)
          containing199 = [period | period <- periods,
            busyStartEvent period <= 199,
            199 < busyRecoveryBeforeEvent period]
          showAt field period = show (field period) ++ " at start q=" ++
            show (busyStartEvent period)
      in [ ""
         , "Busy-period scan summary:"
         , "  completed periods: " ++ show (length periods)
         , "  maximum event count: " ++ maybe "n/a" (showAt busyEventCount) maxEvents
         , "  maximum root width: " ++ maybe "n/a"
             (\period -> fmt 10 (busyRootWidth period) ++ " at start q=" ++
               show (busyStartEvent period)) maxWidth
         , "  largest reserve fraction consumed: " ++ maybe "n/a"
             (\period -> fmt 10 (busyLossOverReserve period) ++ " at start q=" ++
               show (busyStartEvent period)) maxFraction
         , "  period containing event 199: " ++ case containing199 of
             period : _ -> show (busyStartEvent period) ++ " -> recovery before " ++
               show (busyRecoveryBeforeEvent period) ++ " (" ++
               show (busyEventCount period) ++ " event states)"
             [] -> "none in completed scan"
         ]
    rootSummarySection =
      let rows = reportDualDynamics report
          maxRho = if null rows then Nothing else Just (maximumBy
            (comparing dualRootRatio) rows)
          maxOvershoot = if null rows then Nothing else Just (minimumBy
            (comparing dualRootDisplacement) rows)
          maxKickGap = if null rows then Nothing else Just (maximumBy
            (comparing dualRootKickOverGap) rows)
          crudeFailures = length (filter (not . dualCrudeGapCondition) rows)
          showAt field row = fmt 10 (field row) ++ " at q=" ++ show (dualEvent row)
      in [ ""
         , "Root-coordinate scan summary:"
         , "  maximum rho: " ++ maybe "n/a" (showAt dualRootRatio) maxRho
         , "  largest optimizer overshoot: " ++ maybe "n/a"
             (\row -> fmt 10 (max (-dualRootDisplacement row) 0) ++
               " at q=" ++ show (dualEvent row)) maxOvershoot
         , "  maximum rootKick/sqrtGap: " ++ maybe "n/a"
             (showAt dualRootKickOverGap) maxKickGap
         , "  failures of gap >= (6/5)*Lambda(next): " ++ show crudeFailures ++
             " / " ++ show (length rows)
         ]
    rootPotentialSection =
      [ ""
      , "Root-barrier candidates (NumericalEvidence):"
      , "potential                              global min     min event change   decreasing events"
      , "-----------------------------------------------------------------------------------"
      ] ++ map renderRootPotential rootPotentialSpecs
    rootPotentialSpecs =
      [("M + (5/3)*overshoot^2/sqrt(q)", rootBarrier (5 / 3))
      ,("M + 2*overshoot^2/sqrt(q)", rootBarrier 2)
      ,("curvature safety energy", dualCurvatureSafetyEnergy)]
    rootBarrier coefficient row =
      let overshoot = max (-dualRootDisplacement row) 0
      in dualGlobalMargin row + coefficient * overshoot ^ (2 :: Int) /
        dualSqrtEvent row
    renderRootPotential (label, potential) =
      let values = map potential (reportDualDynamics report)
          changes = zipWith (-) (drop 1 values) values
          minValue = if null values then 0 / 0 else minimum values
          minChange = if null changes then 0 / 0 else minimum changes
          decreases = length (filter (< (-1e-12)) changes)
      in intercalate "  " [pad 38 label, pad 14 (fmt 9 minValue),
          pad 18 (fmt 9 minChange), show decreases]
    lyapunovSection =
      [ ""
      , "Simple Lyapunov-potential scan (NumericalEvidence):"
      , "potential                       global min     min event change   decreasing events"
      , "--------------------------------------------------------------------------------"
      ] ++ map renderPotential potentialSpecs
    potentialSpecs =
      [("M + 1/4*x^2", \row -> dualGlobalMargin row + 0.25 * dualOptimizerDisplacement row ^ (2 :: Int))
      ,("M + 1/2*x^2", \row -> dualGlobalMargin row + 0.5 * dualOptimizerDisplacement row ^ (2 :: Int))
      ,("M + x^2", \row -> dualGlobalMargin row + dualOptimizerDisplacement row ^ (2 :: Int))
      ,("M + 1/4*neg(x)^2", \row -> dualGlobalMargin row + 0.25 * (max (-dualOptimizerDisplacement row) 0) ^ (2 :: Int))
      ,("M + 1/2*neg(x)^2", \row -> dualGlobalMargin row + 0.5 * (max (-dualOptimizerDisplacement row) 0) ^ (2 :: Int))
      ,("M + neg(x)^2", \row -> dualGlobalMargin row + (max (-dualOptimizerDisplacement row) 0) ^ (2 :: Int))
      ,("M + 1/4*d^2", \row -> dualGlobalMargin row + 0.25 * dualDeficit row ^ (2 :: Int))
      ,("M + 1/2*d^2", \row -> dualGlobalMargin row + 0.5 * dualDeficit row ^ (2 :: Int))
      ,("M + d^2", \row -> dualGlobalMargin row + dualDeficit row ^ (2 :: Int))]
    renderPotential (label, potential) =
      let values = map potential (reportDualDynamics report)
          changes = zipWith (-) (drop 1 values) values
          minValue = if null values then 0 / 0 else minimum values
          minChange = if null changes then 0 / 0 else minimum changes
          decreases = length (filter (< (-1e-12)) changes)
      in intercalate "  " [pad 31 label, pad 14 (fmt 9 minValue),
          pad 18 (fmt 9 minChange), show decreases]

renderExplorerCsv :: ExplorerReport -> String
renderExplorerCsv report
  | explorerMode (reportOptions report) == BusyMode = unlines $
      ["trust,status,start_event,recovery_before_event,event_count,root_start,root_end,root_width,t_width,starting_discrepancy,most_negative_discrepancy,ending_discrepancy,weighted_loss,psi_start,psi_end,minimum_psi,loss_over_reserve,loss_times_sqrt_start,loss_over_initial_backlog_sq,max_backlog_over_sqrt_start,arrival_mass,service_drift,arrival_over_service"] ++
      map renderBusyCsv (reportBusyPeriods report)
  | explorerMode (reportOptions report) == RootsMode = unlines $
      ["trust,status,event_q,next_event_r,u_star_before,u_star_after,sqrt_q,sqrt_r,root_displacement,rho,root_kick,kick_lower,kick_upper,sqrt_gap,kick_over_gap,normalized_root_impulse,active,global_margin,block_margin,margin_update,curvature_safety_energy,root_barrier_five_thirds,root_barrier_two,crude_gap_condition"] ++
      map renderRootCsv (reportDualDynamics report)
  | explorerMode (reportOptions report) == DualMode = unlines $
      ["trust,status,event_q,next_event_r,lambda_q,S_q,C_q,t_star,A_star,global_margin,deficit_q,arch_drift,next_lambda,predicted_next_deficit,active,block_margin,block_equals_global,event_area_update,event_value,safety_energy,safety_slack,curvature_lower,exact_curvature,curvature_safety_energy,exact_curvature_safety_energy,curvature_safety_slack,log_gap,convex_remainder,optimizer_displacement,kick_displacement,kick_area,pre_kick_displacement,post_kick_displacement,backlog_before,backlog_after,kick_over_lambda,kick_over_log_gap,prime_scale_kick_bound,curvature_scaled_deficit,next_lambda_over_drift,next_lambda_over_log_gap,drift_over_log_gap"] ++
      map renderDualCsv (reportDualDynamics report)
  | explorerMode (reportOptions report) == BlocksMode = unlines $
      ["trust,status,event_q,next_event_r,gap,S_q,C_q,slope_deficit_left,slope_deficit_right,margin,t_candidate,exp_t_candidate,minimizer_type,winning_cell"] ++
      map renderBlockCsv (reportBlockMargins report)
  | explorerMode (reportOptions report) == MarginsMode = unlines $
      ["trust,status,cell,S_n,C_n,dual,margin,t_candidate,minimizer_type,distance_since_event,distance_to_event,mangoldt_n,mangoldt_n_plus_1"] ++
      map renderMarginCsv (reportMargins report)
  | otherwise = unlines $
  ["trust,status,omega,cell,t_left,t_right,t_candidate,psi,derivative,second_derivative,distance_above_best,psi_over_t,psi_over_t2,exp_neg_half_psi,exp_neg_omega_psi,omega_t,prime_gap,theta,chebyshev_psi,psi_minus_n,left_prime_power,right_prime_power"] ++
  map renderCellCsv (reportCellMinima report)
  where
    renderBusyCsv period = intercalate ","
      ["NumericalEvidence", "candidate", show (busyStartEvent period)
      ,show (busyRecoveryBeforeEvent period), show (busyEventCount period)
      ,num (busyRootStart period), num (busyRootEnd period)
      ,num (busyRootWidth period), num (busyTWidth period)
      ,num (busyStartingDiscrepancy period)
      ,num (busyMostNegativeDiscrepancy period)
      ,num (busyEndingDiscrepancy period), num (busyWeightedLoss period)
      ,num (busyPsiStart period), num (busyPsiEnd period)
      ,num (busyMinimumPsi period), num (busyLossOverReserve period)
      ,num (busyLossTimesSqrtStart period)
      ,num (busyLossOverInitialBacklogSq period)
      ,num (busyMaxBacklogOverSqrtStart period)
      ,num (busyArrivalMass period), num (busyServiceDrift period)
      ,num (busyArrivalOverService period)]
    renderRootCsv row = intercalate ","
      ["NumericalEvidence", "candidate", show (dualEvent row)
      ,show (dualNextEvent row), num (dualRootOptimizer row)
      ,num (dualNextRootOptimizer row), num (dualSqrtEvent row)
      ,num (dualSqrtNextEvent row), num (dualRootDisplacement row)
      ,num (dualRootRatio row), num (dualRootKick row)
      ,num (dualRootKickLower row), num (dualRootKickUpper row)
      ,num (dualSqrtGap row), num (dualRootKickOverGap row)
      ,num (dualNormalizedRootImpulse row), boolText (dualActive row)
      ,num (dualGlobalMargin row), num (dualBlockMargin row)
      ,num (dualEventAreaUpdate row), num (dualCurvatureSafetyEnergy row)
      ,num (rootBarrierCsv (5 / 3) row), num (rootBarrierCsv 2 row)
      ,boolText (dualCrudeGapCondition row)]
    rootBarrierCsv coefficient row =
      let overshoot = max (-dualRootDisplacement row) 0
      in dualGlobalMargin row + coefficient * overshoot ^ (2 :: Int) /
        dualSqrtEvent row
    renderDualCsv row = intercalate ","
      ["NumericalEvidence", "candidate", show (dualEvent row)
      ,show (dualNextEvent row), num (dualLambda row), num (dualSlope row)
      ,num (dualIntercept row), num (dualOptimizer row), num (dualArchDual row)
      ,num (dualGlobalMargin row), num (dualDeficit row), num (dualArchDrift row)
      ,num (dualNextImpulse row), num (dualPredictedNextDeficit row)
      ,boolText (dualActive row), num (dualBlockMargin row)
      ,boolText (dualBlockEqualsGlobal row), num (dualEventAreaUpdate row)
      ,num (dualEventValue row), num (dualSafetyEnergy row)
      ,num (dualSafetySlack row), num (dualCurvatureLower row)
      ,num (dualExactCurvature row), num (dualCurvatureSafetyEnergy row)
      ,num (dualExactCurvatureSafetyEnergy row), num (dualCurvatureSafetySlack row)
      ,num (dualLogGap row)
      ,num (dualConvexRemainder row), num (dualOptimizerDisplacement row)
      ,num (dualKickDisplacement row), num (dualKickArea row)
      ,num (dualPreKickDisplacement row), num (dualPostKickDisplacement row)
      ,num (dualBacklogBefore row), num (dualBacklogAfter row)
      ,num (dualKickOverLambda row), num (dualKickOverLogGap row)
      ,num (dualPrimeScaleKickBound row), num (dualCurvatureScaledDeficit row)
      ,num (dualImpulseOverDrift row), num (dualImpulseOverLogGap row)
      ,num (dualDriftOverLogGap row)]
    renderBlockCsv row = intercalate ","
      ["NumericalEvidence", "candidate", show (blockLeftEvent row)
      ,show (blockRightEvent row), show (blockGap row), num (blockSlope row)
      ,num (blockIntercept row), num (blockSlopeDeficitLeft row)
      ,num (blockSlopeDeficitRight row), num (blockMarginValue row)
      ,num (blockCandidateT row), num (blockCandidateExpT row)
      ,blockMinimizerType row, show (blockWinningCell row)]
    renderMarginCsv row = intercalate ","
      ["NumericalEvidence", "candidate", show (marginCell row)
      ,num (marginSlope row), num (marginIntercept row), num (marginDual row)
      ,num (marginValue row), num (marginCandidateT row)
      ,marginMinimizerType row
      ,maybe "" show (marginSinceLastEvent row)
      ,maybe "" show (marginToNextEvent row)
      ,num (marginMangoldtLeft row), num (marginMangoldtRight row)]
    renderCellCsv cell = intercalate ","
      ["NumericalEvidence"
      ,statusText (statusForCell cell)
      ,num (cellOmega cell), show (cellIndex cell), num (cellLeft cell)
      ,num (cellRight cell), num (cellCandidateT cell), num (cellCandidateValue cell)
      ,num (cellDerivative cell), num (cellSecondDerivative cell)
      ,num (cellDistanceAboveBest cell), num (cellPsiOverT cell), num (cellPsiOverTSq cell)
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
  ,"  ],"
  ,"  \"critical_points\": ["
  ,intercalate ",\n" (map (indent 4 . criticalJson) (reportCriticalPoints report))
  ,"  ],"
  ,"  \"branches\": ["
  ,intercalate ",\n" (map (indent 4 . branchJson) (reportBranches report))
  ,"  ],"
  ,"  \"crossings\": ["
  ,intercalate ",\n" (map (indent 4 . crossingJson) (reportCrossings report))
  ,"  ],"
  ,"  \"margins\": ["
  ,intercalate ",\n" (map (indent 4 . marginJson) (reportMargins report))
  ,"  ],"
  ,"  \"mangoldt_blocks\": ["
  ,intercalate ",\n" (map (indent 4 . blockJson) (reportBlockMargins report))
  ,"  ],"
  ,"  \"dual_dynamics\": ["
  ,intercalate ",\n" (map (indent 4 . dualJson) (reportDualDynamics report))
  ,"  ],"
  ,"  \"busy_periods\": ["
  ,intercalate ",\n" (map (indent 4 . busyJson) (reportBusyPeriods report))
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
  ,jsonField "cross_check_error" (num (summaryCrossCheckError summary))
  ,jsonField "derivative_check_error" (num (summaryDerivativeCheckError summary))] ++ "}"

cellJson :: CellMinimum -> String
cellJson cell = "{" ++ intercalate ", "
  [jsonField "omega" (num (cellOmega cell))
  ,jsonField "prime_cell" (show (cellIndex cell))
  ,jsonField "t_left" (num (cellLeft cell))
  ,jsonField "t_right" (num (cellRight cell))
  ,jsonField "minimizing_t_candidate" (num (cellCandidateT cell))
  ,jsonField "minimum_candidate" (num (cellCandidateValue cell))
  ,jsonField "derivative" (num (cellDerivative cell))
  ,jsonField "second_derivative" (num (cellSecondDerivative cell))
  ,jsonField "distance_above_best" (num (cellDistanceAboveBest cell))
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

marginJson :: CellMargin -> String
marginJson row = "{" ++ intercalate ", "
  [jsonField "cell" (show (marginCell row))
  ,jsonField "slope_S_n" (num (marginSlope row))
  ,jsonField "intercept_C_n" (num (marginIntercept row))
  ,jsonField "dual_D_n" (num (marginDual row))
  ,jsonField "margin" (num (marginValue row))
  ,jsonField "minimizing_t_candidate" (num (marginCandidateT row))
  ,jsonField "minimizer_type" (jsonString (marginMinimizerType row))
  ,jsonField "distance_since_mangoldt_event"
      (maybe "null" show (marginSinceLastEvent row))
  ,jsonField "distance_to_mangoldt_event"
      (maybe "null" show (marginToNextEvent row))
  ,jsonField "mangoldt_n" (num (marginMangoldtLeft row))
  ,jsonField "mangoldt_n_plus_1" (num (marginMangoldtRight row))] ++ "}"

blockJson :: BlockMargin -> String
blockJson row = "{" ++ intercalate ", "
  [jsonField "event_q" (show (blockLeftEvent row))
  ,jsonField "next_event_r" (show (blockRightEvent row))
  ,jsonField "gap" (show (blockGap row))
  ,jsonField "slope_S_q" (num (blockSlope row))
  ,jsonField "intercept_C_q" (num (blockIntercept row))
  ,jsonField "slope_deficit_left" (num (blockSlopeDeficitLeft row))
  ,jsonField "slope_deficit_right" (num (blockSlopeDeficitRight row))
  ,jsonField "block_margin" (num (blockMarginValue row))
  ,jsonField "minimizing_t_candidate" (num (blockCandidateT row))
  ,jsonField "exp_minimizing_t_candidate" (num (blockCandidateExpT row))
  ,jsonField "minimizer_type" (jsonString (blockMinimizerType row))
  ,jsonField "winning_integer_cell" (show (blockWinningCell row))] ++ "}"

dualJson :: DualDynamics -> String
dualJson row = "{" ++ intercalate ", "
  [jsonField "event_q" (show (dualEvent row))
  ,jsonField "next_event_r" (show (dualNextEvent row))
  ,jsonField "lambda_q" (num (dualLambda row))
  ,jsonField "slope_S_q" (num (dualSlope row))
  ,jsonField "intercept_C_q" (num (dualIntercept row))
  ,jsonField "t_star" (num (dualOptimizer row))
  ,jsonField "arch_dual" (num (dualArchDual row))
  ,jsonField "global_dual_margin" (num (dualGlobalMargin row))
  ,jsonField "event_slope_deficit" (num (dualDeficit row))
  ,jsonField "archimedean_drift" (num (dualArchDrift row))
  ,jsonField "next_mangoldt_impulse" (num (dualNextImpulse row))
  ,jsonField "predicted_next_deficit" (num (dualPredictedNextDeficit row))
  ,jsonField "active_block" (jsonBool (dualActive row))
  ,jsonField "block_margin" (num (dualBlockMargin row))
  ,jsonField "block_equals_global" (jsonBool (dualBlockEqualsGlobal row))
  ,jsonField "event_area_update" (num (dualEventAreaUpdate row))
  ,jsonField "event_value" (num (dualEventValue row))
  ,jsonField "safety_energy" (num (dualSafetyEnergy row))
  ,jsonField "safety_slack" (num (dualSafetySlack row))
  ,jsonField "curvature_lower" (num (dualCurvatureLower row))
  ,jsonField "exact_curvature" (num (dualExactCurvature row))
  ,jsonField "curvature_safety_energy" (num (dualCurvatureSafetyEnergy row))
  ,jsonField "exact_curvature_safety_energy" (num (dualExactCurvatureSafetyEnergy row))
  ,jsonField "curvature_safety_slack" (num (dualCurvatureSafetySlack row))
  ,jsonField "log_gap" (num (dualLogGap row))
  ,jsonField "convex_remainder" (num (dualConvexRemainder row))
  ,jsonField "optimizer_displacement" (num (dualOptimizerDisplacement row))
  ,jsonField "kick_displacement" (num (dualKickDisplacement row))
  ,jsonField "kick_area" (num (dualKickArea row))
  ,jsonField "pre_kick_displacement" (num (dualPreKickDisplacement row))
  ,jsonField "post_kick_displacement" (num (dualPostKickDisplacement row))
  ,jsonField "backlog_before" (num (dualBacklogBefore row))
  ,jsonField "backlog_after" (num (dualBacklogAfter row))
  ,jsonField "kick_over_lambda" (num (dualKickOverLambda row))
  ,jsonField "kick_over_log_gap" (num (dualKickOverLogGap row))
  ,jsonField "prime_scale_kick_bound" (num (dualPrimeScaleKickBound row))
  ,jsonField "curvature_scaled_deficit" (num (dualCurvatureScaledDeficit row))
  ,jsonField "next_lambda_over_drift" (num (dualImpulseOverDrift row))
  ,jsonField "next_lambda_over_log_gap" (num (dualImpulseOverLogGap row))
  ,jsonField "drift_over_log_gap" (num (dualDriftOverLogGap row))
  ,jsonField "root_optimizer_before" (num (dualRootOptimizer row))
  ,jsonField "root_optimizer_after" (num (dualNextRootOptimizer row))
  ,jsonField "sqrt_event" (num (dualSqrtEvent row))
  ,jsonField "sqrt_next_event" (num (dualSqrtNextEvent row))
  ,jsonField "root_displacement" (num (dualRootDisplacement row))
  ,jsonField "root_ratio" (num (dualRootRatio row))
  ,jsonField "root_kick" (num (dualRootKick row))
  ,jsonField "root_kick_lower" (num (dualRootKickLower row))
  ,jsonField "root_kick_upper" (num (dualRootKickUpper row))
  ,jsonField "sqrt_gap" (num (dualSqrtGap row))
  ,jsonField "root_kick_over_gap" (num (dualRootKickOverGap row))
  ,jsonField "normalized_root_impulse" (num (dualNormalizedRootImpulse row))
  ,jsonField "crude_gap_condition" (jsonBool (dualCrudeGapCondition row))] ++ "}"

busyJson :: BusyPeriod -> String
busyJson period = "{" ++ intercalate ", "
  [jsonStringField "trust" "NumericalEvidence"
  ,jsonStringField "status" "candidate"
  ,jsonField "start_event" (show (busyStartEvent period))
  ,jsonField "recovery_before_event" (show (busyRecoveryBeforeEvent period))
  ,jsonField "event_count" (show (busyEventCount period))
  ,jsonField "root_start" (num (busyRootStart period))
  ,jsonField "root_end" (num (busyRootEnd period))
  ,jsonField "root_width" (num (busyRootWidth period))
  ,jsonField "t_width" (num (busyTWidth period))
  ,jsonField "starting_discrepancy" (num (busyStartingDiscrepancy period))
  ,jsonField "most_negative_discrepancy" (num (busyMostNegativeDiscrepancy period))
  ,jsonField "ending_discrepancy" (num (busyEndingDiscrepancy period))
  ,jsonField "weighted_loss" (num (busyWeightedLoss period))
  ,jsonField "psi_start" (num (busyPsiStart period))
  ,jsonField "psi_end" (num (busyPsiEnd period))
  ,jsonField "minimum_psi" (num (busyMinimumPsi period))
  ,jsonField "loss_over_reserve" (num (busyLossOverReserve period))
  ,jsonField "loss_times_sqrt_start" (num (busyLossTimesSqrtStart period))
  ,jsonField "loss_over_initial_backlog_sq"
      (num (busyLossOverInitialBacklogSq period))
  ,jsonField "max_backlog_over_sqrt_start"
      (num (busyMaxBacklogOverSqrtStart period))
  ,jsonField "arrival_mass" (num (busyArrivalMass period))
  ,jsonField "service_drift" (num (busyServiceDrift period))
  ,jsonField "arrival_over_service" (num (busyArrivalOverService period))] ++ "}"

criticalJson :: CriticalPoint -> String
criticalJson point = "{" ++ intercalate ", "
  [jsonField "omega" (num (criticalOmega point))
  ,jsonField "prime_cell" (show (criticalCell point))
  ,jsonField "t" (num (criticalT point))
  ,jsonField "psi" (num (criticalValue point))
  ,jsonField "derivative" (num (criticalDerivative point))
  ,jsonField "second_derivative" (num (criticalSecondDerivative point))
  ,jsonField "mixed_derivative" (num (criticalMixedDerivative point))
  ,jsonStringField "classification"
      (classificationText (criticalClassification point))] ++ "}"

branchJson :: BranchPoint -> String
branchJson point = "{" ++ intercalate ", "
  [jsonStringField "branch_id" (branchId point)
  ,jsonField "omega" (num (branchOmega point))
  ,jsonField "prime_cell" (show (branchCell point))
  ,jsonField "t" (num (branchT point))
  ,jsonField "minimum" (num (branchMinimum point))
  ,jsonField "curvature" (num (branchCurvature point))
  ,jsonField "dt_domega" (num (branchDtDomega point))] ++ "}"

crossingJson :: EnvelopeCrossing -> String
crossingJson crossing = "{" ++ intercalate ", "
  [jsonField "omega_cross" (num (crossingOmega crossing))
  ,jsonField "cell_a" (show (crossingCellA crossing))
  ,jsonField "cell_b" (show (crossingCellB crossing))
  ,jsonField "t_a" (num (crossingTA crossing))
  ,jsonField "t_b" (num (crossingTB crossing))
  ,jsonField "common_minimum" (num (crossingCommonMinimum crossing))] ++ "}"

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
  ,jsonField "strong_convex_sample" (rationalJson
      (certificateStrongSample certificate))
  ,jsonField "strong_convex_value_lower" (rationalJson
      (certificateStrongValueLower certificate))
  ,jsonField "strong_convex_deriv_abs_upper" (rationalJson
      (certificateStrongDerivAbsUpper certificate))
  ,jsonField "strong_convex_curvature_lower" (rationalJson
      (certificateStrongCurvatureLower certificate))
  ,jsonField "strong_convex_candidate_margin" (num
      (certificateStrongMargin certificate))
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

classificationText :: CriticalClassification -> String
classificationText LocalMinimum = "local_min"
classificationText LocalMaximum = "local_max"
classificationText CriticalUncertain = "uncertain"

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
