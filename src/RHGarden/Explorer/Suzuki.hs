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
  , ChebyshevProfilePoint(..)
  , BusyPeriod(..)
  , CandidateCertificate(..)
  , defaultExplorerOptions
  , parseExplorerOptions
  , exploreSuzuki
  , renderExplorerAscii
  , renderExplorerCsv
  , renderExplorerJson
  , renderBusyPeriodsJson
  , renderCertificatesJson
  , runSuzukiExplorer
  , runSuzukiEventRegression
  , runSuzukiSurchargeScan
  , suzukiPsiNumeric
  , psiShiftedNumeric
  , dPsiDt
  , d2PsiDt2
  , serviceDecayCellCostsNumeric
  , serviceDecayCellQuadratureNumeric
  ) where

import Data.Char (toLower)
import Data.List (intercalate, isSuffixOf, maximumBy, minimumBy,
  nubBy, sort, sortOn, zipWith4)
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
  , dualChebyshevPsi :: Double
  } deriving (Eq, Show)

-- | Numerically evaluated terms in the Lean-checked identity
-- Arrival - Service = transformed Chebyshev error + archimedean defect.
-- The residual is a regression diagnostic, never proof evidence.
data ChebyshevProfilePoint = ChebyshevProfilePoint
  { profileRoot :: Double
  , profileIntegerX :: Double
  , profileChebyshevError :: Double
  , profileBoundaryContribution :: Double
  , profileIntegralContribution :: Double
  , profileArchDefect :: Double
  , profileTransformedExcess :: Double
  , profileExactExcess :: Double
  , profileDecompositionResidual :: Double
  , profileBacklog :: Double
  , profileWeightedLoss :: Double
  , profileJumpAwareUpper :: Double
  , profileJumpAwareGap :: Double
  , profileOutgoingService :: Double
  , profileOutgoingExactCost :: Double
  , profileOutgoingLinearCost :: Double
  , profileCumulativeExactCost :: Double
  , profileRemainingReserve :: Double
  , profileEventExcessUpper :: Double
  , profileTransformedGap :: Double
  , profileOutgoingEnvelopeCost :: Double
  , profileOutgoingEnvelopeLinearCost :: Double
  , profileCumulativeEnvelopeCost :: Double
  , profileEnvelopeReserveRemaining :: Double
  , profileLocalWidthExcessUpper :: Double
  , profileOutgoingLocalWidthCost :: Double
  , profileEventLogExcessUpper :: Double
  , profileOutgoingEventLogCost :: Double
  , profilePinnedExcessUpper :: Double
  , profileOutgoingPinnedCost :: Double
  } deriving (Eq, Show)

-- | A maximal numerically detected interval on which the right-continuous
-- root-slope discrepancy is negative.  A period may cross several Mangoldt
-- impulses before smooth archimedean service returns the discrepancy to zero.
-- These records are NumericalEvidence only.
data BusyPeriod = BusyPeriod
  { busyStartEvent :: Int
  , busyRecoveryBeforeEvent :: Int
  , busyEventCount :: Int
  , busyIntervalStart :: Int
  , busyIntervalEnd :: Int
  , busyIntervalWidth :: Int
  , busyEffectiveTheta :: Double
  , busyWidthOverSqrtStart :: Double
  , busyWidthOverSqrtLogStart :: Double
  , busyGuthMaynardScaleRatio :: Double
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
  , busyPinnedPrefixArrivalUpper :: Double
  , busyPinnedBoundOverArrival :: Double
  , busyPinnedExcessOverService :: Double
  , busyPinnedBoundOverRequired :: Double
  , busyPinnedBoundExcessOverRequired :: Double
  , busyArrivalExcessBudget :: Double
  , busyActualMaxArrivalServiceExcess :: Double
  , busyPrefixEnvelopeSlack :: Double
  , busyRequiredArrivalUpper :: Double
  , busyArrivalSlack :: Double
  , busyEpsilonRequired :: Double
  , busyPrefixEpsilonRequired :: Double
  , busyCheckedElementaryArrivalUpper :: Double
  , busyArithmeticBoundFactor :: Double
  , busyArithmeticBoundExcess :: Double
  , busyProfileMaxResidual :: Double
  , busyChebyshevIncrementSlopeRequired :: Double
  , busyAnchoredLinearEnvelopeEpsilonBudget :: Double
  , busyAnchoredLinearEnvelopeSlack :: Double
  , busyFiniteEventExactCost :: Double
  , busyFiniteEventLinearCost :: Double
  , busyFiniteEventCostResidual :: Double
  , busyFiniteEventReserveRemaining :: Double
  , busyJumpAwareMaxGap :: Double
  , busyEnvelopeCost :: Double
  , busyEnvelopeLinearCost :: Double
  , busyEnvelopeCostGap :: Double
  , busyEnvelopeReserveRemaining :: Double
  , busyEnvelopeMaxExcessGap :: Double
  , busyEnvelopeFirstFailingCell :: Maybe Int
  , busyLocalWidthCost :: Double
  , busyLocalWidthReserveRemaining :: Double
  , busyLocalWidthFirstFailingCell :: Maybe Int
  , busyEventLogCost :: Double
  , busyEventLogReserveRemaining :: Double
  , busyEventLogFirstFailingCell :: Maybe Int
  , busyPrimePowerSurcharge :: Double
  , busySurchargeIdentityResidual :: Double
  , busyPinnedAnchoredCost :: Double
  , busyPinnedAnchoredFirstFailingCell :: Maybe Int
  , busyChebyshevProfile :: [ChebyshevProfilePoint]
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
      eventOnly = explorerMode checked `elem` [DualMode, RootsMode, BusyMode]
      maximumCells :: Int
      maximumCells = if eventOnly then 20000000 else 2000000
  if nMaxDouble > fromIntegral maximumCells
    then Left $ "t-max creates more than " ++ show maximumCells ++
      " arithmetic cells for this mode; use a smaller exploratory range"
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
      , busyIntervalStart = intervalStart
      , busyIntervalEnd = intervalEnd
      , busyIntervalWidth = intervalWidth
      , busyEffectiveTheta = thetaEff
      , busyWidthOverSqrtStart = safeRatio (fromIntegral intervalWidth)
          (sqrt (fromIntegral intervalStart))
      , busyWidthOverSqrtLogStart = safeRatio (fromIntegral intervalWidth)
          (sqrt (fromIntegral intervalStart) * log (fromIntegral intervalStart))
      , busyGuthMaynardScaleRatio = safeRatio (fromIntegral intervalWidth)
          (fromIntegral intervalStart ** (17 / 30))
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
      , busyPinnedPrefixArrivalUpper = pinnedUpper
      , busyPinnedBoundOverArrival = safeRatio pinnedUpper arrival
      , busyPinnedExcessOverService = pinnedUpper - service
      , busyPinnedBoundOverRequired = safeRatio pinnedUpper requiredArrivalUpper
      , busyPinnedBoundExcessOverRequired = pinnedUpper - requiredArrivalUpper
      , busyArrivalExcessBudget = arrivalExcessBudget
      , busyActualMaxArrivalServiceExcess = actualMaxArrivalServiceExcess
      , busyPrefixEnvelopeSlack = prefixEnvelopeSlack
      , busyRequiredArrivalUpper = requiredArrivalUpper
      , busyArrivalSlack = arrivalSlack
      -- The terminal metric requested by the certificate diagnostics.
      , busyEpsilonRequired = safeRatio arrivalSlack arrival
      -- The stronger prefix-uniform diagnostic used by the actual verifier.
      , busyPrefixEpsilonRequired = safeRatio prefixEnvelopeSlack arrival
      , busyCheckedElementaryArrivalUpper = checkedElementaryUpper
      , busyArithmeticBoundFactor = safeRatio checkedElementaryUpper
          requiredArrivalUpper
      , busyArithmeticBoundExcess = checkedElementaryUpper - requiredArrivalUpper
      , busyProfileMaxResidual = maximum
          (map (abs . profileDecompositionResidual) chebyshevProfile)
      , busyChebyshevIncrementSlopeRequired = incrementSlopeRequired
      , busyAnchoredLinearEnvelopeEpsilonBudget = anchoredEnvelopeBudget
      , busyAnchoredLinearEnvelopeSlack = anchoredEnvelopeBudget - incrementSlopeRequired
      , busyFiniteEventExactCost = finiteExactCost
      , busyFiniteEventLinearCost = finiteLinearCost
      , busyFiniteEventCostResidual = finiteExactCost - loss
      , busyFiniteEventReserveRemaining = psiStart - finiteExactCost
      , busyJumpAwareMaxGap = maximum (0 : map profileJumpAwareGap chebyshevProfile)
      , busyEnvelopeCost = envelopeCost
      , busyEnvelopeLinearCost = sum envelopeLinearCosts
      , busyEnvelopeCostGap = envelopeCost - finiteExactCost
      , busyEnvelopeReserveRemaining = psiStart - envelopeCost
      , busyEnvelopeMaxExcessGap = maximum (0 : eventExcessGaps)
      , busyEnvelopeFirstFailingCell = firstFailingCell envelopeCosts
      , busyLocalWidthCost = sum localWidthCosts
      , busyLocalWidthReserveRemaining = psiStart - sum localWidthCosts
      , busyLocalWidthFirstFailingCell = firstFailingCell localWidthCosts
      , busyEventLogCost = sum eventLogCosts
      , busyEventLogReserveRemaining = psiStart - sum eventLogCosts
      , busyEventLogFirstFailingCell = firstFailingCell eventLogCosts
      , busyPrimePowerSurcharge = surcharge
      , busySurchargeIdentityResidual = sum eventLogCosts - loss - surcharge
      , busyPinnedAnchoredCost = sum pinnedAnchoredCosts
      , busyPinnedAnchoredFirstFailingCell = firstFailingCell pinnedAnchoredCosts
      , busyChebyshevProfile = chebyshevProfile
      }
      where
        first = head rows
        final = last rows
        initialRows = init rows
        surcharge = sum
          [(log (fromIntegral (dualNextEvent row)) / dualSqrtNextEvent row -
            dualNextImpulse row) * log (rootEnd * rootEnd / fromIntegral (dualNextEvent row))
          | row <- initialRows]
        rootStart = dualSqrtEvent first
        rootEnd = dualRootOptimizer final
        intervalStart = ceiling (rootStart * rootStart - 1e-9)
        intervalEnd = floor (rootEnd * rootEnd + 1e-9)
        intervalWidth = max 0 (intervalEnd - intervalStart)
        thetaEff
          | intervalStart > 1 && intervalWidth > 0 =
              log (fromIntegral intervalWidth) / log (fromIntegral intervalStart)
          | otherwise = 0 / 0
        startD = dualDeficit first
        psiStart = dualEventValue first
        psiEnd = dualBlockMargin final
        loss = psiStart - psiEnd
        arrival = sum (map dualNextImpulse initialRows)
        service = sum (map dualArchDrift initialRows) - dualDeficit final
        initialBacklog = max (-startD) 0
        -- The checked rectangle-envelope verifier asks for every local prefix
        -- arrival to be at most service plus this excess budget.  The terminal
        -- value below is a diagnostic proxy for that pointwise requirement.
        arrivalExcessBudget
          | rootEnd > rootStart =
              psiStart * rootStart / (2 * (rootEnd - rootStart)) - initialBacklog
          | otherwise = 0 / 0
        -- At an event root, Arrival-Service equals D(start)-D(current).
        -- Discrepancy rises between events, so the most negative event state
        -- gives the exact sampled maximum prefix excess for this excursion.
        actualMaxArrivalServiceExcess =
          startD - minimum (map dualDeficit rows)
        prefixEnvelopeSlack =
          arrivalExcessBudget - actualMaxArrivalServiceExcess
        requiredArrivalUpper = service + arrivalExcessBudget
        arrivalSlack = requiredArrivalUpper - arrival
        endpoint = fromIntegral (dualNextEvent final)
        endpointLog = log endpoint
        -- Numerical evaluation of Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise.
        -- Applying a global prefix estimate to a short busy interval discards
        -- the lower prefix; the resulting looseness is itself research data.
        pinnedUpper = 2 * log 4 * sqrt endpoint + 2 * endpointLog +
          endpointLog * endpointLog / 2
        checkedEndpoint = fromIntegral intervalEnd
        checkedStart = fromIntegral intervalStart
        checkedWidth = fromIntegral intervalWidth
        -- Numerical value of weightedMangoldtInterval_le_localWidth.
        checkedElementaryUpper
          | intervalEnd > 1 = checkedWidth * log checkedEndpoint /
              sqrt (checkedStart + 1)
          | otherwise = 0
        startChebyshevError = dualChebyshevPsi first - fromIntegral (dualEvent first)
        startArchSlope = dualSlope first + dualDeficit first
        segmentIntegral row endpointRoot =
          let leftRoot = dualSqrtEvent row
              chebyshev = dualChebyshevPsi row
          in chebyshev * (1 / leftRoot - 1 / endpointRoot) -
              (endpointRoot - leftRoot)
        eventIntegrals = scanl (+) 0
          [segmentIntegral row (dualSqrtNextEvent row) | row <- initialRows]
        outgoingEndpointRoots = map dualSqrtNextEvent initialRows ++ [rootEnd]
        coarsenedSampleUpper row =
          let q = fromIntegral (dualEvent row)
              rValue = dualChebyshevPsi row - q
          in if dualEvent row == dualEvent first then rValue
             else fromIntegral (ceiling (1000 * rValue) :: Integer) / 1000
        sampleGap row = coarsenedSampleUpper row -
          (dualChebyshevPsi row - fromIntegral (dualEvent row))
        integralGaps = scanl (+) 0
          [sampleGap row * (1 / dualSqrtEvent row - 1 / dualSqrtNextEvent row)
          | row <- initialRows]
        -- The exact anchor R(m) is subtracted, never rounded. Every sample
        -- allowance is charged both at its endpoint and in earlier cells.
        eventExcessGaps = zipWith (\row ig -> sampleGap row / dualSqrtEvent row + ig)
          rows integralGaps
        envelopeCostsAndLinear = zipWith3
          (\row endpointRoot gap -> serviceDecayCellCostsNumeric
            (dualSqrtEvent row) endpointRoot (-dualDeficit row + gap))
          rows outgoingEndpointRoots eventExcessGaps
        envelopeCosts = map fst envelopeCostsAndLinear
        envelopeLinearCosts = map snd envelopeCostsAndLinear
        envelopeCost = sum envelopeCosts
        envelopeCumulativeBefore = init (scanl (+) 0 envelopeCosts)
        localWidthExcess row =
          let q = fromIntegral (dualEvent row)
              m = fromIntegral (dualEvent first)
              serviceToRoot = dualSlope row + dualDeficit row - startArchSlope
          in (q - m) * log q / sqrt (m + 1) - serviceToRoot
        localWidthCosts = zipWith (\row endpointRoot -> fst
          (serviceDecayCellCostsNumeric (dualSqrtEvent row) endpointRoot
            (-startD + localWidthExcess row))) rows outgoingEndpointRoots
        -- Pinned vonMangoldt_le_log, applied only at complete event roots.
        -- Prime powers are deliberately overcharged by log(q), while the
        -- anchor jump is excluded. This is a conservative finite coarsening.
        eventLogGaps = scanl (+) 0
          [log (fromIntegral (dualNextEvent row)) / dualSqrtNextEvent row -
            dualNextImpulse row | row <- initialRows]
        eventLogCosts = zipWith3 (\row endpointRoot gap -> fst
          (serviceDecayCellCostsNumeric (dualSqrtEvent row) endpointRoot
            (-dualDeficit row + gap))) rows outgoingEndpointRoots eventLogGaps
        -- Exact anchored cancellation is proved in SuzukiPinnedEventBound.
        -- Keep the starting state exact; only later event bounds use P(q).
        pinnedSignedUpper row
          | dualEvent row == dualEvent first = -startD
          | otherwise = let q = fromIntegral (dualEvent row); lq = log q
                            p = 2 * log 4 * sqrt q + 2 * lq + lq * lq / 2
                        in p - (dualSlope row + dualDeficit row)
        pinnedAnchoredCosts = zipWith (\row endpointRoot -> fst
          (serviceDecayCellCostsNumeric (dualSqrtEvent row) endpointRoot
            (pinnedSignedUpper row))) rows outgoingEndpointRoots
        firstFailingCell costs = case
            [dualEvent row | (row, total) <- zip rows (drop 1 (scanl (+) 0 costs)),
              total > psiStart + 1e-10] of
          [] -> Nothing
          q : _ -> Just q
        cellCosts row endpointRoot =
          let leftRoot = dualSqrtEvent row
              pLeft = dualSlope row + dualDeficit row
              (exactCost, linearCost) = serviceDecayCellCostsNumeric
                leftRoot endpointRoot (-dualDeficit row)
          in (exactCost, linearCost,
              archimedeanDerivative (2 * log endpointRoot) - pLeft)
        outgoingCosts = zipWith cellCosts rows outgoingEndpointRoots
        exactCosts = [cost | (cost, _, _) <- outgoingCosts]
        linearCosts = [cost | (_, cost, _) <- outgoingCosts]
        cumulativeBefore = init (scanl (+) 0 exactCosts)
        finiteExactCost = sum exactCosts
        finiteLinearCost = sum linearCosts
        eventPoint row integralContribution endpointRoot cumulativeCost =
          let root = dualSqrtEvent row
              x = fromIntegral (dualEvent row)
              errorValue = dualChebyshevPsi row - x
              boundary = errorValue / root - startChebyshevError / rootStart
              serviceToRoot = dualSlope row + dualDeficit row - startArchSlope
              archDefect = 2 * (root - rootStart) - serviceToRoot
              transformed = boundary + integralContribution + archDefect
              exactExcess = startD - dualDeficit row
              rhoUpper = coarsenedSampleUpper row
              jumpUpper = fromIntegral (dualEvent row) + rhoUpper - x
              (outCost, outLinearCost, outService) = cellCosts row endpointRoot
          in ChebyshevProfilePoint
            { profileRoot = root
            , profileIntegerX = x
            , profileChebyshevError = errorValue
            , profileBoundaryContribution = boundary
            , profileIntegralContribution = integralContribution
            , profileArchDefect = archDefect
            , profileTransformedExcess = transformed
            , profileExactExcess = exactExcess
            , profileDecompositionResidual = transformed - exactExcess
            , profileBacklog = max (-dualDeficit row) 0
            , profileWeightedLoss = psiStart - dualEventValue row
            , profileJumpAwareUpper = jumpUpper
            , profileJumpAwareGap = jumpUpper - errorValue
            , profileOutgoingService = outService
            , profileOutgoingExactCost = outCost
            , profileOutgoingLinearCost = outLinearCost
            , profileCumulativeExactCost = cumulativeCost
            , profileRemainingReserve = psiStart - cumulativeCost
            , profileEventExcessUpper = exactExcess
            , profileTransformedGap = 0
            , profileOutgoingEnvelopeCost = 0
            , profileOutgoingEnvelopeLinearCost = 0
            , profileCumulativeEnvelopeCost = 0
            , profileEnvelopeReserveRemaining = psiStart
            , profileLocalWidthExcessUpper = localWidthExcess row
            , profileOutgoingLocalWidthCost = 0
            , profileEventLogExcessUpper = exactExcess
            , profileOutgoingEventLogCost = 0
            , profilePinnedExcessUpper = startD + pinnedSignedUpper row
            , profileOutgoingPinnedCost = 0
            }
        exactEventProfile = zipWith4 eventPoint rows eventIntegrals
          outgoingEndpointRoots cumulativeBefore
        roundedEventProfile = zipWith4 (\point gap (cost, linearCost, localCost) cumulative -> point
          { profileEventExcessUpper = profileExactExcess point + gap
          , profileTransformedGap = gap
          , profileOutgoingEnvelopeCost = cost
          , profileOutgoingEnvelopeLinearCost = linearCost
          , profileCumulativeEnvelopeCost = cumulative
          , profileEnvelopeReserveRemaining = psiStart - cumulative
          , profileOutgoingLocalWidthCost = localCost
          }) exactEventProfile eventExcessGaps
          (zip3 envelopeCosts envelopeLinearCosts localWidthCosts) envelopeCumulativeBefore
        eventProfile = zipWith4 (\point gap cost pinnedCost -> point
          { profileEventLogExcessUpper = profileExactExcess point + gap
          , profileOutgoingEventLogCost = cost
          , profileOutgoingPinnedCost = pinnedCost
          }) roundedEventProfile eventLogGaps eventLogCosts pinnedAnchoredCosts
        integralBeforeFinal = last eventIntegrals
        recoveryIntegral = integralBeforeFinal + segmentIntegral final rootEnd
        recoveryX = rootEnd * rootEnd
        recoveryError = dualChebyshevPsi final - recoveryX
        recoveryBoundary = recoveryError / rootEnd - startChebyshevError / rootStart
        recoveryService = dualSlope final - startArchSlope
        recoveryDefect = 2 * (rootEnd - rootStart) - recoveryService
        recoveryTransformed = recoveryBoundary + recoveryIntegral + recoveryDefect
        recoveryPoint = ChebyshevProfilePoint
          { profileRoot = rootEnd
          , profileIntegerX = recoveryX
          , profileChebyshevError = recoveryError
          , profileBoundaryContribution = recoveryBoundary
          , profileIntegralContribution = recoveryIntegral
          , profileArchDefect = recoveryDefect
          , profileTransformedExcess = recoveryTransformed
          , profileExactExcess = startD
          , profileDecompositionResidual = recoveryTransformed - startD
          , profileBacklog = 0
          , profileWeightedLoss = loss
          , profileJumpAwareUpper = fromIntegral (dualEvent final) +
              coarsenedSampleUpper final - recoveryX
          , profileJumpAwareGap = fromIntegral (dualEvent final) +
              coarsenedSampleUpper final - recoveryX - recoveryError
          , profileOutgoingService = 0
          , profileOutgoingExactCost = 0
          , profileOutgoingLinearCost = 0
          , profileCumulativeExactCost = finiteExactCost
          , profileRemainingReserve = psiStart - finiteExactCost
          , profileEventExcessUpper = startD + recoveryGap
          , profileTransformedGap = recoveryGap
          , profileOutgoingEnvelopeCost = 0
          , profileOutgoingEnvelopeLinearCost = 0
          , profileCumulativeEnvelopeCost = envelopeCost
          , profileEnvelopeReserveRemaining = psiStart - envelopeCost
          , profileLocalWidthExcessUpper = checkedElementaryUpper - service
          , profileOutgoingLocalWidthCost = 0
          , profileEventLogExcessUpper = startD + last eventLogGaps
          , profileOutgoingEventLogCost = 0
          , profilePinnedExcessUpper = startD + pinnedSignedUpper final -
              (dualSlope final - (dualSlope final + dualDeficit final))
          , profileOutgoingPinnedCost = 0
          }
        recoveryGap = last integralGaps + sampleGap final *
          (1 / dualSqrtEvent final - 1 / rootEnd) + sampleGap final / rootEnd
        chebyshevProfile = eventProfile ++ [recoveryPoint]
        startX = fromIntegral (dualEvent first)
        incrementSlopeRequired = maximum (0 :
          [max 0 ((profileChebyshevError point - startChebyshevError) /
            (profileIntegerX point - startX))
          | point <- chebyshevProfile, profileIntegerX point > startX])
        -- Numerical audit for the anchored family
        -- U_m(x)=R(m)+eps*(x-m), which preserves the exact start value used by
        -- the Lean certificate.  Its transformed error profile is exactly
        -- 2*eps*(u-sqrt(m)); only quadrature of the positive-part loss remains
        -- numerical here.
        anchoredEnvelopeLoss epsilon = trapezoidArea
          [(profileRoot point,
            2 / profileRoot point * max 0
              (initialBacklog + 2 * epsilon *
                (profileRoot point - rootStart) + profileArchDefect point))
          | point <- chebyshevProfile]
        anchoredEnvelopeBudget = bisectIncreasing 0 (findUpper 1e-6) (60 :: Int)
          (\epsilon -> anchoredEnvelopeLoss epsilon <= psiStart)
        findUpper upper
          | upper >= 1 = upper
          | anchoredEnvelopeLoss upper > psiStart = upper
          | otherwise = findUpper (2 * upper)
        bisectIncreasing lower _upper 0 _ = lower
        bisectIncreasing lower upper iterations predicate
          | predicate midpoint = bisectIncreasing midpoint upper
              (iterations - 1) predicate
          | otherwise = bisectIncreasing lower midpoint
              (iterations - 1) predicate
          where midpoint = (lower + upper) / 2
        trapezoidArea points = sum
          [ (x1 - x0) * (y0 + y1) / 2
          | ((x0, y0), (x1, y1)) <- zip points (drop 1 points)]
        safeRatio numerator denominator
          | abs denominator < 1e-15 = 0 / 0
          | otherwise = numerator / denominator

buildDualDynamics :: ExplorerOptions -> [PrimeEvent] -> [DualDynamics]
buildDualDynamics options events = case events of
    [] -> []
    firstEvent : _ -> go 0 0 0
      (integrateArchDerivative 0 (eventLogN firstEvent)) events
  where
    go _ _ _ _ [] = []
    go _ _ _ _ [_] = []
    go preSlope preIntercept preChebyshev archLeft (event : nextEvent : rest) =
      let slope = preSlope + eventWeight event
          intercept = preIntercept + eventWeight event * eventLogN event
          chebyshev = preChebyshev + eventMangoldt event
          archRight = archLeft + integrateArchDerivative
            (eventLogN event) (eventLogN nextEvent)
          remaining = go slope intercept chebyshev archRight (nextEvent : rest)
      in if eventLogN nextEvent < explorerTMin options - 1e-12 ||
            eventLogN event > explorerTMax options + 1e-12
          then remaining
          else build slope intercept chebyshev archLeft archRight event nextEvent : remaining
    build slope intercept chebyshev archLeft archRight event nextEvent = DualDynamics
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
          , dualChebyshevPsi = chebyshev
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

-- | Exploratory Double evaluation of the proved real cell formula. This
-- uses a numerical cutoff, not outward bounds or a Lean certificate.
-- The state k is signed: surplus is retained until the positive part.
serviceDecayCellCostsNumeric :: Double -> Double -> Double -> (Double, Double)
serviceDecayCellCostsNumeric r s k
  | s <= r || k <= 0 = (0, 0)
  | otherwise = (max 0 exactCost, max 0 linearCost)
  where
    p = archimedeanDerivative (2 * log r)
    h = serviceCutoffNumeric r s k
    hl = min s (r + 3 * k / 5)
    -- Integrating the archimedean increment directly avoids subtracting
    -- two large evaluations of A in a very narrow cell.
    exactCost = 2 * (k + p) * log (h / r) -
      integrateArchDerivative (2 * log r) (2 * log h)
    linearCost = 2 * (k + 5 * r / 3) * log (hl / r) - 10 * (hl - r) / 3

serviceCutoffNumeric :: Double -> Double -> Double -> Double
serviceCutoffNumeric r s k
  | k <= 0 || s <= r = r
  | archimedeanDerivative (2 * log s) <= target = s
  | otherwise = exp (bisectArchSlope 60 target (2 * log r) (2 * log s) / 2)
  where target = archimedeanDerivative (2 * log r) + k

-- | Independent integration of the weighted density, for regression only.
serviceDecayCellQuadratureNumeric :: Double -> Double -> Double -> Double
serviceDecayCellQuadratureNumeric r s k
  | s <= r || k <= 0 = 0
  | otherwise = adaptiveSimpson 1e-12 18 density r (serviceCutoffNumeric r s k)
  where
    p = archimedeanDerivative (2 * log r)
    density u = 2 / u * max 0 (k - (archimedeanDerivative (2 * log u) - p))

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

-- | Reproduce the reported scan and retain every event row of the two
-- named regressions. The ordinary UI export deliberately samples rows.
runSuzukiEventRegression :: FilePath -> IO ()
runSuzukiEventRegression path = case exploreSuzuki options of
  Left err -> ioError (userError err)
  Right report -> do
    let periods = reportBusyPeriods report
        selected = filter (\p -> busyStartEvent p `elem` [31, 324431, 8573249]) periods
        eventLogFailures = filter ((< (-1e-10)) . busyEventLogReserveRemaining) periods
        oldPass = length (filter ((>= 0) . busyAnchoredLinearEnvelopeSlack) periods)
        newPass = length (filter ((>= (-1e-10)) . busyEnvelopeReserveRemaining) periods)
        localPass = length (filter ((>= (-1e-10)) . busyLocalWidthReserveRemaining) periods)
        eventLogPass = length (filter ((>= (-1e-10)) . busyEventLogReserveRemaining) periods)
        valid = length periods == 10341 && oldPass == 7872 && length selected == 3 &&
          newPass == 10341 && localPass == 10147 && eventLogPass == 10340 &&
          map busyStartEvent eventLogFailures == [31] &&
          all ((< 1e-7) . abs . busyFiniteEventCostResidual) periods &&
          all ((< 1e-7) . abs . busySurchargeIdentityResidual) periods &&
          all (\p -> busyEnvelopeCostGap p >= -1e-8 &&
            busyEventLogCost p + 1e-8 >= busyFiniteEventExactCost p &&
            busyEnvelopeMaxExcessGap p <= 0.0010001 / busyRootStart p &&
            busyEnvelopeLinearCost p + 1e-8 >= busyEnvelopeCost p) periods &&
          any (\p -> busyStartEvent p == 324431 && busyRecoveryBeforeEvent p == 361201 &&
            busyArrivalSlack p > 0 && busyPrefixEnvelopeSlack p < 0) selected &&
          any (\p -> busyStartEvent p == 8573249 && busyRecoveryBeforeEvent p == 8906237 &&
            busyAnchoredLinearEnvelopeSlack p < -6) selected
        summary = "{" ++ intercalate ", "
          [jsonStringField "trust" "NumericalEvidence"
          ,jsonField "t_max" (num (explorerTMax options))
          ,jsonField "actual_cutoff" (show (floor (exp (explorerTMax options)) :: Int))
          ,jsonField "periods" (show (length periods))
          ,jsonField "old_affine_pass" (show oldPass)
          ,jsonField "old_affine_fail" (show (length periods - oldPass))
          ,jsonField "jump_sample_pass" (show newPass)
          ,jsonField "local_width_pass" (show localPass)
          ,jsonField "event_log_pass" (show eventLogPass)
          ,jsonField "max_surcharge_identity_residual" (num (maximum
              (0 : map (abs . busySurchargeIdentityResidual) periods)))
          ,jsonField "max_cost_residual" (num (maximum (0 : map (abs . busyFiniteEventCostResidual) periods)))
          ,jsonField "max_envelope_cost_gap" (num (maximum (0 : map busyEnvelopeCostGap periods)))
          ,jsonField "regressions_pass" (jsonBool valid)] ++ "}"
    putStrLn summary
    if valid then pure () else ioError (userError "Suzuki numerical regression failed")
    writeFile path ("{\n\"summary\": " ++ summary ++ ",\n\"regressions\": [\n" ++
      intercalate ",\n" (map (busyJsonWithProfile True) selected) ++
      "\n],\n\"event_log_failures\": [\n" ++
      intercalate ",\n" (map (busyJsonWithProfile True) eventLogFailures) ++ "\n]}\n")
    putStrLn ("Wrote full NumericalEvidence event diagnostics to " ++ path)
  where
    options = defaultExplorerOptions
      { explorerMode = BusyMode, explorerOmegas = [0], explorerTMin = log 2
      , explorerTMax = 16.118095, explorerSamples = 401, explorerPrimeCells = True }

-- | A full-origin scan: every window inherits its actual arithmetic state.
-- Only completed excursions are ranked; the terminal gap is reported, not
-- silently promoted to a coverage theorem.
runSuzukiSurchargeScan :: Int -> FilePath -> IO ()
runSuzukiSurchargeScan cutoff path = case exploreSuzuki options of
  Left err -> ioError (userError err)
  Right report -> do
    let periods = reportBusyPeriods report
        gap p = busyPsiEnd p - busyPrimePowerSurcharge p
        failures = filter ((< (-1e-10)) . gap) periods
        ranked = take 20 (sortOn gap periods)
        rows = reportDualDynamics report
        actualCutoff = floor (exp (explorerTMax options)) :: Int
        terminal = case reverse rows of
          row : _ -> let terminalSlope = dualSlope row +
                           (if dualNextEvent row <= actualCutoff then dualNextImpulse row else 0)
                         terminalD = archimedeanDerivative (log (fromIntegral actualCutoff)) - terminalSlope
                     in "{" ++ intercalate ", "
            [jsonField "last_event" (show (dualEvent row))
            ,jsonField "next_event" (show (dualNextEvent row))
            ,jsonField "signed_discrepancy" (num (dualDeficit row))
            ,jsonField "unrestricted_recovery_square" (num (dualRootOptimizer row ^ (2 :: Int)))
            ,jsonField "unfinished_at_last_event" (jsonBool (dualDeficit row < 0))
            ,jsonField "arithmetic_slope_at_cutoff" (num terminalSlope)
            ,jsonField "signed_discrepancy_at_cutoff" (num terminalD)
            ,jsonField "unfinished_at_cutoff" (jsonBool (terminalD < 0))] ++ "}"
          [] -> "null"
        summary = "{" ++ intercalate ", "
          [jsonStringField "trust" "NumericalEvidence"
          ,jsonField "requested_cutoff" (show cutoff)
          ,jsonField "actual_cutoff" (show (floor (exp (explorerTMax options)) :: Int))
          ,jsonField "completed_periods" (show (length periods))
          ,jsonField "surcharge_failures" (show (length failures))
          ,jsonField "max_identity_residual" (num (maximum
            (0 : map (abs . busySurchargeIdentityResidual) periods)))
          ,jsonStringField "coverage" "Completed excursions only; no eventual-recovery assumption or positivity claim for the terminal interval."
          ,jsonField "terminal_state" terminal] ++ "}"
    putStrLn summary
    writeFile path ("{\n\"summary\": " ++ summary ++ ",\n\"worst_margins\": [\n" ++
      intercalate ",\n" (map busyJson ranked) ++ "\n],\n\"failures\": [\n" ++
      intercalate ",\n" (map (busyJsonWithProfile True) failures) ++ "\n]}\n")
  where
    options = defaultExplorerOptions
      { explorerMode = BusyMode, explorerOmegas = [0], explorerTMin = log 2
      , explorerTMax = log (fromIntegral cutoff), explorerSamples = 401
      , explorerPrimeCells = True }

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
  , "Lean-certified finite coverage: [0, log 37], with fresh cell reserves; no infinite tail is proved."
  , "Lean-certified initial coverage: [0,log 2], with strict positivity on (0,log 3]."
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
      , "start    recover<  events  x          h        theta     epsilon req   loss/reserve  elementary/required"
      , "---------------------------------------------------------------------------------------------------------"
      ] ++ map renderBusy busyRowsForDisplay ++ busySummarySection ++
        busyScaleSection ++ busyProfileSection ++ busyRankingSection
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
      , pad 10 (show (busyIntervalStart period))
      , pad 8 (show (busyIntervalWidth period))
      , pad 9 (fmt 6 (busyEffectiveTheta period))
      , pad 13 (fmt 7 (busyEpsilonRequired period))
      , pad 13 (fmt 7 (busyLossOverReserve period))
      , fmt 5 (busyArithmeticBoundFactor period)]
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
          comparablePinned = [period | period <- periods,
            busyArrivalMass period > 1e-12,
            isFinite (busyPinnedBoundOverArrival period)]
          tightestPinned = if null comparablePinned then Nothing else Just
            (minimumBy (comparing busyPinnedBoundOverArrival) comparablePinned)
          containing199 = [period | period <- periods,
            busyStartEvent period <= 199,
            199 < busyRecoveryBeforeEvent period]
          infeasibleRectangles = [period | period <- periods,
            isFinite (busyPrefixEnvelopeSlack period),
            busyPrefixEnvelopeSlack period < 0]
          worstRectangle = if null infeasibleRectangles then Nothing else Just
            (minimumBy (comparing busyPrefixEnvelopeSlack) infeasibleRectangles)
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
         , "  tightest pinned global-prefix/actual-arrival ratio: " ++ maybe "n/a"
             (\period -> fmt 6 (busyPinnedBoundOverArrival period) ++
               "x at start q=" ++ show (busyStartEvent period)) tightestPinned
         , "  constant-excess rectangle infeasible even with exact sampled prefixes: " ++
             show (length infeasibleRectangles) ++ maybe ""
               (\period -> " (worst start q=" ++ show (busyStartEvent period) ++
                 ", slack=" ++ fmt 8 (busyPrefixEnvelopeSlack period) ++ ")")
               worstRectangle
         , "  period containing event 199: " ++ case containing199 of
             period : _ -> show (busyStartEvent period) ++ " -> recovery before " ++
               show (busyRecoveryBeforeEvent period) ++ " (" ++
               show (busyEventCount period) ++ " event states)"
             [] -> "none in completed scan"
         ]
    busyScaleSection =
      let periods = [p | p <- reportBusyPeriods report,
            isFinite (busyEffectiveTheta p)]
          countAbove x = length (filter ((> x) . busyEffectiveTheta) periods)
          countAtMost x = length (filter ((<= x) . busyEffectiveTheta) periods)
          decades = [3 .. 8 :: Int]
          renderDecade k =
            let lo = 10 ^ k
                hi = 10 ^ (k + 1)
                rows = [p | p <- periods, busyIntervalStart p >= lo,
                  busyIntervalStart p < hi]
                values = sort (map busyEffectiveTheta rows)
                danger = if null rows then Nothing else Just
                  (maximumBy (comparing busyLossOverReserve) rows)
            in if null rows then "  1e" ++ show k ++ "..1e" ++ show (k + 1) ++
                "  no completed periods"
              else "  1e" ++ show k ++ "..1e" ++ show (k + 1) ++
                "  count=" ++ show (length rows) ++
                "  min=" ++ fmt 6 (head values) ++
                "  median=" ++ fmt 6 (medianSorted values) ++
                "  dangerous=" ++ maybe "n/a" (fmt 6 . busyEffectiveTheta) danger
      in [ ""
         , "Short-interval scale audit (NumericalEvidence; theta_GM=17/30 is literature context only):"
         , "  theta > 2/3:   " ++ show (countAbove (2 / 3))
         , "  theta > 3/5:   " ++ show (countAbove (3 / 5))
         , "  theta > 17/30: " ++ show (countAbove (17 / 30))
         , "  theta > 1/2:   " ++ show (countAbove (1 / 2))
         , "  theta <= 1/2:  " ++ show (countAtMost (1 / 2))
         , "  logarithmic start bins:"
         ] ++ map renderDecade decades
    busyProfileSection =
      let periods = reportBusyPeriods report
          maxResidual = maximum (0 : map busyProfileMaxResidual periods)
          linearFeasible = [p | p <- periods, busyAnchoredLinearEnvelopeSlack p >= 0]
          linearFailures = [p | p <- periods, busyAnchoredLinearEnvelopeSlack p < 0]
          tightest = if null linearFeasible then Nothing else Just
            (minimumBy (comparing busyAnchoredLinearEnvelopeSlack) linearFeasible)
          worstFailure = if null linearFailures then Nothing else Just
            (minimumBy (comparing busyAnchoredLinearEnvelopeSlack) linearFailures)
          maxFiniteResidual = maximum (0 : map (abs . busyFiniteEventCostResidual) periods)
          maxJumpGap = maximum (0 : map busyJumpAwareMaxGap periods)
          findStart q = case filter ((== q) . busyStartEvent) periods of
            period : _ -> "q=" ++ show q ++
              " exactCost=" ++ fmt 9 (busyFiniteEventExactCost period) ++
              " linearCost=" ++ fmt 9 (busyFiniteEventLinearCost period) ++
              " reserveRemaining=" ++ fmt 9 (busyFiniteEventReserveRemaining period) ++
              " envelopeCost=" ++ fmt 9 (busyEnvelopeCost period) ++
              " envelopeRemaining=" ++ fmt 9 (busyEnvelopeReserveRemaining period) ++
              " localWidthCost=" ++ fmt 9 (busyLocalWidthCost period) ++
              " localWidthFirstFailure=" ++ show (busyLocalWidthFirstFailingCell period) ++
              " oldLinearSlack=" ++ fmt 9 (busyAnchoredLinearEnvelopeSlack period)
            [] -> "q=" ++ show q ++ " not completed in this scan"
          renderCandidate period =
            "q=" ++ show (busyStartEvent period) ++
            " required eps=" ++ fmt 9 (busyChebyshevIncrementSlopeRequired period) ++
            " budget eps=" ++ fmt 9 (busyAnchoredLinearEnvelopeEpsilonBudget period) ++
            " slack=" ++ fmt 9 (busyAnchoredLinearEnvelopeSlack period)
      in [ ""
         , "Chebyshev-error profile audit (NumericalEvidence):"
         , "  exact decomposition max residual: " ++ fmt 12 maxResidual
         , "  U_m(x)=R(m)+epsilon*(x-m) profile-feasible completed periods: " ++
             show (length linearFeasible) ++ "/" ++ show (length periods)
         , "  tightest feasible linear envelope: " ++ maybe "none" renderCandidate tightest
         , "  worst failed linear envelope: " ++ maybe "none" renderCandidate worstFailure
         , "  epsilon required checks R(x)-R(m)<=epsilon*(x-m) at event prefixes; epsilon budget is the largest trapezoidal profile budget."
         , "  finite event exact-service cost residual versus exact loss: " ++ fmt 12 maxFiniteResidual
         , "  jump-aware coarsening maximum R-envelope gap: " ++ fmt 9 maxJumpGap
         , "  jump-aware total-cost feasible periods: " ++ show
             (length (filter ((>= (-1e-10)) . busyEnvelopeReserveRemaining) periods)) ++
             "/" ++ show (length periods)
         , "  local-width total-cost feasible periods: " ++ show
             (length (filter ((>= (-1e-10)) . busyLocalWidthReserveRemaining) periods)) ++
             "/" ++ show (length periods)
         , "  324431 regression: " ++ findStart 324431
         , "  8573249 regression: " ++ findStart 8573249
         , "  jump-aware samples keep R(m) exact and round later R(q_i) upward by 0.001; transformed allowances and their costs are NumericalEvidence, not outward-certified bounds."
         ]
    busyRankingSection =
      let periods = reportBusyPeriods report
          comparable = [p | p <- periods, busyArrivalMass p > 1e-12,
            isFinite (busyEpsilonRequired p),
            isFinite (busyPrefixEpsilonRequired p),
            isFinite (busyArithmeticBoundFactor p)]
          feasible = filter ((>= 0) . busyPrefixEnvelopeSlack) comparable
          infeasible = filter ((< 0) . busyPrefixEnvelopeSlack) comparable
          rank title rows = ["", title,
            "  start -> recover     theta       terminal eps  profile eps   loss/reserve   elementary/required"] ++
            map renderRank (take 20 rows)
          renderRank p = "  " ++ pad 20
            (show (busyStartEvent p) ++ " -> " ++ show (busyRecoveryBeforeEvent p)) ++
            pad 12 (fmt 7 (busyEffectiveTheta p)) ++
            pad 13 (fmt 7 (busyEpsilonRequired p)) ++
            pad 13 (fmt 7 (busyPrefixEpsilonRequired p)) ++
            pad 15 (fmt 7 (busyLossOverReserve p)) ++
            fmt 5 (busyArithmeticBoundFactor p)
      in rank "Top 20 by reserve fraction consumed:"
           (reverse (sortOn busyLossOverReserve comparable)) ++
         rank "Constant-excess rectangle failures (exact sampled prefix already exceeds budget):"
           (sortOn busyPrefixEnvelopeSlack infeasible) ++
         rank "Top 20 feasible periods by smallest prefix-envelope slack:"
           (sortOn busyPrefixEpsilonRequired feasible) ++
         rank "Top 20 by smallest terminal arrival epsilonRequired:"
           (sortOn busyEpsilonRequired comparable) ++
         rank "Top 20 by largest checked-bound/required-bound factor:"
           (reverse (sortOn busyArithmeticBoundFactor comparable)) ++
         rank "Top 20 by smallest effective exponent:"
           (sortOn busyEffectiveTheta comparable)
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
    medianSorted [] = 0 / 0
    medianSorted values
      | odd count = values !! (count `div` 2)
      | otherwise = (values !! (count `div` 2 - 1) +
          values !! (count `div` 2)) / 2
      where count = length values

renderExplorerCsv :: ExplorerReport -> String
renderExplorerCsv report
  | explorerMode (reportOptions report) == BusyMode = unlines $
      ["trust,status,start_event,recovery_before_event,event_count,interval_start,interval_end,interval_width,theta_eff,width_over_sqrt_x,width_over_sqrt_x_log_x,h_over_x_17_30,root_start,root_end,root_width,t_width,starting_discrepancy,most_negative_discrepancy,ending_discrepancy,weighted_loss,psi_start,psi_end,minimum_psi,loss_over_reserve,loss_times_sqrt_start,loss_over_initial_backlog_sq,max_backlog_over_sqrt_start,arrival_mass,service_drift,arrival_over_service,arrival_excess_budget,actual_max_arrival_service_excess,prefix_envelope_slack,required_arrival_upper,arrival_slack,epsilon_required,prefix_epsilon_required,checked_elementary_arrival_upper,arithmetic_bound_factor,arithmetic_bound_excess,pinned_prefix_arrival_upper,pinned_bound_over_arrival,pinned_bound_excess_over_service,pinned_bound_over_required,pinned_bound_excess_over_required"] ++
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
      ,show (busyIntervalStart period), show (busyIntervalEnd period)
      ,show (busyIntervalWidth period), num (busyEffectiveTheta period)
      ,num (busyWidthOverSqrtStart period)
      ,num (busyWidthOverSqrtLogStart period)
      ,num (busyGuthMaynardScaleRatio period)
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
      ,num (busyArrivalOverService period)
      ,num (busyArrivalExcessBudget period)
      ,num (busyActualMaxArrivalServiceExcess period)
      ,num (busyPrefixEnvelopeSlack period)
      ,num (busyRequiredArrivalUpper period)
      ,num (busyArrivalSlack period), num (busyEpsilonRequired period)
      ,num (busyPrefixEpsilonRequired period)
      ,num (busyCheckedElementaryArrivalUpper period)
      ,num (busyArithmeticBoundFactor period)
      ,num (busyArithmeticBoundExcess period)
      ,num (busyPinnedPrefixArrivalUpper period)
      ,num (busyPinnedBoundOverArrival period)
      ,num (busyPinnedExcessOverService period)
      ,num (busyPinnedBoundOverRequired period)
      ,num (busyPinnedBoundExcessOverRequired period)]
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

renderBusyPeriodsJson :: [BusyPeriod] -> String
renderBusyPeriodsJson periods = "[\n" ++
  intercalate ",\n" (map (indent 2 . busyJson) periods) ++ "\n]"

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
  ,jsonField "crude_gap_condition" (jsonBool (dualCrudeGapCondition row))
  ,jsonField "chebyshev_psi" (num (dualChebyshevPsi row))] ++ "}"

chebyshevProfileJson :: ChebyshevProfilePoint -> String
chebyshevProfileJson point = "{" ++ intercalate ", "
  [jsonField "root" (num (profileRoot point))
  ,jsonField "x" (num (profileIntegerX point))
  ,jsonField "chebyshev_error" (num (profileChebyshevError point))
  ,jsonField "boundary_contribution" (num (profileBoundaryContribution point))
  ,jsonField "integral_contribution" (num (profileIntegralContribution point))
  ,jsonField "arch_defect" (num (profileArchDefect point))
  ,jsonField "transformed_excess" (num (profileTransformedExcess point))
  ,jsonField "exact_excess" (num (profileExactExcess point))
  ,jsonField "decomposition_residual" (num (profileDecompositionResidual point))
  ,jsonField "backlog" (num (profileBacklog point))
  ,jsonField "weighted_loss" (num (profileWeightedLoss point))
  ,jsonField "jump_aware_upper" (num (profileJumpAwareUpper point))
  ,jsonField "jump_aware_gap" (num (profileJumpAwareGap point))
  ,jsonField "outgoing_service" (num (profileOutgoingService point))
  ,jsonField "outgoing_exact_cost" (num (profileOutgoingExactCost point))
  ,jsonField "outgoing_linear_cost" (num (profileOutgoingLinearCost point))
  ,jsonField "cumulative_exact_cost" (num (profileCumulativeExactCost point))
  ,jsonField "remaining_reserve" (num (profileRemainingReserve point))
  ,jsonField "event_excess_upper" (num (profileEventExcessUpper point))
  ,jsonField "transformed_gap" (num (profileTransformedGap point))
  ,jsonField "outgoing_envelope_cost" (num (profileOutgoingEnvelopeCost point))
  ,jsonField "outgoing_envelope_linear_cost" (num (profileOutgoingEnvelopeLinearCost point))
  ,jsonField "cumulative_envelope_cost" (num (profileCumulativeEnvelopeCost point))
  ,jsonField "envelope_reserve_remaining" (num (profileEnvelopeReserveRemaining point))
  ,jsonField "local_width_excess_upper" (num (profileLocalWidthExcessUpper point))
  ,jsonField "outgoing_local_width_cost" (num (profileOutgoingLocalWidthCost point))
  ,jsonField "event_log_excess_upper" (num (profileEventLogExcessUpper point))
  ,jsonField "outgoing_event_log_cost" (num (profileOutgoingEventLogCost point))
  ,jsonField "pinned_excess_upper" (num (profilePinnedExcessUpper point))
  ,jsonField "outgoing_pinned_cost" (num (profileOutgoingPinnedCost point))] ++ "}"

busyJson :: BusyPeriod -> String
busyJson = busyJsonWithProfile False

busyJsonWithProfile :: Bool -> BusyPeriod -> String
busyJsonWithProfile fullProfile period = "{" ++ intercalate ", "
  [jsonStringField "trust" "NumericalEvidence"
  ,jsonStringField "status" "candidate"
  ,jsonField "start_event" (show (busyStartEvent period))
  ,jsonField "recovery_before_event" (show (busyRecoveryBeforeEvent period))
  ,jsonField "event_count" (show (busyEventCount period))
  ,jsonField "interval_start" (show (busyIntervalStart period))
  ,jsonField "interval_end" (show (busyIntervalEnd period))
  ,jsonField "interval_width" (show (busyIntervalWidth period))
  ,jsonField "theta_eff" (num (busyEffectiveTheta period))
  ,jsonField "width_over_sqrt_x" (num (busyWidthOverSqrtStart period))
  ,jsonField "width_over_sqrt_x_log_x" (num (busyWidthOverSqrtLogStart period))
  ,jsonField "h_over_x_17_30" (num (busyGuthMaynardScaleRatio period))
  ,jsonField "root_start" (num (busyRootStart period))
  ,jsonField "root_end" (num (busyRootEnd period))
  ,jsonField "recovery_square" (num (busyRootEnd period ^ (2 :: Int)))
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
  ,jsonField "arrival_over_service" (num (busyArrivalOverService period))
  ,jsonField "arrival_excess_budget" (num (busyArrivalExcessBudget period))
  ,jsonField "actual_max_arrival_service_excess"
      (num (busyActualMaxArrivalServiceExcess period))
  ,jsonField "prefix_envelope_slack" (num (busyPrefixEnvelopeSlack period))
  ,jsonField "required_arrival_upper" (num (busyRequiredArrivalUpper period))
  ,jsonField "arrival_slack" (num (busyArrivalSlack period))
  ,jsonField "epsilon_required" (num (busyEpsilonRequired period))
  ,jsonField "prefix_epsilon_required"
      (num (busyPrefixEpsilonRequired period))
  ,jsonField "checked_elementary_arrival_upper"
      (num (busyCheckedElementaryArrivalUpper period))
  ,jsonField "arithmetic_bound_factor" (num (busyArithmeticBoundFactor period))
  ,jsonField "arithmetic_bound_excess" (num (busyArithmeticBoundExcess period))
  ,jsonField "profile_max_residual" (num (busyProfileMaxResidual period))
  ,jsonField "chebyshev_increment_slope_required"
      (num (busyChebyshevIncrementSlopeRequired period))
  ,jsonField "anchored_linear_envelope_epsilon_budget"
      (num (busyAnchoredLinearEnvelopeEpsilonBudget period))
  ,jsonField "anchored_linear_envelope_slack"
      (num (busyAnchoredLinearEnvelopeSlack period))
  ,jsonField "finite_event_exact_cost" (num (busyFiniteEventExactCost period))
  ,jsonField "finite_event_linear_cost" (num (busyFiniteEventLinearCost period))
  ,jsonField "finite_event_cost_residual"
      (num (busyFiniteEventCostResidual period))
  ,jsonField "finite_event_reserve_remaining"
      (num (busyFiniteEventReserveRemaining period))
  ,jsonField "jump_aware_max_gap" (num (busyJumpAwareMaxGap period))
  ,jsonField "envelope_cost" (num (busyEnvelopeCost period))
  ,jsonField "envelope_linear_cost" (num (busyEnvelopeLinearCost period))
  ,jsonField "envelope_cost_gap" (num (busyEnvelopeCostGap period))
  ,jsonField "envelope_reserve_remaining" (num (busyEnvelopeReserveRemaining period))
  ,jsonField "envelope_max_excess_gap" (num (busyEnvelopeMaxExcessGap period))
  ,jsonField "envelope_first_failing_cell" (maybe "null" show (busyEnvelopeFirstFailingCell period))
  ,jsonField "local_width_cost" (num (busyLocalWidthCost period))
  ,jsonField "local_width_reserve_remaining" (num (busyLocalWidthReserveRemaining period))
  ,jsonField "local_width_first_failing_cell" (maybe "null" show (busyLocalWidthFirstFailingCell period))
  ,jsonField "event_log_cost" (num (busyEventLogCost period))
  ,jsonField "prime_power_surcharge" (num (busyPrimePowerSurcharge period))
  ,jsonField "surcharge_identity_residual" (num (busySurchargeIdentityResidual period))
  ,jsonField "pinned_anchored_cost" (num (busyPinnedAnchoredCost period))
  ,jsonField "pinned_anchored_first_failing_cell"
      (maybe "null" show (busyPinnedAnchoredFirstFailingCell period))
  ,jsonField "corrected_exact_service_cost"
      (num (busyEventLogCost period - busyPrimePowerSurcharge period))
  ,jsonField "event_log_reserve_remaining" (num (busyEventLogReserveRemaining period))
  ,jsonField "event_log_first_failing_cell" (maybe "null" show (busyEventLogFirstFailingCell period))
  ,jsonStringField "failure_interpretation"
      "A negative envelope reserve means the chosen sample bounds or reserve do not meet the sufficient total-cost inequality; all evaluations use Double, not proved outward bounds."
  ,jsonField "pinned_prefix_arrival_upper"
      (num (busyPinnedPrefixArrivalUpper period))
  ,jsonField "pinned_bound_over_arrival"
      (num (busyPinnedBoundOverArrival period))
  ,jsonField "pinned_bound_excess_over_service"
      (num (busyPinnedExcessOverService period))
  ,jsonField "pinned_bound_over_required"
      (num (busyPinnedBoundOverRequired period))
  ,jsonField "pinned_bound_excess_over_required"
      (num (busyPinnedBoundExcessOverRequired period))
  ,jsonField "chebyshev_profile" ("[" ++ intercalate ","
      (map chebyshevProfileJson (if fullProfile then busyChebyshevProfile period
        else sampleProfile 160 (busyChebyshevProfile period))) ++ "]")] ++ "}"
  where
    sampleProfile limit points
      | length points <= limit = points
      | otherwise =
          let stride = max 1 (length points `div` (limit - 1))
              sampled = [point | (index, point) <- zip [0 :: Int ..] points,
                index `mod` stride == 0]
              finalPoint = case reverse points of
                point : _ -> Just point
                [] -> Nothing
          in case (reverse sampled, finalPoint) of
            (point : _, Just final) | point == final -> sampled
            (_, Just final) -> sampled ++ [final]
            (_, Nothing) -> sampled

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
