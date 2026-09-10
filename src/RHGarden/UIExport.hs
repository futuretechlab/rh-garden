module RHGarden.UIExport
  ( writeUiExport
  , gardenJson
  , frontiersJson
  , statusJson
  ) where

import Control.Exception (IOException, try)
import Data.Char (ord)
import Data.List (intercalate, isInfixOf, nub)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import System.Process (readProcess)

import RHGarden.Core
import RHGarden.Explorer.Suzuki
import RHGarden.Registry
import RHGarden.Representation

writeUiExport :: FilePath -> IO ()
writeUiExport projectRoot = do
  let outputDir = projectRoot </> "ui" </> "public" </> "data"
  createDirectoryIfMissing True outputDir
  headResult <- try (readProcess "git" ["rev-parse", "HEAD"] "") :: IO (Either IOException String)
  let headCommit = either (const "unavailable") (takeWhile (`notElem` "\r\n")) headResult
      scanOptions = defaultExplorerOptions
        { explorerOmegas = [0, 0.125, 0.5]
        , explorerTMax = 7
        , explorerSamples = 701
        , explorerPrimeCells = True
        }
      busyOptions = defaultExplorerOptions
        { explorerMode = BusyMode
        , explorerOmegas = [0]
        , explorerTMax = log 25000
        , explorerSamples = 401
        , explorerPrimeCells = True
        }
  scanReport <- requireReport "field scan" scanOptions
  busyReport <- requireReport "busy-period scan" busyOptions
  writeFile (outputDir </> "garden.json") gardenJson
  writeFile (outputDir </> "frontiers.json") frontiersJson
  writeFile (outputDir </> "status.json") (statusJson headCommit)
  writeFile (outputDir </> "explorer-summary.json")
    (explorerSummaryJson scanReport busyReport)
  putStrLn $ "RH Garden Navigator data exported to " ++ outputDir
  putStrLn $ "Snapshot commit: " ++ headCommit
  where
    requireReport label options = case exploreSuzuki options of
      Left err -> ioError (userError (label ++ " failed: " ++ err))
      Right report -> pure report

gardenJson :: String
gardenJson = unlines
  [ "{"
  , "  \"schema_version\": 1,"
  , "  \"generated_by\": \"rh-garden ui-export\","
  , "  \"nodes\": ["
  , intercalate ",\n" (map (indent 4 . criterionNodeJson) allCriteria ++
      map (indent 4 . representationNodeJson) allRepresentations)
  , "  ],"
  , "  \"edges\": ["
  , intercalate ",\n" (map (indent 4 . criterionEdgeJson) certifiedGraph ++
      map (indent 4 . representationEdgeJson) representationExplorationGraph)
  , "  ]"
  , "}"
  ]

frontiersJson :: String
frontiersJson = unlines
  [ "{"
  , "  \"schema_version\": 1,"
  , "  \"frontiers\": ["
  , indent 4 $ object
      [ stringField "id" "multi-event-arrival-service"
      , stringField "title" "Multi-event weighted-Mangoldt arrival/service control"
      , stringField "category" "arithmetic"
      , stringField "status" "open"
      , stringField "trust" "Open"
      , stringField "known_chain" "Exact arrivals -> exact Chebyshev Abel identity -> exact discrepancy balance -> weighted backlog loss"
      , stringField "exact_blocker" "For each completed negative excursion [a,b], bound the local mass sum_{a^2<n<=b^2} Lambda(n)/sqrt(n) sharply enough that integral_a^b 2 max(-D(u),0)/u du <= PsiRoot(a)."
      , stringField "current_bound" "Pinned global prefix estimates discard the lower endpoint and are structurally too coarse for short root intervals."
      , arrayField "source_modules"
          ["formal/RHGarden/SuzukiBusyPeriods.lean",
           "formal/RHGarden/SuzukiRootDiscrepancy.lean",
           "src/RHGarden/Explorer/Suzuki.hs"]
      , arrayField "candidate_approaches"
          ["short-interval Chebyshev psi bounds",
           "exact-prefix plus theorem-backed tail",
           "multi-event reserve/loss certificates"]
      ]
  , ","
  , indent 4 $ object
      [ stringField "id" "initial-suzuki-interval"
      , stringField "title" "Close the remaining initial Suzuki interval"
      , stringField "category" "analytic"
      , stringField "status" "open"
      , stringField "trust" "Open"
      , stringField "known_chain" "Local punctured positivity and complete cell-2 positivity are LeanChecked"
      , stringField "exact_blocker" "Certify nonnegativity from the existing local endpoint through log 2."
      , stringField "current_bound" "Finite local result only."
      , arrayField "source_modules" ["formal/RHGarden/SuzukiLocalPositive.lean"]
      , arrayField "candidate_approaches" ["archimedean prime-free bounds"]
      ]
  , "  ]"
  , "}"
  ]

statusJson :: String -> String
statusJson headCommit = unlines
  [ "{"
  , "  \"schema_version\": 1,"
  , "  \"snapshot_commit\": " ++ jsonString headCommit ++ ","
  , "  \"snapshot_note\": \"Refresh with cabal run rh-garden -- ui-export; validation fields are not inferred by the frontend.\","
  , "  \"formal_build\": \"not_checked_by_export\","
  , "  \"cabal_test\": \"not_checked_by_export\","
  , "  \"submission\": \"NO PROOF OF RH IS CLAIMED.\","
  , "  \"submission_ready\": false,"
  , "  \"counts\": {"
  , "    \"criteria\": " ++ show (length allCriteria) ++ ","
  , "    \"representations\": " ++ show (length allRepresentations) ++ ","
  , "    \"lean_checked_edges\": " ++ show leanEdges ++ ","
  , "    \"literature_edges\": " ++ show literatureEdges ++ ","
  , "    \"numerical_edges\": " ++ show numericalEdges ++ ","
  , "    \"open_edges\": " ++ show conjecturalEdges
  , "  }"
  , "}"
  ]
  where
    trusts = map rrTrust certifiedGraph ++ map rreTrust representationExplorationGraph
    leanEdges = count (== leanCheckedTrust) trusts
    literatureEdges = count (== literatureCertifiedTrust) trusts
    numericalEdges = count (== numericalEvidenceTrust) trusts
    conjecturalEdges = count (== conjecturalTrust) trusts

explorerSummaryJson :: ExplorerReport -> ExplorerReport -> String
explorerSummaryJson scanReport busyReport = unlines
  [ "{"
  , "  \"schema_version\": 1,"
  , "  \"trust\": \"NumericalEvidence\","
  , "  \"warning\": \"Numerical positivity over a finite range is not sufficient evidence for RH.\","
  , "  \"field_samples\": ["
  , intercalate ",\n" (map (indent 4 . fieldSampleJson) fieldSamples)
  , "  ],"
  , "  \"scan\": " ++ indentAfter 2 (renderExplorerJson scanReport) ++ ","
  , "  \"busy\": " ++ indentAfter 2 (renderExplorerJson busyReport)
  , "}"
  ]
  where
    omegas = [0, 0.125, 0.5]
    ts = [fromIntegral i * 7 / 80 | i <- [0 .. 80 :: Int]]
    fieldSamples = [(omega, t, psiShiftedNumeric omega t) | omega <- omegas, t <- ts]

fieldSampleJson :: (Double, Double, Double) -> String
fieldSampleJson (omega, t, value) = object
  [ numberField "omega" omega
  , numberField "t" t
  , numberField "psi" value
  , stringField "trust" "NumericalEvidence"
  ]

allCriteria :: [Criterion]
allCriteria = [minBound .. maxBound]

allRepresentations :: [Representation]
allRepresentations = [minBound .. maxBound]

criterionNodeJson :: Criterion -> String
criterionNodeJson criterion = object
  [ stringField "id" (criterionId criterion)
  , stringField "display_name" (criterionLabel criterion)
  , stringField "district" (districtFor (show criterion))
  , stringField "description" (criterionLabel criterion)
  , stringField "trust" "Open"
  , stringField "kind" "proposition"
  , stringField "status" "open"
  , boolField "rh_equivalent" (mutuallyReachable criterion RH)
  , arrayField "theorem_names" []
  , arrayField "source_files" ["src/RHGarden/Core.hs", "src/RHGarden/Registry.hs"]
  ]

representationNodeJson :: Representation -> String
representationNodeJson representation = object
  [ stringField "id" (representationId representation)
  , stringField "display_name" (representationLabel representation)
  , stringField "district" (districtFor (show representation))
  , stringField "description" (representationLabel representation)
  , stringField "trust" (show (representationTrust representation))
  , stringField "kind" "representation"
  , stringField "status" (if representationTrust representation == conjecturalTrust then "open" else "defined")
  , boolField "rh_equivalent" (representation == SuzukiPsiZeroSide || representation == SuzukiRootPrefixArea)
  , arrayField "theorem_names" (representationTheorems representation)
  , arrayField "source_files" (sourceFiles representation)
  ]

criterionEdgeJson :: RuntimeReduction -> String
criterionEdgeJson edge = object
  [ stringField "id" ("criterion-edge:" ++ rrName edge)
  , stringField "source" (criterionId (rrFrom edge))
  , stringField "target" (criterionId (rrTo edge))
  , stringField "relation_type" (show (rrRelation edge))
  , stringField "trust" (show (rrTrust edge))
  , stringField "theorem_name" (refShort (rrReference edge))
  , stringField "provenance" (refCitation (rrReference edge))
  , stringField "information_loss" "proposition reduction"
  , stringField "description" (rrNote edge)
  ]

representationEdgeJson :: RuntimeRepresentationEdge -> String
representationEdgeJson edge = object
  [ stringField "id" ("representation-edge:" ++ rreName edge)
  , stringField "source" (representationId (rreFrom edge))
  , stringField "target" (representationId (rreTo edge))
  , stringField "relation_type" (show (rreKind edge))
  , stringField "trust" (show (rreTrust edge))
  , stringField "theorem_name" (refShort (rreReference edge))
  , stringField "provenance" (refCitation (rreReference edge))
  , stringField "information_loss" (show (rreReconstruction edge))
  , stringField "description" (rreTransform edge)
  ]

criterionId :: Criterion -> String
criterionId criterion = "criterion:" ++ show criterion

representationId :: Representation -> String
representationId representation = "representation:" ++ show representation

mutuallyReachable :: Criterion -> Criterion -> Bool
mutuallyReachable a b = reachable a b && reachable b a
  where
    reachable start target = go [] [start]
      where
        go _ [] = False
        go seen (x : xs)
          | x == target = True
          | x `elem` seen = go seen xs
          | otherwise = go (x : seen)
              ([rrTo edge | edge <- certifiedGraph,
                rrFrom edge == x, rrTrust edge /= conjecturalTrust] ++ xs)

representationTrust :: Representation -> Trust
representationTrust representation
  | representation `elem` numericalRepresentations = numericalEvidenceTrust
  | representation == RHGardenNavigator = exactExecutableTrust
  | representation == GardenRegistry = exactExecutableTrust
  | representation == FormalStatus = exactExecutableTrust
  | any ((== leanCheckedTrust) . rreTrust) incident = leanCheckedTrust
  | any ((== literatureCertifiedTrust) . rreTrust) incident = literatureCertifiedTrust
  | any ((== conjecturalTrust) . rreTrust) incident = conjecturalTrust
  | otherwise = exactExecutableTrust
  where
    incident = [edge | edge <- representationExplorationGraph,
      rreFrom edge == representation || rreTo edge == representation]

numericalRepresentations :: [Representation]
numericalRepresentations =
  [ SuzukiPositivityExplorer, SuzukiMinimumBranches, SuzukiEnvelopeCrossings
  , CandidateCellCertificate, CandidateTailCertificate, CandidateOperatorIdentity
  ]

representationTheorems :: Representation -> [String]
representationTheorems representation = nub
  [refShort (rreReference edge) | edge <- representationExplorationGraph,
    (rreFrom edge == representation || rreTo edge == representation),
    rreTrust edge == leanCheckedTrust]

sourceFiles :: Representation -> [String]
sourceFiles representation
  | representation `elem` [SuzukiRootSlopeDiscrepancy, SuzukiRootPrefixArea,
      SuzukiBusyPeriodLoss] = ["formal/RHGarden/SuzukiRootDiscrepancy.lean"]
  | representation == SuzukiBusyPeriodCertificates =
      ["formal/RHGarden/SuzukiBusyPeriods.lean"]
  | representation == SuzukiPositivityExplorer =
      ["src/RHGarden/Explorer/Suzuki.hs"]
  | representation == RHGardenNavigator = ["ui/src/App.tsx", "src/RHGarden/UIExport.hs"]
  | otherwise = ["src/RHGarden/Registry.hs"]

districtFor :: String -> String
districtFor name
  | "Suzuki" `isInfixOf` name || "Screw" `isInfixOf` name = "Suzuki"
  | "Mangoldt" `isInfixOf` name || "Lagarias" `isInfixOf` name = "Prime arithmetic"
  | "Nevanlinna" `isInfixOf` name = "Nevanlinna"
  | "Weil" `isInfixOf` name = "Weil"
  | "Li" `isInfixOf` name || "Mobius" `isInfixOf` name = "Li"
  | "Xi" `isInfixOf` name || "Zeta" `isInfixOf` name = "Xi"
  | "Hadamard" `isInfixOf` name || "Canonical" `isInfixOf` name ||
      "Divisor" `isInfixOf` name = "Hadamard"
  | "Explorer" `isInfixOf` name || "Navigator" `isInfixOf` name ||
      "Registry" `isInfixOf` name || "Status" `isInfixOf` name = "Explorer"
  | otherwise = "Open frontiers"

count :: (a -> Bool) -> [a] -> Int
count predicate = length . filter predicate

object :: [String] -> String
object fields = "{" ++ intercalate ", " fields ++ "}"

stringField :: String -> String -> String
stringField key value = jsonString key ++ ": " ++ jsonString value

numberField :: String -> Double -> String
numberField key value = jsonString key ++ ": " ++ finiteNumber value

boolField :: String -> Bool -> String
boolField key value = jsonString key ++ ": " ++ if value then "true" else "false"

arrayField :: String -> [String] -> String
arrayField key values = jsonString key ++ ": [" ++
  intercalate ", " (map jsonString values) ++ "]"

finiteNumber :: Double -> String
finiteNumber value
  | isNaN value || isInfinite value = "null"
  | otherwise = show value

jsonString :: String -> String
jsonString text = '"' : concatMap escape text ++ "\""
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\r' = "\\r"
    escape '\t' = "\\t"
    escape char
      | ord char < 32 = "?"
      | otherwise = [char]

indent :: Int -> String -> String
indent spaces = unlines . map padLine . lines
  where
    padLine "" = ""
    padLine line = replicate spaces ' ' ++ line

indentAfter :: Int -> String -> String
indentAfter spaces source = case lines source of
  [] -> "{}"
  firstLine : rest -> firstLine ++ "\n" ++
    intercalate "\n" (map padLine rest)
  where
    padLine "" = ""
    padLine line = replicate spaces ' ' ++ line
