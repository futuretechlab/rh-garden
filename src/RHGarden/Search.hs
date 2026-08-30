module RHGarden.Search
  ( SearchMode(..)
  , Route(..)
  , shortestRoute
  , renderRoute
  , RepresentationRoute(..)
  , shortestRepresentationRoute
  , renderRepresentationRoute
  ) where

import Data.List (minimumBy)
import qualified Data.Map.Strict as M
import Data.Ord (comparing)

import RHGarden.Core
import RHGarden.Representation

data SearchMode = KernelMode | LiteratureMode | ExplorationMode
  deriving (Eq, Show)

data Route = Route
  { routeCost  :: Int
  , routeSteps :: [RuntimeReduction]
  } deriving (Eq, Show)

allowed :: SearchMode -> RuntimeReduction -> Bool
allowed KernelMode = admissibleInKernelMode
allowed LiteratureMode = admissibleInLiteratureMode
allowed ExplorationMode = const True

allowedTrust :: SearchMode -> Trust -> Bool
allowedTrust KernelMode trust = trust == leanCheckedTrust
allowedTrust LiteratureMode trust = trust /= conjecturalTrust
allowedTrust ExplorationMode _ = True

-- | Dijkstra-like search.  The graph is intentionally tiny in v0.1, so a
-- sorted-list frontier is clearer than introducing another package dependency.
shortestRoute
  :: SearchMode
  -> [RuntimeReduction]
  -> Criterion
  -> Criterion
  -> Maybe Route
shortestRoute mode graph start goal = go M.empty [(0, start, [])]
  where
    usable = filter (allowed mode) graph

    go _ [] = Nothing
    go best frontier =
      let current@(cost, node, revSteps) = minimumBy (comparing first3) frontier
          rest = removeOne current frontier
      in case M.lookup node best of
           Just old | old <= cost -> go best rest
           _
             | node == goal -> Just (Route cost (reverse revSteps))
             | otherwise ->
                 let best' = M.insert node cost best
                     next =
                       [ (cost + rrCost e, rrTo e, e : revSteps)
                       | e <- usable
                       , rrFrom e == node
                       ]
                 in go best' (next ++ rest)

    first3 (c, _, _) = c

removeOne :: Eq a => a -> [a] -> [a]
removeOne _ [] = []
removeOne x (y:ys)
  | x == y = ys
  | otherwise = y : removeOne x ys

renderRoute :: Criterion -> Route -> String
renderRoute start r =
  unlines $
    [ "start: " ++ criterionLabel start
    , "total route cost: " ++ show (routeCost r)
    ] ++ concatMap renderStep (zip [(1 :: Int)..] (routeSteps r))
  where
    renderStep (i, e) =
      [ "  " ++ show i ++ ". " ++ criterionLabel (rrFrom e)
      , "       --[" ++ rrName e ++ "; " ++ show (rrRelation e) ++
        "; " ++ show (rrTrust e) ++ "]-->"
      , "     " ++ criterionLabel (rrTo e)
      , "     ref: " ++ refShort (rrReference e)
      , "     note: " ++ rrNote e
      , "     preservation: " ++ maybe "none registered" show (rrPreservation e)
      , "     citation: " ++ refCitation (rrReference e)
      ]

data RepresentationRoute = RepresentationRoute
  { representationRouteCost :: Int
  , representationRouteSteps :: [RuntimeRepresentationEdge]
  } deriving (Eq, Show)

shortestRepresentationRoute
  :: SearchMode -> [RuntimeRepresentationEdge] -> Representation
  -> Representation -> Maybe RepresentationRoute
shortestRepresentationRoute mode graph start goal = go M.empty [(0, start, [])]
  where
    usable = filter (allowedTrust mode . rreTrust) graph

    go _ [] = Nothing
    go best frontier =
      let current@(cost, node, reversedSteps) = minimumBy (comparing routeTupleCost) frontier
          rest = removeOne current frontier
      in case M.lookup node best of
           Just old | old <= cost -> go best rest
           _ | node == goal -> Just (RepresentationRoute cost (reverse reversedSteps))
             | otherwise ->
                 let best' = M.insert node cost best
                     next =
                       [ (cost + rreCost edge, rreTo edge, edge : reversedSteps)
                       | edge <- usable, rreFrom edge == node
                       ]
                 in go best' (next ++ rest)

    routeTupleCost (cost, _, _) = cost

renderRepresentationRoute :: Representation -> RepresentationRoute -> String
renderRepresentationRoute start route = unlines $
  [ "start representation: " ++ representationLabel start
  , "total route cost: " ++ show (representationRouteCost route)
  ] ++ concatMap renderStep (zip [1 :: Int ..] (representationRouteSteps route))
  where
    renderStep (index, edge) =
      [ "  " ++ show index ++ ". " ++ representationLabel (rreFrom edge)
      , "       --[" ++ rreName edge ++ "; " ++ show (rreKind edge) ++ "; " ++ show (rreTrust edge) ++ "]-->"
      , "     " ++ representationLabel (rreTo edge)
      , "     transform: " ++ rreTransform edge
      , "     reconstruction: " ++ show (rreReconstruction edge)
      , "     preservation: " ++ maybe "none registered" show (rrePropertyTransport edge)
      , "     ref: " ++ refShort (rreReference edge)
      ]
