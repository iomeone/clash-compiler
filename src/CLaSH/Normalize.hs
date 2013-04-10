module CLaSH.Normalize where

import Control.Concurrent.Supply        (Supply)
import           Control.Lens           ((.=))
import qualified Control.Lens        as Lens
import qualified Control.Monad.State as State
import Data.HashMap.Lazy                (HashMap)
import qualified Data.HashMap.Lazy   as HashMap
import qualified Data.Map            as Map

import CLaSH.Core.FreeVars      (termFreeIds)
import CLaSH.Core.Pretty        (showDoc)
import CLaSH.Core.Term          (TmName,Term)
import CLaSH.Core.Type          (Type)
import CLaSH.Normalize.Strategy
import CLaSH.Normalize.Types
import CLaSH.Rewrite.Types      (DebugLevel(..),RewriteState(..),dbgLevel,
  bindings,classOps,dictFuns)
import CLaSH.Rewrite.Util       (liftRS,runRewrite,runRewriteSession)
import CLaSH.Util

runNormalization ::
  DebugLevel
  -> Supply
  -> HashMap TmName (Type,Term)
  -> HashMap TmName (Type,[Term])
  -> HashMap TmName (Type,Int)
  -> NormalizeSession a
  -> a
runNormalization lvl supply globals dfunMap clsOpMap
  = flip State.evalState normState
  . runRewriteSession lvl rwState
  where
    rwState   = RewriteState 0 globals dfunMap clsOpMap supply
    normState = NormalizeState
                  HashMap.empty
                  Map.empty
                  HashMap.empty
                  []
                  (error "Report as bug: no curFun")

normalize ::
  [TmName]
  -> NormalizeSession [(TmName,(Type,Term))]
normalize (bndr:bndrs) = do
  let bndrS = showDoc bndr
  exprM <- fmap (HashMap.lookup bndr) $ Lens.use bindings
  case exprM of
    Just (ty,expr) -> do
      liftRS $ curFun .= bndr
      normalizedExpr <- makeCachedT3 bndr normalized $
                         normalizeExpr bndrS expr
      usedBndrs <- usedGlobalBndrs normalizedExpr
      case (bndr `elem` usedBndrs) of
        True -> error $ $(curLoc) ++ "Expr belonging to bndr: " ++ bndrS ++ " remains recursive after normalization."
        False -> do
          prevNorm <- fmap (HashMap.keys) $ liftRS $ Lens.use normalized
          let toNormalize = filter (`notElem` prevNorm) usedBndrs
          normalizedOthers <- normalize (toNormalize ++ bndrs)
          return ((bndr,(ty,normalizedExpr)):normalizedOthers)
    Nothing -> error $ $(curLoc) ++ "Expr belonging to bndr: " ++ bndrS ++ " not found"

normalize [] = return []

normalizeExpr ::
  String
  -> Term
  -> NormalizeSession Term
normalizeExpr bndrS expr = do
  lvl <- Lens.view dbgLevel
  let before = showDoc expr
  let expr' = traceIf (lvl >= DebugFinal)
                (bndrS ++ " before normalization:\n\n" ++ before ++ "\n")
                expr
  rewritten <- runRewrite "normalization" normalization expr'
  let after = showDoc rewritten
  traceIf (lvl >= DebugFinal)
    (bndrS ++ " after normalization:\n\n" ++ after ++ "\n") $
    return rewritten

usedGlobalBndrs ::
  Term
  -> NormalizeSession [TmName]
usedGlobalBndrs tm = do
  clsOps <- fmap (HashMap.keys) $ Lens.use classOps
  dfuns  <- fmap (HashMap.keys) $ Lens.use dictFuns
  return . filter (`notElem` (clsOps ++ dfuns)) $ termFreeIds tm
