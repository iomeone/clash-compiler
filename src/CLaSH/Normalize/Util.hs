{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns  #-}
module CLaSH.Normalize.Util where

import Control.Lens                ((.=),(%=))
import qualified Control.Lens      as Lens
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.List as      List
import Unbound.LocallyNameless     (Fresh, aeq,embed,unbind)

import CLaSH.Core.DataCon (dataConInstArgTys)
import CLaSH.Core.Term    (Term(..),TmName)
import CLaSH.Core.TyCon   (TyCon(..),tyConDataCons)
import CLaSH.Core.Type    (Type(..),TypeView(..),tyView,isFunTy)
import CLaSH.Core.Util    (Gamma,collectArgs)
import CLaSH.Core.Var     (Var(..),Id)
import CLaSH.Netlist.Util (representableType)
import CLaSH.Normalize.Types
import CLaSH.Rewrite.Types
import CLaSH.Rewrite.Util

nonRep ::
  Type
  -> Bool
nonRep = not . representableType

isBoxTy ::
  Type
  -> Bool
isBoxTy = isBoxTy' []

isBoxTy' ::
  [Type]
  -> Type
  -> Bool
isBoxTy' ts ty@(tyView -> TyConApp tc tys)
  | ty `notElem` ts = any (\t -> isBoxTy' (ty:ts) t || isFunTy t)
                          (conArgs tc tys)
  | otherwise       = False
isBoxTy' _ _        = False

isPolyFunTy ::
  Fresh m
  => Type
  -> m Bool
isPolyFunTy (tyView -> FunTy _ _) = return True
isPolyFunTy (ForAllTy tvT)        = unbind tvT >>= (isPolyFunTy . snd)
isPolyFunTy _                     = return False

conArgs :: TyCon -> [Type] -> [Type]
conArgs tc tys = bigUnionTys $ map (flip dataConInstArgTys tys)
               $ tyConDataCons tc
  where
    bigUnionTys :: [[Type]] -> [Type]
    bigUnionTys []   = []
    bigUnionTys tyss = foldl1 (List.unionBy aeq) tyss

alreadyInlined ::
  TmName
  -> NormalizeMonad Bool
alreadyInlined f = do
  cf <- Lens.use curFun
  inlinedHM <- Lens.use inlined
  case HashMap.lookup cf inlinedHM of
    Nothing -> do
      return False
    Just inlined' -> do
      if (f `elem` inlined')
        then return True
        else do
          return False

commitNewInlined :: NormRewrite
commitNewInlined _ e = R $ liftR $ do
  cf <- Lens.use curFun
  nI <- Lens.use newInlined
  inlinedHM <- Lens.use inlined
  case HashMap.lookup cf inlinedHM of
    Nothing -> inlined %= (HashMap.insert cf nI)
    Just _  -> inlined %= (HashMap.adjust (`List.union` nI) cf)
  newInlined .= []
  return e

fvs2bvs ::
  Gamma
  -> [TmName]
  -> [Id]
fvs2bvs gamma = map (\n -> Id n (embed $ gamma HashMap.! n))

isSimple ::
  Term
  -> Bool
isSimple (Literal _) = True
isSimple (Data _)    = True
isSimple e@(App _ _)
  | (Data _, args) <- collectArgs e
  = all (either isSimple (const True)) args
  | (Prim _, args) <- collectArgs e
  = all (either isSimple (const True)) args
isSimple _ = False
