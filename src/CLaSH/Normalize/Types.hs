module CLaSH.Normalize.Types where

import Control.Monad.State (State)
import Data.HashMap.Lazy (HashMap)
import Data.Map          (Map)

import CLaSH.Core.Term (Term,TmName)
import CLaSH.Core.Type (Type)
import CLaSH.Rewrite.Types (Rewrite,RewriteSession)
import CLaSH.Util

data NormalizeState
  = NormalizeState
  { _normalized      :: HashMap TmName Term
  , _specialisations :: Map (TmName,Int,Either Term Type) (TmName,Type)
  , _inlined         :: HashMap TmName [TmName]
  , _newInlined      :: [TmName]
  , _curFun          :: TmName
  }

makeLenses ''NormalizeState

type NormalizeMonad = State NormalizeState

type NormalizeSession = RewriteSession NormalizeMonad

type NormRewrite = Rewrite NormalizeMonad
