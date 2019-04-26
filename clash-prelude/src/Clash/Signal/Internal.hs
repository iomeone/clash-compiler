{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2017-2019, Myrtle Software Ltd
                  2017,      Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}

{-# LANGUAGE Unsafe #-}

-- See: https://github.com/clash-lang/clash-compiler/commit/721fcfa9198925661cd836668705f817bddaae3c
-- as to why we need this.
{-# OPTIONS_GHC -fno-cpr-anal #-}

{-# OPTIONS_HADDOCK show-extensions not-home #-}

module Clash.Signal.Internal
  ( -- * Datatypes
    Signal(..)
  , head#
  , tail#
    -- * Domains
  , KnownDomain(..)
  , ActiveEdge(..)
  , SActiveEdge(..)
  , InitBehavior(..)
  , SInitBehavior(..)
  , ResetKind(..)
  , SResetKind(..)
  , Domain(..)
  , SDomain(..)
  , System
  , XilinxSystem
  , IntelSystem
    -- * Clocks
  , Clock (..)
  , ClockKind (..)
  , clockPeriod
  , clockEnable
  , toEnabledClock
    -- ** Clock gating
    -- * Resets
  , ResetPolarity(..)
  , Reset(..)
  , fromSyncReset
  , syncPolarity
  , toHighPolarity
  , toLowPolarity
  , unsafeFromReset
  , unsafeToActiveHighReset
  , unsafeToActiveLowReset
    -- * Basic circuits
  , delay#
  , register#
  , mux
    -- * Simulation and testbench functions
  , clockGen
  , tbClockGen
  , resetGen
    -- * Boolean connectives
  , (.&&.), (.||.)
    -- * Simulation functions (not synthesizable)
  , simulate
    -- ** lazy version
  , simulate_lazy
    -- * List \<-\> Signal conversion (not synthesizable)
  , sample
  , sampleN
  , fromList
    -- ** lazy versions
  , sample_lazy
  , sampleN_lazy
  , fromList_lazy
    -- * QuickCheck combinators
  , testFor
    -- * Type classes
    -- ** 'Eq'-like
  , (.==.), (./=.)
    -- ** 'Ord'-like
  , (.<.), (.<=.), (.>=.), (.>.)
    -- ** 'Functor'
  , mapSignal#
    -- ** 'Applicative'
  , signal#
  , appSignal#
    -- ** 'Foldable'
  , foldr#
    -- ** 'Traversable'
  , traverse#
  -- * EXTREMELY EXPERIMENTAL
  , joinSignal#
  )
where

import Type.Reflection            (Typeable)
import Control.Applicative        (liftA2, liftA3)
import Control.DeepSeq            (NFData)
import Data.Default.Class         (Default (..))
import GHC.Generics               (Generic)
import GHC.TypeLits               (KnownSymbol, Nat, Symbol)
import Language.Haskell.TH.Syntax (Lift (..))
import Test.QuickCheck            (Arbitrary (..), CoArbitrary(..), Property,
                                   property)

import Clash.Promoted.Nat         (SNat (..), snatToNum)
import Clash.Promoted.Symbol      (SSymbol (..))
import Clash.XException           (Undefined, errorX, deepseqX, defaultSeqX)

{- $setup
>>> :set -XDataKinds
>>> :set -XMagicHash
>>> :set -XTypeApplications
>>> import Clash.Promoted.Nat
>>> import Clash.XException
>>> type System = "System"
>>> let systemClockGen = clockGen @System
>>> let systemResetGen = resetGen @System
>>> import Clash.Explicit.Signal (register)
>>> let registerS = register
>>> let registerA = register
-}

-- * Signal
data ActiveEdge
  = Rising
  | Falling

data SActiveEdge (edge :: ActiveEdge) where
  SRising  :: SActiveEdge 'Rising
  SFalling :: SActiveEdge 'Falling

data ResetKind
  = Asynchronous
  | Synchronous

data SResetKind (resetKind :: ResetKind) where
  SAsynchronous :: SResetKind 'Asynchronous
  SSynchronous  :: SResetKind 'Synchronous

data InitBehavior
  = Undefined
  | Defined

data SInitBehavior (init :: InitBehavior) where
  SUndefined :: SInitBehavior 'Undefined
  SDefined :: SInitBehavior 'Defined

-- | A domain with a name (@Symbol@) and a clock period (@Nat@) in /ps/
data Domain
  = Domain
  { _tag :: Symbol
  -- ^ Domain name
  , _period :: Nat
  -- ^ Period of clock in /ps/
  , _edge :: ActiveEdge
  -- ^ Determines which edge of the clock registers are sensitive to
  , _reset :: ResetKind
  -- ^ Determines how components with reset lines respond to changes
  , _init :: InitBehavior
  -- ^ Determines the initial (or "power up") value of various components
  }
  deriving (Typeable)

-- | GADT version of 'Domain'
data SDomain (tag :: Symbol) (conf :: Domain) where
  SDomain
    :: SSymbol tag
    -- Domain name ^
    -> SNat period
    -- Period of clock in /ps/ ^
    -> SActiveEdge edge
    -- Determines which edge of the clock registers are sensitive to ^
    -> SResetKind reset
    -- Determines how components with reset lines respond to changes ^
    -> SInitBehavior init
    -- Determines the initial (or "power up") value of various components ^
    -> SDomain tag ('Domain tag period edge reset init)

-- | TODO: docs
class KnownSymbol tag => KnownDomain (tag :: Symbol) (conf :: Domain) | tag -> conf where
  knownDomain :: SSymbol tag -> SDomain tag conf

-- | A /clock/ (and /reset/) tag with clocks running at 100 MHz
instance KnownDomain System ('Domain System 10000 'Rising 'Asynchronous 'Defined) where
  knownDomain tag = SDomain tag SNat SRising SAsynchronous SDefined

-- | System instance with defaults set for Xilinx FPGAs
instance KnownDomain XilinxSystem ('Domain XilinxSystem 10000 'Rising 'Synchronous 'Defined) where
  knownDomain tag = SDomain tag SNat SRising SSynchronous SDefined

-- | System instance with defaults set for Intel FPGAs
instance KnownDomain IntelSystem ('Domain IntelSystem 10000 'Rising 'Asynchronous 'Defined) where
  knownDomain tag = SDomain tag SNat SRising SAsynchronous SDefined

type System = "System"
type IntelSystem = "IntelSystem"
type XilinxSystem = "XilinxSystem"

infixr 5 :-
{- |  TODO: docs
-}
data Signal (tag :: Symbol) a
  -- | The constructor, @(':-')@, is __not__ synthesizable.
  = a :- Signal tag a

head# :: Signal tag a -> a
head# (x' :- _ )  = x'

tail# :: Signal tag a -> Signal tag a
tail# (_  :- xs') = xs'

instance Show a => Show (Signal tag a) where
  show (x :- xs) = show x ++ " " ++ show xs

instance Lift a => Lift (Signal tag a) where
  lift ~(x :- _) = [| signal# x |]

instance Default a => Default (Signal tag a) where
  def = signal# def

instance Functor (Signal tag) where
  fmap = mapSignal#

{-# NOINLINE mapSignal# #-}
mapSignal# :: (a -> b) -> Signal tag a -> Signal tag b
mapSignal# f (a :- as) = f a :- mapSignal# f as

instance Applicative (Signal tag) where
  pure  = signal#
  (<*>) = appSignal#

{-# NOINLINE signal# #-}
signal# :: a -> Signal tag a
signal# a = let s = a :- s in s

{-# NOINLINE appSignal# #-}
appSignal# :: Signal tag (a -> b) -> Signal tag a -> Signal tag b
appSignal# (f :- fs) xs@(~(a :- as)) = f a :- (xs `seq` appSignal# fs as) -- See [NOTE: Lazy ap]

{- NOTE: Lazy ap
Signal's ap, i.e (Applicative.<*>), must be lazy in it's second argument:

> appSignal :: Signal' clk (a -> b) -> Signal' clk a -> Signal' clk b
> appSignal (f :- fs) ~(a :- as) = f a :- appSignal fs as

because some feedback loops, such as the loop described in 'system' in the
example at http://hackage.haskell.org/package/clash-prelude-0.10.10/docs/Clash-Prelude-BlockRam.html,
will lead to "Exception <<loop>>".

However, this "naive" lazy version is _too_ lazy and induces spaceleaks.
The current version:

> appSignal# :: Signal' clk (a -> b) -> Signal' clk a -> Signal' clk b
> appSignal# (f :- fs) xs@(~(a :- as)) = f a :- (xs `seq` appSignal# fs as)

Is lazy enough to handle the earlier mentioned feedback loops, but doesn't leak
(as much) memory like the "naive" lazy version, because the Signal constructor
of the second argument is evaluated as soon as the tail of the result is evaluated.
-}


{-# NOINLINE joinSignal# #-}
-- | __WARNING: EXTREMELY EXPERIMENTAL__
--
-- The circuit semantics of this operation are unclear and/or non-existent.
-- There is a good reason there is no 'Monad' instance for 'Signal''.
--
-- Is currently treated as 'id' by the Clash compiler.
joinSignal# :: Signal tag (Signal tag a) -> Signal tag a
joinSignal# ~(xs :- xss) = head# xs :- joinSignal# (mapSignal# tail# xss)

instance Num a => Num (Signal tag a) where
  (+)         = liftA2 (+)
  (-)         = liftA2 (-)
  (*)         = liftA2 (*)
  negate      = fmap negate
  abs         = fmap abs
  signum      = fmap signum
  fromInteger = signal# . fromInteger

-- | __NB__: Not synthesizable
--
-- __NB__: In \"@'foldr' f z s@\":
--
-- * The function @f@ should be /lazy/ in its second argument.
-- * The @z@ element will never be used.
instance Foldable (Signal tag) where
  foldr = foldr#

{-# NOINLINE foldr# #-}
-- | __NB__: Not synthesizable
--
-- __NB__: In \"@'foldr#' f z s@\":
--
-- * The function @f@ should be /lazy/ in its second argument.
-- * The @z@ element will never be used.
foldr# :: (a -> b -> b) -> b -> Signal tag a -> b
foldr# f z (a :- s) = a `f` (foldr# f z s)

instance Traversable (Signal tag) where
  traverse = traverse#

{-# NOINLINE traverse# #-}
traverse# :: Applicative f => (a -> f b) -> Signal tag a -> f (Signal tag b)
traverse# f (a :- s) = (:-) <$> f a <*> traverse# f s

-- * Clocks and resets

-- | Distinction between enabled and unenabled clocks
data ClockKind
  = Regular
  -- ^ A clock signal simply represented as a single bit.
  | Enabled
  -- ^ A clock signal that carries an additional signal indicating whether
  -- it's enabled.
  deriving (Eq, Ord, Show, Generic, NFData)

-- | A clock signal belonging to a domain
data Clock (tag :: Symbol) (enabled :: ClockKind) where
  Clock
    :: SSymbol tag
    -> Maybe (Signal tag Bool)
    -> Clock tag enabled

-- | Get the clock period of a 'Clock' (in /ps/) as a 'Num'
clockPeriod
  :: KnownDomain tag dom
  => Num a
  => Clock tag enabled
  -> a
clockPeriod (Clock tag _enabled) =
  case knownDomain tag of
    SDomain _tag period _edge _reset _init ->
      snatToNum period

-- | If the clock is enabled, return 'Just' the /enable/ signal, 'Nothing'
-- otherwise
clockEnable
  :: Clock tag enabled
  -> Maybe (Signal tag Bool)
clockEnable (Clock _tag enabled) = enabled

instance Show (Clock tag enabled) where
  show (Clock tag _enabled) = "<Clock: " ++ show tag ++ ">"

-- | Clock gating primitive
toEnabledClock
  :: Clock tag enabled
  -> Signal tag Bool
  -> Clock tag 'Enabled
toEnabledClock (Clock tag _en) en = Clock tag (Just en)
{-# NOINLINE toEnabledClock #-}

-- | Clock generator for simulations. Do __not__ use this clock generator for
-- for the /testBench/ function, use 'tbClockGen' instead.
--
-- To be used like:
--
-- TODO: Docs
clockGen
  :: KnownDomain tag dom
  => Clock tag 'Regular
clockGen = Clock SSymbol Nothing
{-# NOINLINE clockGen #-}

-- | Clock generator to be used in the /testBench/ function.
--
-- To be used like:
--
-- @
-- type DomA = Dom \"A\" 1000
-- clkA en = clockGen @DomA en
-- @
--
-- === __Example__
--
-- @
-- type DomA1 = Dom \"A\" 1 -- fast, twice as fast as slow
-- type DomB2 = Dom \"B\" 2 -- slow
--
-- topEntity
--   :: Clock DomA1 Source
--   -> Reset DomA1 Asynchronous
--   -> Clock DomB2 Source
--   -> Signal DomA1 (Unsigned 8)
--   -> Signal DomB2 (Unsigned 8, Unsigned 8)
-- topEntity clk1 rst1 clk2 i =
--   let h = register clk1 rst1 0 (register clk1 rst1 0 i)
--       l = register clk1 rst1 0 i
--   in  unsafeSynchronizer clk1 clk2 (bundle (h,l))
--
-- testBench
--   :: Signal DomB2 Bool
-- testBench = done
--   where
--     testInput      = stimuliGenerator clkA1 rstA1 $(listToVecTH [1::Unsigned 8,2,3,4,5,6,7,8])
--     expectedOutput = outputVerifier   clkB2 rstB2 $(listToVecTH [(0,0) :: (Unsigned 8, Unsigned 8),(1,2),(3,4),(5,6),(7,8)])
--     done           = expectedOutput (topEntity clkA1 rstA1 clkB2 testInput)
--     done'          = not \<$\> done
--     clkA1          = 'tbClockGen' \@DomA1 (unsafeSynchronizer clkB2 clkA1 done')
--     clkB2          = 'tbClockGen' \@DomB2 done'
--     rstA1          = resetGen \@DomA1
--     rstB2          = resetGen \@DomB2
-- @
tbClockGen
  :: KnownDomain tag dom
  => Signal tag Bool
  -> Clock tag 'Regular
tbClockGen _ = Clock SSymbol Nothing
{-# NOINLINE tbClockGen #-}

-- | TODO: Docs
resetGen
  :: KnownDomain tag dom
  => Reset tag 'ActiveHigh
resetGen = ActiveHighReset (True :- pure False)
{-# NOINLINE resetGen #-}

-- | TODO: Docs
data ResetPolarity
  = ActiveHigh
  | ActiveLow

-- | A reset signal belonging to a @domain@.
--
-- The underlying representation of resets is 'Bool'. Note that all components
-- in the __clash-prelude__ package have an /active-high/ reset port, i.e., the
-- component is reset when the reset port is 'True'.
data Reset (tag :: Symbol) (polarity :: ResetPolarity) where
  ActiveHighReset :: Signal tag Bool -> Reset tag 'ActiveHigh
  ActiveLowReset :: Signal tag Bool -> Reset tag 'ActiveLow

-- | Convert a reset to an active high reset. Has no effect if reset is already
-- an active high reset.
toHighPolarity
  :: Reset tag polarity
  -> Reset tag 'ActiveHigh
toHighPolarity (ActiveHighReset r) = ActiveHighReset r
toHighPolarity (ActiveLowReset r) = ActiveHighReset (not <$> r)
{-# INLINE toHighPolarity #-}

-- | Convert a reset to an active low reset. Has no effect if reset is already
-- an active low reset.
toLowPolarity
  :: Reset tag polarity
  -> Reset tag 'ActiveLow
toLowPolarity (ActiveHighReset r) = ActiveLowReset (not <$> r)
toLowPolarity (ActiveLowReset r) = ActiveLowReset r
{-# INLINE toLowPolarity #-}

-- | Sync polarity of two reset signals. Inverts polarity of second argument,
-- if polarities are not the same. If they are, it does nothing.
syncPolarity
  :: Reset tag1 polarity1
  -- ^ Reset with desired reset polarity
  -> Reset tag2 polarity2
  -- ^ Reset with some reset polarity
  -> Reset tag2 polarity1
  -- ^ Same reset as second argument, but with reset polarity of the first
syncPolarity r1 r2 =
  case r1 of
    ActiveHighReset _ ->
      toHighPolarity r2
    ActiveLowReset _ ->
      toLowPolarity r2
{-# INLINE syncPolarity #-}

-- | 'unsafeFromAsyncReset' is unsafe because it can introduce:
--
-- * <Clash-Explicit-Signal.html#metastability meta-stability>
--
-- when used in combination with an asynchronous reset. Use 'fromReset' if
-- you're using a synchronous one.
unsafeFromReset
  :: Reset tag polarity
  -> Signal tag Bool
unsafeFromReset (ActiveHighReset r) = r
unsafeFromReset (ActiveLowReset r) = r
{-# NOINLINE unsafeFromReset #-}

-- | It is safe to treat synchronous resets as @Bool@ signals
fromSyncReset
  :: KnownDomain tag ('Domain tag _period _edge 'Synchronous _init)
  => Reset tag polarity
  -> Signal tag Bool
fromSyncReset (ActiveHighReset r) = r
fromSyncReset (ActiveLowReset r) = r
{-# NOINLINE fromSyncReset #-}

-- | 'unsafeToActiveHighReset' is unsafe. For asynchronous resets it is unsafe
-- because it can introduce combinatorial loops. In case of synchronous resets
-- it can lead to <Clash-Explicit-Signal.html#metastability meta-stability>
-- issues in the presence of asynchronous resets.
--
-- === __Example__
--
-- TODO: Example
unsafeToActiveHighReset :: Signal tag Bool -> Reset tag 'ActiveHigh
unsafeToActiveHighReset r = ActiveHighReset r
{-# NOINLINE unsafeToActiveHighReset #-}

-- | 'unsafeToActiveHighReset' is unsafe. For asynchronous resets it is unsafe
-- because it can introduce combinatorial loops. In case of synchronous resets
-- it can lead to <Clash-Explicit-Signal.html#metastability meta-stability>
-- issues in the presence of asynchronous resets.
--
-- === __Example__
--
-- TODO: Example
unsafeToActiveLowReset :: Signal tag Bool -> Reset tag 'ActiveLow
unsafeToActiveLowReset r = ActiveLowReset r
{-# NOINLINE unsafeToActiveLowReset #-}


infixr 2 .||.
-- | The above type is a generalisation for:
--
-- @
-- __(.||.)__ :: 'Clash.Signal.Signal' 'Bool' -> 'Clash.Signal.Signal' 'Bool' -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('||') that returns a 'Clash.Signal.Signal' of 'Bool'
(.||.) :: Applicative f => f Bool -> f Bool -> f Bool
(.||.) = liftA2 (||)

infixr 3 .&&.
-- | The above type is a generalisation for:
--
-- @
-- __(.&&.)__ :: 'Clash.Signal.Signal' 'Bool' -> 'Clash.Signal.Signal' 'Bool' -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('&&') that returns a 'Clash.Signal.Signal' of 'Bool'
(.&&.) :: Applicative f => f Bool -> f Bool -> f Bool
(.&&.) = liftA2 (&&)

-- [Note: register strictness annotations]
--
-- In order to produce the first (current) value of the register's output
-- signal, 'o', we don't need to know the shape of either input (enable or
-- value-in).  This is important, because both values might be produced from
-- the output in a feedback loop, so we can't know their shape (pattern
-- match) them until we have produced output.
--
-- Thus, we use lazy pattern matching to delay inspecting the shape of
-- either argument until output has been produced.
--
-- However, both arguments need to be evaluated to WHNF as soon as possible
-- to avoid a space-leak.  Below, we explicitly reduce the value-in signal
-- using 'seq' as the tail of our output signal is produced.  On the other
-- hand, because the value of the tail depends on the value of the enable
-- signal 'e', it will be forced by the 'if'/'then' statement and we don't
-- need to 'seq' it explicitly.

delay#
  :: Undefined a
  => Clock tag enabled
  -> a
  -> Signal tag a
  -> Signal tag a
delay# (Clock _tag Nothing) dflt =
  \s -> dflt :- s

delay# (Clock _tag (Just en)) dflt =
    go dflt en
  where
    go o (e :- es) as@(~(x :- xs)) =
      let o' = if e then x else o
      -- See [Note: register strictness annotations]
      in  o `defaultSeqX` o :- (as `seq` go o' es xs)
{-# NOINLINE delay# #-}

-- | A register with a power up and reset value. Power up values are not
-- supported on all platforms, please consult the manual of your target platform
-- and check the notes below.
--
-- Xilinx: power up values and reset values MUST be the same. If they are not,
-- the Xilinx tooling __will ignore the reset value__ and use the power up value
-- instead.
--
-- Intel: power up values and reset values MUST be the same. If they are not,
-- the Intel tooling __will ignore the power up value__ and use the reset value
-- instead.
register#
  :: forall tag dom enabled a
   . ( KnownDomain tag dom
     , Undefined a )
  => Clock tag enabled
  -> Reset tag 'ActiveHigh
  -> a
  -- ^ Power up value
  -> a
  -- ^ Reset value
  -> Signal tag a
  -> Signal tag a
register# (Clock tag Nothing) rst powerUpVal resetVal =
  case knownDomain tag of
    SDomain _tag _period _edge SSynchronous _init ->
      goSync powerUpVal (unsafeFromReset rst)
    SDomain _tag _period _edge SAsynchronous _init ->
      goAsync powerUpVal (unsafeFromReset rst)
 where
  goSync
    :: a
    -> Signal tag Bool
    -> Signal tag a
    -> Signal tag a
  goSync o rt@(~(r :- rs)) as@(~(x :- xs)) =
    let o' = if r then resetVal else x
        -- [Note: register strictness annotations]
    in  o `defaultSeqX` o :- (rt `seq` as `seq` goSync o' rs xs)

  goAsync
    :: a
    -> Signal tag Bool
    -> Signal tag a
    -> Signal tag a
  goAsync o0 (r :- rs) as@(~(x :- xs)) =
    let o1 = if r then resetVal else o0
        oN = if r then resetVal else x
        -- [Note: register strictness annotations]
    in  o1 `defaultSeqX` o1 :- (as `seq` goAsync oN rs xs)

register# (Clock tag (Just ena)) rst powerUpVal resetVal =
  case knownDomain tag of
    SDomain _tag _period _edge SSynchronous _init ->
      goSync powerUpVal (unsafeFromReset rst) ena
    SDomain _tag _period _edge SAsynchronous _init ->
      goAsync powerUpVal (unsafeFromReset rst) ena
 where
  goSync
    :: a
    -> Signal tag Bool
    -> Signal tag Bool
    -> Signal tag a
    -> Signal tag a
  goSync o rt@(~(r :- rs)) enas@(~(e :- es)) as@(~(x :- xs)) =
    let oE = if e then x else o
        oR = if r then resetVal else oE
        -- [Note: register strictness annotations]
    in  o `defaultSeqX` o :- (rt `seq` enas `seq` as `seq` goSync oR rs es xs)

  goAsync
    :: a
    -> Signal tag Bool
    -> Signal tag Bool
    -> Signal tag a
    -> Signal tag a
  goAsync o (r :- rs) enas@(~(e :- es)) as@(~(x :- xs)) =
    let oR = if r then resetVal else o
        oE = if r then resetVal else (if e then x else o)
        -- [Note: register strictness annotations]
    in  oR `defaultSeqX` oR :- (as `seq` enas `seq` goAsync oE rs es xs)
{-# NOINLINE register# #-}

-- | The above type is a generalisation for:
--
-- @
-- __mux__ :: 'Clash.Signal.Signal' 'Bool' -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a
-- @
--
-- A multiplexer. Given "@'mux' b t f@", output @t@ when @b@ is 'True', and @f@
-- when @b@ is 'False'.
mux :: Applicative f => f Bool -> f a -> f a -> f a
mux = liftA3 (\b t f -> if b then t else f)
{-# INLINE mux #-}

infix 4 .==.
-- | The above type is a generalisation for:
--
-- @
-- __(.==.)__ :: 'Eq' a => 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('==') that returns a 'Clash.Signal.Signal' of 'Bool'
(.==.) :: (Eq a, Applicative f) => f a -> f a -> f Bool
(.==.) = liftA2 (==)

infix 4 ./=.
-- | The above type is a generalisation for:
--
-- @
-- __(./=.)__ :: 'Eq' a => 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('/=') that returns a 'Clash.Signal.Signal' of 'Bool'
(./=.) :: (Eq a, Applicative f) => f a -> f a -> f Bool
(./=.) = liftA2 (/=)

infix 4 .<.
-- | The above type is a generalisation for:
--
-- @
-- __(.<.)__ :: 'Ord' a => 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('<') that returns a 'Clash.Signal.Signal' of 'Bool'
(.<.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.<.) = liftA2 (<)

infix 4 .<=.
-- | The above type is a generalisation for:
--
-- @
-- __(.<=.)__ :: 'Ord' a => 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('<=') that returns a 'Clash.Signal.Signal' of 'Bool'
(.<=.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.<=.) = liftA2 (<=)

infix 4 .>.
-- | The above type is a generalisation for:
--
-- @
-- __(.>.)__ :: 'Ord' a => 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' 'Bool'
-- @
--
-- It is a version of ('>') that returns a 'Clash.Signal.Signal' of 'Bool'
(.>.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.>.) = liftA2 (>)

infix 4 .>=.
-- | The above type is a generalisation for:
--
-- @
-- __(.>=.)__ :: 'Ord' a => 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' 'Bool'
-- @
--
--  It is a version of ('>=') that returns a 'Clash.Signal.Signal' of 'Bool'
(.>=.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.>=.) = liftA2 (>=)

instance Fractional a => Fractional (Signal tag a) where
  (/)          = liftA2 (/)
  recip        = fmap recip
  fromRational = signal# . fromRational

instance Arbitrary a => Arbitrary (Signal tag a) where
  arbitrary = liftA2 (:-) arbitrary arbitrary

instance CoArbitrary a => CoArbitrary (Signal tag a) where
  coarbitrary xs gen = do
    n <- arbitrary
    coarbitrary (take (abs n) (sample_lazy xs)) gen

-- | The above type is a generalisation for:
--
-- @
-- __testFor__ :: 'Int' -> 'Clash.Signal.Signal' Bool -> 'Property'
-- @
--
-- @testFor n s@ tests the signal @s@ for @n@ cycles.
testFor :: Foldable f => Int -> f Bool -> Property
testFor n = property . and . take n . sample

-- * List \<-\> Signal conversion (not synthesizable)

-- | The above type is a generalisation for:
--
-- @
-- __sample__ :: 'Clash.Signal.Signal' a -> [a]
-- @
--
-- Get an infinite list of samples from a 'Clash.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'Clash.Signal.Signal'
-- at consecutive clock cycles
--
-- > sample s == [s0, s1, s2, s3, ...
--
-- __NB__: This function is not synthesizable
sample :: (Foldable f, Undefined a) => f a -> [a]
sample = foldr (\a b -> deepseqX a (a : b)) []

-- | The above type is a generalisation for:
--
-- @
-- __sampleN__ :: Int -> 'Clash.Signal.Signal' a -> [a]
-- @
--
-- Get a list of @n@ samples from a 'Clash.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'Clash.Signal.Signal'
-- at consecutive clock cycles
--
-- > sampleN 3 s == [s0, s1, s2]
--
-- __NB__: This function is not synthesizable
sampleN :: (Foldable f, Undefined a) => Int -> f a -> [a]
sampleN n = take n . sample

-- | Create a 'Clash.Signal.Signal' from a list
--
-- Every element in the list will correspond to a value of the signal for one
-- clock cycle.
--
-- >>> sampleN 2 (fromList [1,2,3,4,5])
-- [1,2]
--
-- __NB__: This function is not synthesizable
fromList :: Undefined a => [a] -> Signal tag a
fromList = Prelude.foldr (\a b -> deepseqX a (a :- b)) (errorX "finite list")

-- * Simulation functions (not synthesizable)

-- | Simulate a (@'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' b@) function
-- given a list of samples of type @a@
--
-- >>> simulate (register systemClockGen resetGen 8) [1, 1, 2, 3]
-- [8,8,1,2,3...
-- ...
--
-- __NB__: This function is not synthesizable
simulate :: (Undefined a, Undefined b) => (Signal tag1 a -> Signal tag2 b) -> [a] -> [b]
simulate f = sample . f . fromList

-- | The above type is a generalisation for:
--
-- @
-- __sample__ :: 'Clash.Signal.Signal' a -> [a]
-- @
--
-- Get an infinite list of samples from a 'Clash.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'Clash.Signal.Signal'
-- at consecutive clock cycles
--
-- > sample s == [s0, s1, s2, s3, ...
--
-- __NB__: This function is not synthesizable
sample_lazy :: Foldable f => f a -> [a]
sample_lazy = foldr (:) []

-- | The above type is a generalisation for:
--
-- @
-- __sampleN__ :: Int -> 'Clash.Signal.Signal' a -> [a]
-- @
--
-- Get a list of @n@ samples from a 'Clash.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'Clash.Signal.Signal'
-- at consecutive clock cycles
--
-- > sampleN 3 s == [s0, s1, s2]
--
-- __NB__: This function is not synthesizable
sampleN_lazy :: Foldable f => Int -> f a -> [a]
sampleN_lazy n = take n . sample_lazy

-- | Create a 'Clash.Signal.Signal' from a list
--
-- Every element in the list will correspond to a value of the signal for one
-- clock cycle.
--
-- >>> sampleN 2 (fromList [1,2,3,4,5])
-- [1,2]
--
-- __NB__: This function is not synthesizable
fromList_lazy :: [a] -> Signal tag a
fromList_lazy = Prelude.foldr (:-) (error "finite list")

-- * Simulation functions (not synthesizable)

-- | Simulate a (@'Clash.Signal.Signal' a -> 'Clash.Signal.Signal' b@) function
-- given a list of samples of type @a@
--
-- >>> simulate (register systemClockGen resetGen 8) [1, 1, 2, 3]
-- [8,8,1,2,3...
-- ...
--
-- __NB__: This function is not synthesizable
simulate_lazy :: (Signal tag1 a -> Signal tag2 b) -> [a] -> [b]
simulate_lazy f = sample_lazy . f . fromList_lazy
