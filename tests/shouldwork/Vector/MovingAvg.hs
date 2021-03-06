module MovingAvg where

import Clash.Prelude

windowN
  :: HiddenClockReset domain gated synchronous
  => Default a
  => KnownNat n
  => Undefined a
  => SNat (n+1)
  -> Signal domain a
  -> Vec (n + 1) (Signal domain a)
windowN size = window

movingAvarageNaive size signal =  fold (+) <$> bundle (windowN size signal)

topEntity
  :: Clock System Source
  -> Reset System Asynchronous
  -> Signal System (Signed 9)
  -> Signal System (Signed 9)
topEntity = exposeClockReset (movingAvarageNaive d5)
