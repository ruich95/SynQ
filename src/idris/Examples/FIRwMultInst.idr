import SynQ

import Examples.FIRwMult
import Data.Vect
import System.File

import Impl.TAC

%hide Data.Linear.Interface.seq
-- %hide Prelude.(>>=)
%hide LState.(>>=)
-- %hide Prelude.(=<<)
-- %hide Prelude.pure

{- 
  25 taps lowpass FIR filter.
  sample rate        : 2000 Hz
  pass band          : 400  Hz
  stop band (-40 dB) : 500  Hz
  weight (12 bit): 
    28 80 68 -7 -72 -16 90 67 -110 -175 124 637 895 637 124 -175 -110 67 90 -16 -72 -7 68 80 28
  input: 8 bit
  output: 21 bit
-}

weight: Vect 25 Bits64
weight = [28, 80, 68, 7, 72, 16, 90, 67, 110, 175, 124, 637, 
          895, 637, 124, 175, 110, 67, 90, 16, 72, 7, 68, 80, 28]

sign: Vect 25 Bool
sign = [True, True, True, False, False, False, True, True, False, False, True, True, True, 
        True, True, False, False, True, True, False, False, False, True, True, True]

initN: (Comb comb, Primitive comb)
    => {w: Nat} 
    -> (n: Nat) 
    -> comb () (BitVec w) 
    -> comb () (Repeat n (BitVec w))
initN 0         x = unit
initN (S 0)     x = x
initN (S (S k)) x = 
  let _ = repeatSig (S k) $ BV {n=w} 
  in prod x $ initN (S k) x

initSt: {w: Nat} 
     -> (n: Nat) 
     -> (BitVec w) 
     -> RepeatSt n $ !* (BitVec w)
initSt 0         x = ()
initSt (S 0)     x = MkBang x
initSt (S (S k)) x = (MkBang x) # initSt (S k) x

fir: (Seq comb seq, Primitive comb, Mult comb)
  => (1 reg: Reg (Repeat 24 (BitVec 16)) comb seq)
  -> seq (RepeatSt 24 $ !* (BitVec 16))
         (BitVec 1, BitVec 1, BitVec 16) (BitVec 32)
fir reg = 
  let init = initN 24 (const $ BV 0)
  in mkFIR {coefW=16} init weight sign reg 

--firMealy: (BitVec 1, BitVec 1, BitVec 8) 
--  -> LState (RepeatSt 25 $ !* (BitVec 21)) (BitVec 21)
--firMealy = runSeq $ fir Eval.SeqPrimitive.reg
