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
  weight (16 bit): 
    [442, 1284, 1094, -119, -1154, -261, 1446, 1072, -1765, -2804, 1982, 10196, 14323, 10196, 1982, -2804, -1765, 1072, 1446, -261, -1154, -119, 1094, 1284, 442]
  input: 16 bit
  coefs: 16 bit
  output: 32 bit
-}

coefs: Vect 25 Bits64
coefs = [442, 1284, 1094, 65417, 64382, 65275, 1446, 1072, 63771, 62732, 1982, 10196, 14323, 10196, 1982, 62732, 63771, 1072, 1446, 65275, 64382, 65417, 1094, 1284, 442]

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

fir: (Seq comb seq, Primitive comb, Arith comb)
  => (1 reg: Reg (Repeat 24 (BitVec 16)) comb seq)
  -> seq (RepeatSt 24 $ !* (BitVec 16))
         (BitVec 1, BitVec 1, BitVec 16) (BitVec 32)
fir reg = 
  let init = initN 24 (const $ BV 0)
  in mkFIR {coefW=16} init coefs reg 

firTAC: FTAC
firTAC = moveState $ elimDead $ elimGet $ flatTAC $ genTAC (fir reg)


