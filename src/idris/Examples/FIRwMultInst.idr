import SynQ

import Examples.FIRwMult
import Data.Vect
import System.File

import Impl.TAC

import Sym.CombP

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

-- coefs: Vect 25 Bits64
-- coefs = [442, 1284, 1094, 65417, 64382, 65275, 1446, 1072, 63771, 62732, 1982, 10196, 14323, 10196, 1982, 62732, 63771, 1072, 1446, 65275, 64382, 65417, 1094, 1284, 442]

-- coefs: Vect 128 Bits64
-- coefs = [0, 0, 0, 0, 0, 0, 65535, 65535, 1, 1, 0, 65533, 65535, 4, 3, 65531, 65530, 4, 11, 65534, 65519, 65532, 21, 14, 65512, 65508, 21, 45, 65525, 65473, 65528, 78, 39, 65451, 65456, 77, 128, 65485, 65359, 65535, 219, 79, 65295, 65354, 231, 304, 65361, 65102, 61, 555, 122, 64890, 65154, 676, 731, 64927, 64346, 382, 1820, 150, 62675, 63977, 5927, 13523, 13523, 5927, 63977, 62675, 150, 1820, 382, 64346, 64927, 731, 676, 65154, 64890, 122, 555, 61, 65102, 65361, 304, 231, 65354, 65295, 79, 219, 65535, 65359, 65485, 128, 77, 65456, 65451, 39, 78, 65528, 65473, 65525, 45, 21, 65508, 65512, 14, 21, 65532, 65519, 65534, 11, 4, 65530, 65531, 3, 4, 65535, 65533, 0, 1, 1, 65535, 65535, 0, 0, 0, 0, 0, 0]

-- coefs: Vect 64 Bits64
-- coefs = [65525, 2, 49, 78, 23, 65469, 65483, 73, 110, 65488, 65364, 65521, 225, 121, 65293, 65269, 202, 436, 65460, 64934, 65378, 723, 518, 64791, 64510, 588, 1738, 65443, 62658, 64216, 6042, 13329, 13329, 6042, 64216, 62658, 65443, 1738, 588, 64510, 64791, 518, 723, 65378, 64934, 65460, 436, 202, 65269, 65293, 121, 225, 65521, 65364, 65488, 110, 73, 65483, 65469, 23, 78, 49, 2, 65525]

coefs: Vect 32 Bits64
coefs = [58, 65241, 64699, 64630, 65441, 745, 382, 64733, 64650, 712, 1646, 65272, 62671, 64395, 6115, 13186, 13186, 6115, 64395, 62671, 65272, 1646, 712, 64650, 64733, 382, 745, 65441, 64630, 64699, 65241, 58]

-- coefs: Vect 16 Bits64
-- coefs = [1381, 3033, 2827, 65319, 62375, 64338, 6190, 13188, 13188, 6190, 64338, 62375, 65319, 2827, 3033, 1381]

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

-- fir: (Seq comb seq, Primitive comb, Arith comb)
--   => (1 reg: Reg (Repeat 127 (BitVec 16)) comb seq)
--   -> seq (RepeatSt 127 $ !* (BitVec 16))
--          (BitVec 1, BitVec 1, BitVec 16) (BitVec 32)
-- fir reg = 
--   let init = initN 127 (const $ BV 0)
--   in mkFIR {coefW=16} init coefs reg 

fir': (Seq comb seq, Primitive comb, Arith comb)
   => (1 reg: Reg (Repeat 31 (BitVec 16)) comb seq)
   -> seq (RepeatSt 31 $ !* (BitVec 16))
          (BitVec 16) (BitVec 32)
fir' reg = 
  mkFIR' {coefW=16} coefs reg 

-- firTAC: FTAC
-- firTAC = moveState $ elimDead $ elimGet $ flatTAC $ genTAC (fir reg)

firTAC': FTAC
firTAC' = 
  let _ : (St (RepeatSt 31 $ !* (BitVec 16))) = repeatSt {n=31}
  in moveState $ elimDead $ elimGet $ flatTAC $ genTAC (fir' reg)


swap: (Comb comb, Primitive comb)
  => comb () (UInt8, UInt8)
  -> comb () (UInt8, UInt8) 
swap x = prod (adder' (proj1 x) (proj2 x))
              (proj2 x)

testSys: (Comb comb, Primitive comb)
  => comb () (UInt8, UInt8)
  -> comb () (UInt8, UInt8) 
testSys x = swap $ swap x

tt: (Seq comb seq, Primitive comb)
  => seq (!* UInt8) 
         (UInt8, UInt8)
         (UInt8, UInt8)
tt = Seq.pure $ prodElim $ lam testSys

ttac: TAC
ttac = genTAC (tt {comb = TACComb})
