import SynQ

import Sym.Comb.ElabScripts
import Data.Linear
import Examples.Sel
import System.File
import Data.List
import Language.Reflection

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide LState.(>>=)
%hide Prelude.(=<<)
-- %hide Prelude.pure

RepeatSt: Nat -> (s: Type) -> Type
RepeatSt 0 s = ()
RepeatSt (S 0) s = s
RepeatSt (S (S k)) s = LPair s (RepeatSt (S k) s)

%hint
repeatStIsSt: {auto sIsSt: St s} -> {n: Nat} -> St (RepeatSt n s)
repeatStIsSt {n = 0} = LU
repeatStIsSt {n = (S 0)} = sIsSt
repeatStIsSt {n = (S (S k))} = LP sIsSt repeatStIsSt

%hint
sameShape: {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s} 
  -> {auto similar: SameShape a s}
  -> {n: Nat} -> SameShape (Repeat n a) (RepeatSt n s)
sameShape {n = 0} = U
sameShape {n = (S 0)} = similar
sameShape {n = (S (S k))} = P similar (sameShape {n=(S k)})


dropLast: (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} 
  -> {n: _}
  -> comb () (Repeat (S n) a)
  -> comb () (Repeat n a)
dropLast {n = 0} x = unit
dropLast {n = (S 0)} x = proj1 x
dropLast {n = (S (S k))} x = 
  let _ = repeatSig (S k) aIsSig
  in prod (proj1 x) (dropLast $ proj2 x)

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

genIf: (Comb comb, Primitive comb) 
  => {auto aIsSig: Sig a}
  -> Elab (comb () (BitVec 1) -> comb () a -> comb () a)
genIf {aIsSig = U} = pure $ \_ => \_ => unit
genIf {aIsSig = (P x y)} = ?genIf'_rhs_1
genIf {aIsSig = BV} = ?genIf'_rhs_2

-- mkFIFO: forall s. (Seq comb seq, Primitive comb)
--   => {cWidth: _} -> {n: Nat} 
--   -> {0 a:_} -> {auto aIsSig: Sig a} 
--   -> {auto sIsSt: St s}
--   -> {auto similar: SameShape a s}
--   -> {auto notEmpty: LTE 1 n}
--   -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
--   -> LPair
--        -- forward path
--        -- input: rst_n
--        -- output: (validO, dataO)
--        ((rst_n : comb () (BitVec 1))
--          -> seq (LPair (!* BitVec cWidth) (RepeatSt n s)) () (BitVec 1, a)) 
--        -- backward path
--        -- input:  dataI, validI, readyI (from the successor stage), rst_n
--        -- output: readyO (to previous stage)
--        ((dataI: comb () a) 
--          -> (validI: comb () (BitVec 1)) 
--          -> (rst_n : comb () (BitVec 1)) 
--          -> (readyI: comb () (BitVec 1))
--          -> seq (LPair (!* BitVec cWidth) (RepeatSt n s)) () (BitVec 1))
-- mkFIFO {n} {notEmpty} (MkReg get set) =
--   let pSig0: Sig (Repeat n a) = repeatSig n aIsSig
--       pSig1: Sig (BitVec cWidth, Repeat n a) = P BV pSig0
--       pSt0: St (RepeatSt n s) = repeatStIsSt 
--       pSt1: St (LPair (!* BitVec cWidth) (RepeatSt n s)) = LP LV pSt0
--       pSame0: SameShape (Repeat n a) (RepeatSt n s)
--         = sameShape
--       pSame1: SameShape (BitVec cWidth, Repeat n a) 
--                         (LPair ((!*) (BitVec cWidth)) 
--                         (RepeatSt n s)) 
--         = P BV pSame0
--   in (\rst_n => 
--         do curSt  <- get
--            let curCount = proj1 curSt
--                curMemSt = proj2 curSt
--            out    <- pure $ sel {prf=notEmpty} 
--                                 (lower' cWidth $ add curCount (not $ const $ BV 0))
--                                 curMemSt
--            validO <- pure $ (not $ curCount `eq` (const $ BV 0))
--            pure $ prod (rst_n `and` validO) out)
--    # (\dataI => \validI => \rst_n => \readyI => 
--          do curSt <- get
--             let curCount = proj1 curSt
--                 curMemSt = proj2 curSt
--                 produce  = (not $ curCount `eq` (const $ BV 0)) `and` (readyI)
--                 nxtCount = mux21 produce 
--                                  (lower' cWidth $ add curCount (not $ const $ BV 0))
--                                  curCount
--                 maxCount = const (BV {n=cWidth} (cast n))
--                 readyO   = (nxtCount `ltu` maxCount)
--                 en       = readyO `and` validI
--                 nxtCount = mux21 en
--                                  (lower' cWidth $ add nxtCount (const $ BV 1))
--                                  nxtCount
--             update <- pure $ case n of 
--                                0         => unit
--                                (S 0)     => dataI
--                                (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
--                                                  dataI (dropLast curMemSt)
--             _      <- set $ prod (mux21 rst_n nxtCount (const $ BV 0)) 
--                                  (if_ en update curMemSt)
--             pure (rst_n `and` readyO))
