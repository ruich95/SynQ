import SynQ

import Data.Linear
import Examples.Sel
import System.File

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide LState.(>>=)
%hide Prelude.(=<<)
%hide Prelude.pure

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

consumeCtrl: {cWidth: _} 
  -> (Comb comb, Primitive comb)
  => (n: Nat)
  -> (curCount: comb () (BitVec cWidth))
  -> (vaild: comb () (BitVec 1))
  -> comb () (BitVec cWidth, BitVec 1, BitVec 1) -- nxtCount, en, ready
consumeCtrl n curCount vaild = 
  let maxCount = const (BV {n=cWidth} (cast n))
      consume  = (curCount `ltu` maxCount) `and` vaild
      nxtCount = mux21 consume 
                       (lower' cWidth $ add curCount (const $ BV 1))
                       curCount
  in prod nxtCount $ prod consume (curCount `ltu` maxCount)

produceCtrl: {cWidth: _} 
  -> (Comb comb, Primitive comb)
  => (curCount: comb () (BitVec cWidth))
  -> (ready   : comb () (BitVec 1))
  -- -> (nxtCount': comb () (BitVec cWidth))
  -> comb () (BitVec cWidth, BitVec 1) -- nxtCount, valid
produceCtrl curCount ready = 
  let produce  = (not $ curCount `eq` (const $ BV 0)) `and` (ready)
      nxtCount = mux21 produce 
                       (lower' cWidth $ add curCount (not $ const $ BV 0))
                       curCount
  in prod nxtCount (not $ curCount `eq` (const $ BV 0))
      
fifo': (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {0 s:_} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> (dat   : comb () a)
  -> (validI: comb () (BitVec 1))
  -> (ready : comb () (BitVec 1))
  -> (rst_n : comb () (BitVec 1))
  -> seq (LPair (!* BitVec cWidth) (RepeatSt n s))
         () (BitVec 1, BitVec 1, a) --(readyO, validO, oData)
fifo' (MkReg get set) dat validI ready rst_n = 
  let pSig0: Sig (Repeat n a) = repeatSig n aIsSig
      pSig1: Sig (BitVec cWidth, Repeat n a) = P BV pSig0
      pSt0: St (RepeatSt n s) = repeatStIsSt 
      pSt1: St (LPair (!* BitVec cWidth) (RepeatSt n s)) = LP LV pSt0
      pSame0: SameShape (Repeat n a) (RepeatSt n s)
        = sameShape
      pSame1: SameShape (BitVec cWidth, Repeat n a) 
                        (LPair ((!*) (BitVec cWidth)) 
                        (RepeatSt n s)) 
        = P BV pSame0
  in do curSt      <- get
        let curCount = proj1 curSt
            curMemSt = proj2 curSt
        produceSig <- pure $ produceCtrl curCount ready -- nxtCount'
        let nxtCount' = proj1 produceSig
            validO   = proj2 produceSig
        consumeSig <- pure $ consumeCtrl n nxtCount' validI
        let nxtCount  = proj1 consumeSig
            en        = proj1 $ proj2 consumeSig 
            readyO    = proj2 $ proj2 consumeSig
        out        <- pure $ sel (lower' cWidth $ add curCount (not $ const $ BV 0))
                                 curMemSt
                                 dat
        update     <- pure $ case n of 
                               0         => unit
                               (S 0)     => dat
                               (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
                                                 dat (dropLast curMemSt)
        _          <- set $ prod (mux21 rst_n nxtCount (const $ BV 0)) 
                                 (if_ en update curMemSt)
        pure $ prod (readyO `and` rst_n) (prod (validO `and` rst_n) out)

fifo: (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {0 s:_} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> seq (LPair (!* BitVec cWidth) (RepeatSt n s))
         (BitVec 1, BitVec 1, a, BitVec 1) -- (readyI, validI, dataI, reset_n)
         (BitVec 1, BitVec 1, a) -- (readyO, validO, data))
fifo reg = 
  let pSig0: Sig (Repeat n a) = repeatSig n aIsSig
      pSig1: Sig (BitVec cWidth, Repeat n a) = P BV pSig0
      pSt0: St (RepeatSt n s) = repeatStIsSt 
      pSt1: St (LPair (!* BitVec cWidth) (RepeatSt n s)) = LP LV pSt0
      pSame0: SameShape (Repeat n a) (RepeatSt n s)
        = sameShape
      pSame1: SameShape (BitVec cWidth, Repeat n a) (LPair ((!*) (BitVec cWidth)) (RepeatSt n s)) 
        = P BV pSame0
  in abst $ \iSig => 
       let readyI = proj1 iSig 
           validI = proj1 $ proj2 iSig 
           dat    = proj1 $ proj2 $ proj2 iSig
           rst_n  = proj2 $ proj2 $ proj2 iSig
       in fifo' reg dat validI readyI rst_n
       
-- fifo4: (Seq comb seq, Primitive comb)
--   => (1 reg: Reg (BitVec 2, Repeat 4 UInt8) comb seq)
--   -> seq (LPair (!* BitVec 2) (RepeatSt 4 (!* UInt8)))
--          (BitVec 1, BitVec 1, UInt8)
--          (BitVec 1, BitVec 1, UInt8)
-- fifo4 = fifo {n=4} {sIsSt= LV}

fifo4: (BitVec 1, BitVec 1, UInt8, BitVec 1)
    -> LState (LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8)))
              (BitVec 1, BitVec 1, UInt8)
fifo4 = runSeq $ fifo {n=4} {sIsSt= LV} reg

%unhide Prelude.pure
%unhide Prelude.(>>=)

%ambiguity_depth 5
readIn: IO (BitVec 1, BitVec 1, UInt8, BitVec 1)
readIn = do putStr "Next Stg Ready?: \n"
            fflush stdout
            en <- (pure $ BitVec.fromInteger . cast) <*> getLine
            putStr "Current Input Valid?: \n"
            fflush stdout
            inst <- (pure $ BitVec.fromInteger . cast) <*> getLine
            putStr "Current Input: \n"
            fflush stdout
            pc <- (pure $ BitVec.fromInteger . cast) <*> getLine
            putStr "Reset? (active low): \n"
            fflush stdout
            rst_n <- (pure $ BitVec.fromInteger . cast) <*> getLine
            pure (en, inst, pc, rst_n)

fifoProg: IO ()
fifoProg = reactMealy readIn fifo4 (MkBang 0 # (MkBang 0 # (MkBang 0 # (MkBang 0 # MkBang 0))))
