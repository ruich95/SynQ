import SynQ

import Data.Linear

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
  -> comb () (BitVec cWidth, BitVec 1) -- nxtCount, en
consumeCtrl n curCount vaild = 
  let maxCount = const (BV {n=cWidth} (cast $ minus n 1))
      consume  = (curCount `ltu` maxCount) `and` vaild
      nxtCount = mux21 consume 
                       (lower' cWidth $ add curCount (const $ BV 1))
                       curCount
  in prod nxtCount consume

produceCtrl: {cWidth: _} 
  -> (Comb comb, Primitive comb)
  => (curCount: comb () (BitVec cWidth))
  -> (ready   : comb () (BitVec 1))
  -> (nxtCount': comb () (BitVec cWidth))
  -> comb () (BitVec cWidth, BitVec 1) -- nxtCount, valid
produceCtrl curCount ready nxtCount' = 
  let produce  = (not $ curCount `eq` (const $ BV 0)) `and` (ready)
      nxtCount = mux21 produce 
                       (lower' cWidth $ add nxtCount' (not $ const $ BV 0))
                       nxtCount'
  in prod nxtCount produce

sel: {cWidth: _} -> (Comb comb, Primitive comb)
  => {n: Nat}
  -> {auto aIsSig: Sig a}
  -> (idx: comb () (BitVec cWidth))
  -> (dat: comb () (Repeat n a))
  -> comb () a
  
%ambiguity_depth 8
fifo': (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {0 s:_} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> (dat   : comb () a)
  -> (validI: comb () (BitVec 1))
  -> (ready : comb () (BitVec 1))
  -> seq (LPair (!* BitVec cWidth) (RepeatSt n s))
         () (BitVec 1, BitVec 1, a) --(readyO, validO, oData)
fifo' (MkReg get set) dat validI ready = 
  let pSig0: Sig (Repeat n a) = repeatSig n aIsSig
      pSig1: Sig (BitVec cWidth, Repeat n a) = P BV pSig0
      pSt0: St (RepeatSt n s) = repeatStIsSt 
      pSt1: St (LPair (!* BitVec cWidth) (RepeatSt n s)) = LP LV pSt0
      pSame0: SameShape (Repeat n a) (RepeatSt n s)
        = sameShape
      pSame1: SameShape (BitVec cWidth, Repeat n a) (LPair ((!*) (BitVec cWidth)) (RepeatSt n s)) 
        = P BV pSame0
  in do curSt      <- get
        let curCount = proj1 curSt
            curMemSt = proj2 curSt
        consumeSig <- pure $ consumeCtrl n curCount validI
        let (nxtCount', readyO) = (proj1 consumeSig, proj2 consumeSig)
        produceSig <- pure $ produceCtrl curCount ready nxtCount'
        let (nxtCount, validO) = (proj1 produceSig, proj2 produceSig)
        out        <- pure $ sel (lower' cWidth $ add curCount (not $ const $ BV 0))
                                 curMemSt
        update     <- pure $ case n of 
                               0         => unit
                               (S 0)     => dat
                               (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
                                                 dat (dropLast curMemSt)
        _          <- set $ prod nxtCount (if_ readyO update curMemSt)
        pure $ prod readyO (prod validO out)

fifo: (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {0 s:_} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> seq (LPair (!* BitVec cWidth) (RepeatSt n s))
         (BitVec 1, BitVec 1, a) -- (readyI, validI, iData)
         (BitVec 1, BitVec 1, a) -- (readyO, validO, oData)
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
           dat    = proj2 $ proj2 iSig
       in fifo' reg dat validI readyI
