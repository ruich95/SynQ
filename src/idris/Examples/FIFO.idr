import SynQ

import Data.Linear

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
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

sInPOut: {0 s: _} -> {0 a:_} -> {n: Nat} 
  -> (Seq comb seq, Reg (Repeat n a) comb seq, Primitive comb)
  => {auto sIsSt: St s}
  -> {auto aIsSig: Sig a} 
  -> {auto similar: SameShape a s}
  -> (dat: comb () a)
  -> (en:  comb () (BitVec 1))
  -> seq (RepeatSt n s) () (Repeat n a)
sInPOut dat en = 
  let sigOut: Sig (Repeat n a) = repeatSig n aIsSig
      stSt:  St (RepeatSt n s) = repeatStIsSt {sIsSt=sIsSt} {n=n}
      similar': SameShape (Repeat n a) (RepeatSt n s)
        = sameShape
  in do pre <- get
        update <- pure $ case n of
                           0         => pre
                           (S 0)     => dat
                           (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
                                             dat (dropLast pre)
        nxt <- pure $ if_ en update pre
        pure pre
        
record SeqInParOut 
  (n: Nat) (0 a: Type) 
  (0 comb: Type -> Type -> Type) 
  (0 seq: Type -> Type -> Type -> Type) where
  constructor MkSIPO
  1 view: {auto sIsSt: St s}
       -> {auto aIsSig: Sig a} 
       -> {auto similar: SameShape a s}
       -> seq (RepeatSt n s) () (Repeat n a)
       
  1 read: {auto sIsSt: St s}
       -> {auto aIsSig: Sig a} 
       -> {auto similar: SameShape a s}
       -> (dat: comb () a)
       -> (en:  comb () (BitVec 1))
       -> seq (RepeatSt n s) () ()

mkSeqInParOut: {0 a:_} -> {0 s:_} -> {n: Nat} 
  -> (Seq comb seq, Primitive comb)
  => {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (Repeat n a) comb seq)
  -> SeqInParOut n a comb seq
mkSeqInParOut (MkReg get set) = 
  let oSig = repeatSig n aIsSig
      stSt: St (RepeatSt n s) = repeatStIsSt {sIsSt=sIsSt} {n=n}
      samilar: SameShape (Repeat n a) (RepeatSt n s) = sameShape
      view: seq (RepeatSt n s) () (Repeat n a)
          = get 
            
      read: comb () a
         -> comb () (BitVec 1)
         -> seq (RepeatSt n s) () ()
         = \dat => \en => do pre <- view 
                             update <- pure $ case n of
                                                0         => pre
                                                (S 0)     => dat
                                                (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
                                                                  dat (dropLast pre)
                             nxt <- pure $ if_ en update pre
                             set nxt
  in MkSIPO view read
  

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

%ambiguity_depth 8
consumeCtrl: {cWidth: _} 
  -> (Seq comb seq, Primitive comb)
  => (n: Nat)
  -> (1 count: Reg (BitVec cWidth) comb seq)
  -> (vaild: comb () (BitVec 1))
  -> (update: comb () (BitVec cWidth) -> comb () (BitVec cWidth)) 
  -> seq (!* BitVec cWidth) () (BitVec 1)
consumeCtrl n (MkReg get set) vaild update = 
  do curCount <- get
     capicity <- pure $ CombPrimitive.const (BV {n=cWidth} (cast n))
     hasSpace <- pure $ (curCount `ltu` capicity)
     nxtCount <- pure $ update $ mux21 hasSpace (lower' cWidth $ add curCount (const $ BV 1))
                                                curCount
     _ <- set nxtCount
     pure hasSpace
