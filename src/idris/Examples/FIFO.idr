import SynQ

import Data.Linear

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide Prelude.pure

FifoSt: Nat -> (s: Type) -> {auto sIsSt: St s} -> Type
FifoSt 0 s = ()
FifoSt (S 0) s = s
FifoSt (S (S k)) s = LPair s (FifoSt (S k) s)

%hint
fifoStIsSt: {auto sIsSt: St s} -> {n: Nat} -> St (FifoSt n s)
fifoStIsSt {n = 0} = LU
fifoStIsSt {n = (S 0)} = sIsSt
fifoStIsSt {n = (S (S k))} = LP sIsSt fifoStIsSt

%hint
sameShape: {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s} 
  -> {auto similar: SameShape a s}
  -> {n: Nat} -> SameShape (Repeat n a) (FifoSt n s)
sameShape {n = 0} = U
sameShape {n = (S 0)} = similar
sameShape {n = (S (S k))} = P similar (sameShape {n=(S k)})

lemma: {n:_} -> (a, Repeat n a) = Repeat (S n) a

dropLast: (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} 
  -> {n: _}
  -> comb () (Repeat (S n) a)
  -> comb () (Repeat n a)
dropLast {n = 0} x = unit
dropLast {n = (S k)} x = 
  let inputSig = repeatSig (S k) aIsSig 
  in ?rhs2 -- prod {aIsSig=aIsSig} {bIsSig=repeatSig k aIsSig} (proj1 x) (dropLast (proj2 x))

sInPOut: {0 s: _} -> {0 a:_} -> {n: Nat} 
  -> (Seq comb seq, Reg (Repeat n a) comb seq, Primitive comb)
  => {auto sIsSt: St s}
  -> {auto aIsSig: Sig a} 
  -> {auto similar: SameShape a s}
  -> (dat: comb () a)
  -> (en:  comb () (BitVec 1))
  -> seq (FifoSt n s) () (Repeat n a)
sInPOut dat en = 
  let sigOut: Sig (Repeat n a) = repeatSig n aIsSig
      stSt:  St (FifoSt n s) = fifoStIsSt {sIsSt=sIsSt} {n=n}
      similar': SameShape (Repeat n a) (FifoSt n s)
        = sameShape
  in do pre <- get
        update <- pure $ case n of
                           0 => pre
                           (S 0) => dat
                           (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} dat ?rhs
        nxt <- pure $ if_ en update pre
        pure pre
