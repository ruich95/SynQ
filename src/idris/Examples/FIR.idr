module Examples.FIR

import SynQ
import Examples.TimesK
import Data.Vect

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide LState.(>>=)
%hide Prelude.(=<<)
%hide Prelude.pure

public export
RepeatSt: Nat -> (s: Type) -> Type
RepeatSt 0 s = ()
RepeatSt (S 0) s = s
RepeatSt (S (S k)) s = LPair s (RepeatSt (S k) s)

%hint
repeatSt: {auto sIsSt: St s} -> {n: Nat} -> St (RepeatSt n s)
repeatSt {n = 0} = LU
repeatSt {n = (S 0)} = sIsSt
repeatSt {n = (S (S k))} = LP sIsSt repeatSt

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

getLast: (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} 
  -> {n: _}
  -> comb () (Repeat (S n) a)
  -> comb () a
getLast {n = 0}     x = x
getLast {n = (S 0)} x = proj2 x
getLast {n = (S (S k))} x = 
  let _ = repeatSig (S $ S k) aIsSig
      x' = proj2 x 
  in getLast {n=S k} x'

%spec m
firState: (Seq comb seq, Primitive comb)
  => {auto aIsSig: Sig a}
  -> {auto sIsSt : St s}
  -> {auto similar: SameShape a s}
  -> (m: Nat)
  -> (init: comb () $ Repeat (S m) a)
  -> (1 reg: Reg (Repeat (S m) a) comb seq)
  -> LC (comb () (BitVec 1) -> comb () (BitVec 1) 
           -> comb () (Repeat (S m) a) -> seq (RepeatSt (S m) s) () ())
      $ seq (RepeatSt (S m) s) () (Repeat (S m) a)
firState 0 init (MkReg get set) = 
  (\rst, skip => set) # get
firState (S k) init (MkReg get set) = 
  let prf1 = repeatSt {sIsSt=sIsSt} {n=S $ S k}
      prf2 = repeatSig (S k) aIsSig
      prf3 = sameShape {similar=similar} {n=S $ S k}
  in (\rst, skip, xs => 
         do cur <- get 
            let nxt = if_ rst init $ if_ skip cur xs 
            set nxt) 
     # get

sum: (Comb comb, Primitive comb) 
  => {m: _} -> {n: _} 
  -> comb () (Repeat (S m) $ BitVec n)
  -> comb () (BitVec n)
sum x = 
  let all = repeatImpliesAll {a=BitVec n} m
      sig = repeatSig (S m) $ BV {n=n}
  in (reduce adder) << x

export
%spec m, weights, sign
mkFIR: (Seq comb seq, Primitive comb)
  => {m: Nat} -> {n: Nat} -> {maxSht: Nat}
  -> (init: comb () $ Repeat (S $ S m) $ BitVec $ S (maxSht+n))
  -> (weights: Vect (S $ S m) Nat)
  -> (sign: Vect (S $ S m) Bool)
  -> (1 reg: Reg (Repeat (S $ S m) (BitVec $ S (maxSht+n))) comb seq)
  -> seq (RepeatSt (S $ S m) (!* (BitVec $ S (maxSht+n))))
         (BitVec 1, BitVec 1, BitVec n) (BitVec $ S (maxSht+n))
mkFIR init weights sign reg = 
  let (firStSet # firStGet) = 
         firState {sIsSt = LV {n=S (maxSht+n)}} (S m) init reg 
      prf1 = repeatSt  {n=S m} {sIsSt=LV {n=S (maxSht+n)}}
      prf2 = repeatSig (S m)   (BV {n=S (maxSht+n)})
  in abst $ \xin => 
       let rst  = proj1 xin
           skip = proj1 $ proj2 xin
           xin  = proj2 $ proj2 xin
           weighted = neg (map not sign) $ timesKs xin weights maxSht
       in do cur <- firStGet 
             let o      = getLast  {n=S m} cur
                 stIni  = dropLast {n=S m} cur
                 wtTl   = proj2 weighted
                 stIni' = pointwise adder' stIni wtTl
                 st'    = prod (proj1 weighted) stIni'
             _ <- firStSet rst skip st'
             pure o
