module Examples.FIRwMult

import SynQ
import Impl.TAC
import Control.Monad.State
import Data.Vect

public export
interface Mult (0 comb: Type -> Type -> Type) where
  mult: {m: _} -> {n: _} 
     -> comb () (BitVec m) -> comb () (BitVec n)
     -> comb () (BitVec $ m + n)

%hide SeqLib.(>>=)

public export
Mult TACComb where
  mult (MkTACC x) (MkTACC y) = 
    MkTACC $ do x   <- x 
                y   <- y
                var <- genVar (BvTy $ m+n)
                let new_op = [MULT x.output y.output var]
                pure $ MkTAC1 U var (x.ops ++ y.ops ++ new_op)


%unhide SeqLib.(>>=)

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

multKs: (Comb comb, Primitive comb, Mult comb)
  => {n: Nat} -> {len: Nat} -> {coefW: Nat}
  -> (coefs: Vect len Bits64)
  -> (xs: comb () $ Repeat len $ BitVec n)
  -> comb () (Repeat len $ BitVec (coefW + n))
multKs [] xs = unit
multKs (c :: []) xs = mult (const $ BV (cast c)) xs
multKs {len=S $ S len} (c :: cs@(_ :: _)) xs = 
  let _  = repeatSig (S len) (BV {n})
      _  = repeatSig (S len) (BV {n=coefW+n})
      hd = proj1 xs 
      tl = proj2 xs
      y = mult (const $ BV (cast c)) hd
  in prod y (multKs cs tl)

neg: (Comb comb, Primitive comb) 
  => {n: Nat} -> {m: Nat}
  -> (k: Vect m Bool)
  -> (x: comb () (Repeat m $ BitVec n))
  -> comb () (Repeat m $ BitVec n)
neg {m = 0} [] x = x
neg {m = (S 0)} [y] x = 
  if y then adder' (not x) (const $ BV 1)
       else x
neg {m = (S (S k))} (y :: ys) x = 
  let _ = repeatSig (S k) $ BV {n=n}
      hd = if y then adder' (not $ proj1 x) 
                            (const $ BV 1)
                else proj1 x
      tl = neg ys (proj2 x)
  in prod hd tl

firState: (Seq comb seq, Primitive comb)
  => {auto aIsSig: Sig a}
  -> {auto sIsSt : St s}
  -> {auto similar: SameShape a s}
  -> (m: Nat)
  -> (init: comb () $ Repeat (S m) a)
  -> (1 reg: Reg (Repeat (S m) a) comb seq)
  -> LC (comb () (BitVec 1) -> comb () (BitVec 1) 
           -> comb () (Repeat (S m) a) 
           -> seq (RepeatSt (S m) s) () ())
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
mkFIR: (Seq comb seq, Primitive comb, Mult comb)
  => {m: Nat} -> {n: Nat} -> {coefW: Nat}
  -> (init: comb () $ Repeat (S m) $ BitVec n)
  -> (weights: Vect (S $ S m) Bits64)
  -> (sign:    Vect (S $ S m) Bool)
  -> (1 reg: Reg (Repeat (S m) (BitVec n)) comb seq)
  -> seq (RepeatSt (S m) (!* (BitVec n)))
         (BitVec 1, BitVec 1, BitVec n) (BitVec $ coefW+n)
mkFIR init weights sign reg = 
  let (firStSet # firStGet) = 
         firState {aIsSig=BV {n=n}} {sIsSt = LV {n=n}} m init reg 
      prf1 = repeatSt  {n=S m} {sIsSt=LV {n=n}}
      prf2 = repeatSig (S m) (BV {n=n})
  in abst $ \xin => 
       let rst  = proj1 xin
           skip = proj1 $ proj2 xin
           xin  = proj2 $ proj2 xin
       in do cur' <- firStGet
             let cur = prod xin cur'
                 weighted 
                   = neg (map not sign) 
                   $ multKs {coefW=coefW} weights cur
                 o = sum {m=S m} weighted
                 nxt = dropLast {aIsSig=BV {n=n}} {n=S m} cur
             _ <- firStSet rst skip nxt
             pure $ o

