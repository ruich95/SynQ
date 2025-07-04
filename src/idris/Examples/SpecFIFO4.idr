import SynQ

import Sym.Comb.ElabScripts
import Data.Linear
import Examples.Sel
import System.File
import Data.List
import Data.Vect
import Language.Reflection

%hide Data.Linear.Interface.seq
-- %hide Prelude.(>>=)
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

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

dropLast4: (Comb comb, Primitive comb) 
  => {n:_} -> comb () (Repeat 4 $ BitVec n) 
  -> comb () (Repeat 3 $ BitVec n)
dropLast4 xs = prod (proj1 xs) (prod (proj1 $ proj2 xs) (proj1 $ proj2 $ proj2 xs))

sel4: (Comb comb, Primitive comb) 
  => {n:_} -> comb () (BitVec 3) 
  -> comb () (Repeat 4 $ BitVec n) 
  -> comb () (BitVec n)
sel4 idx vs = 
  mux21 (idx `eq` (const $ BV 0)) (proj1 vs)
 (mux21 (idx `eq` (const $ BV 1)) (proj1 $ proj2 vs) 
 (mux21 (idx `eq` (const $ BV 2)) (proj1 $ proj2 $ proj2 vs)
                                  (proj2 $ proj2 $ proj2 vs)))

FifoTySig: Type
FifoTySig = (BitVec 3, (Repeat 4 $ BitVec 32), (Repeat 4 $ BitVec 1))

FifoTySt: Type
FifoTySt = (LPair (!* BitVec 3) $ LPair (RepeatSt 4 $ (!* BitVec 32)) (RepeatSt 4 $ (!* BitVec 1)))

fwdComb: (Comb comb, Primitive comb) 
  => comb () FifoTySig -> comb () (BitVec 1, BitVec 32, BitVec 1)
fwdComb = \curSt => 
  let curCount = proj1 curSt 
      curData = proj1 $ proj2 curSt 
      curLast = proj2 $ proj2 curSt 
      pt      = lower' 3 {prf= lteSucc 3} (curCount `add` (const $ BV 7))
      validO  = not $ curCount `eq` (const $ BV 0)
      dataFn  = sel4 pt
      lastFn  = sel4 pt
  in prod validO (prod (dataFn curData) (lastFn curLast))

pack: (Comb comb, Primitive comb) 
  => comb () (BitVec 3) -> comb () (Repeat 4 $ BitVec 32) 
  -> comb () (Repeat 4 $ BitVec 1) -> (comb () $ BitVec 1)
  -> comb () ((BitVec 3, ((Repeat 4 $ BitVec 32), (Repeat 4 $ BitVec 1))), BitVec 1)
pack i x y r = prod (prod i $ prod x y) r

bwdComb: (Comb comb, Primitive comb) 
  => (validI: comb () (BitVec 1)) 
  -> (dataI: comb () (BitVec 32))
  -> (lastI: comb () (BitVec 1))
  -> (readyI: comb () (BitVec 1))
  -> (curSt: comb () FifoTySig) 
  -> comb () (FifoTySig, BitVec 1)
bwdComb validI dataI lastI readyI curSt = 
  let curCount = proj1 curSt 
      curData  = proj1 $ proj2 curSt 
      curLast  = proj2 $ proj2 curSt 
      produce  = (not $ curCount `eq` (const $ BV 0)) `and` (readyI)
      nxtCount = mux21 produce 
                   (lower' 3 {prf= lteSucc 3} (curCount `add` (const $ BV 7)))
                   curCount
      readyO   = (nxtCount `ltu` (const $ BV 4))
      en       = readyO `and` validI
      nxtCount = mux21 en (lower' 3 $ add nxtCount (const $ BV 1))
                       nxtCount
      updateD = if_ en (prod dataI $ dropLast4 curData) curData
      updateL = if_ en (prod lastI $ dropLast4 curLast) curLast
  in pack nxtCount updateD updateL readyO

%hide Prelude.(>>=)
-- %unhide SeqLib.(>>=)
mkFIFO: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (FifoTySig) comb seq)
  -> (validI: comb () (BitVec 1)) 
  -> (dataI:  comb () (BitVec 32)) 
  -> (lastI:  comb () (BitVec 1))
  -> (readyI: comb () (BitVec 1))
  -> seq FifoTySt () ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1)
mkFIFO (MkReg get set) validI dataI lastI readyI = 
  do curSt <- get
     out   <- pure $ fwdComb curSt
     bwdOut <- pure $ bwdComb validI dataI lastI readyI curSt
     _      <- set $ proj1 bwdOut
     pure $ prod out (proj2 bwdOut)

fifo: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (FifoTySig) comb seq)
  -> seq FifoTySt ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1) 
                  ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1)
fifo reg = abst $ \xin => 
  let validI = proj1 $ proj1 xin 
      dataI  = proj1 $ proj2 $ proj1 xin 
      lastI  = proj2 $ proj2 $ proj1 xin 
      readyI = proj2 xin
  in mkFIFO reg validI dataI lastI readyI
  
fifoFn: ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1) -> (1 _: FifoTySt) 
  -> LC FifoTySt ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1)
fifoFn = runSeq' $ fifo reg

unpack': (Comb comb, Primitive comb)
  => comb () (FifoTySig, ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1)) 
  -> (comb () FifoTySig, (comb () (BitVec 1), (comb () (BitVec 32), comb () (BitVec 1))), comb () (BitVec 1))
unpack' x = (proj1 x , (((proj1 $ proj1 $ proj2 x), ((proj1 $ proj2 $ proj1 $ proj2 x), proj2 $ proj2 $ proj1 $ proj2 x)), (proj2 $ proj2 x)))

bwd': (Comb comb, Primitive comb) 
  => -- (validI: comb () (BitVec 1)) 
  -- -> (dataI: comb () (BitVec 32))
  -- -> (lastI: comb () (BitVec 1))
  -- -> (readyI: comb () (BitVec 1))
  -- -> (curSt: comb () FifoTySig) 
  comb (FifoTySig, ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1)) 
       (FifoTySig, BitVec 1)
bwd' = 
  lam $ \x => 
    let (st, (validI, dataI, lastI), readyI) = unpack' x 
    in bwdComb validI dataI lastI readyI st

bwdFn: (d: BitVec 32) -> (l: BitVec 1) -> (ri: BitVec 1) -> FifoTySig -> (FifoTySig, BitVec 1)
bwdFn d l ri st = (runComb bwd') (st, ((BV {n=1} 1, (d, l)), ri)) -- (st, (BV 1, (d, l), ri))

getData0: (FifoTySig, a) -> BitVec 32
getData0 ((x, (y, z)), _) = fst y

getCount: LC FifoTySt a -> BitVec 3
getCount ((MkBang c # (vs # ls)) # _) = c

getCount': FifoTySt -> BitVec 3
getCount' (MkBang c # (vs # ls)) = c

getReady: (FifoTySig, BitVec 1) -> BitVec 1
getReady (_, x) = x

lemma1: (x: BitVec n) -> (y: BitVec n) 
  -> ((x == y) = True) -> x = y

andProp1: forall n. {x: BitVec n} -> (x `bvAnd` (BV {n=n} 0)) = (BV {n=n} 0)

andProp2: forall n. ((BV {n=n} 1) `bvAnd` (BV {n=n} 1)) = (BV {n=n} 1)

notProp1: bvNot (BV {n=1} 0) = BV {n=1} 1

ltuProp1: bvLtu {n=3} (BV 0) (BV 4) = BV 1
ltuProp2: bvLtu {n=3} (BV 0) (BV 5) = BV 1

ltu3Prop1: (x: BitVec 3) -> (y: BitVec 3)
  -> (x == BV 0) = False
  -> bvLtu x y = (bvLtu (bvSlice 0 3 (bvAdd x (BV 7)))
                        (bvSlice 0 3 (bvAdd y (BV 7))))

add3Prop1: bvSlice 0 3 (bvAdd {n=3} (BV 5) (BV 7)) = BV 4

prop1: (st: FifoTySig) 
  -> (d: BitVec 32) -> (l: BitVec 1) -- readyI = 0
  ->((getReady $ bwdFn d l (BV {n=1} 0) st) = (BV {n=1} 1))
  -> ((fst st) `bvLtu` (BV {n=3} 4)) = (BV {n=1} 1)
prop1 st d l prf with (fst st)
  prop1 st d l prf | c with (c == BV 0) proof p0
    prop1 st d l prf | c | False with (bvAnd {n=1} (bvNot (BV 0)) (BV 0)) proof p
      prop1 st d l prf | c | False | cond with (cond == (BV {n=1} 1))  proof p2
        prop1 st d l prf | c | False | cond | False = prf
        prop1 st d l prf | c | False | cond | True = 
          let prf1: (cond === BV {n=1} 0) = rewrite sym p in andProp1 {x=(bvNot (BV 0))}
              prf2: ((cond == BV {n=1} 1) = False) = rewrite prf1 in Refl
              prf3: (False = True) = rewrite sym prf2 in p2
          in absurd prf3
    prop1 st d l prf | c | True = rewrite lemma1 c (BV {n=3} 0) p0 in ltuProp1

prop3: (st: FifoTySig) 
  -> (d: BitVec 32) -> (l: BitVec 1) -- readyI = 0
  ->((getReady $ bwdFn d l (BV {n=1} 0) st) = (BV {n=1} 1))
  -> (getData0 $ bwdFn d l (BV {n=1} 0) st) = d
prop3 st d l prf = ?prop3_rhs

prop2: (st: FifoTySig) 
  -> (d: BitVec 32) -> (l: BitVec 1) -- readyI = 1
  ->((getReady $ bwdFn d l (BV {n=1} 1) st) = (BV {n=1} 1))
  -> ((fst st) `bvLtu` (BV {n=3} 5)) = (BV {n=1} 1)
prop2 st d l prf with (fst st == BV 0) proof p0
  prop2 st d l prf | False with (bvAnd {n=1} (bvNot (BV 0)) (BV 1)) proof p1
    prop2 st d l prf | False | cond = 
      let prf1: (bvAnd {n=1} (BV 1) (BV 1) = cond) 
            = rewrite sym p1 in rewrite notProp1 in Refl
          prf2: (cond = BV {n=1} 1) 
            = rewrite sym prf1 in andProp2
          prf3 = ltu3Prop1 (fst st) (BV 5) p0
      in rewrite sym prf in 
         rewrite prf2 in 
         rewrite prf3 in 
         rewrite add3Prop1 in Refl
  prop2 st d l prf | True = rewrite lemma1 (fst st) (BV {n=3} 0) p0 in ltuProp2
