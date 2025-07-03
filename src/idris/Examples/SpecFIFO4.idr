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
      pt      = lower' 3 (curCount `add` (const $ BV 7))
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
                   (lower' 3 (curCount `add` (const $ BV 7)))
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
  
getData0: LC FifoTySt a -> BitVec 32
getData0 ((c # ((MkBang v # vs) # ls)) # _) = v

getCount: LC FifoTySt a -> BitVec 3
getCount ((MkBang c # (vs # ls)) # _) = c

getCount': FifoTySt -> BitVec 3
getCount' (MkBang c # (vs # ls)) = c


getReadyO: LC FifoTySt ((BitVec 1, (BitVec 32, BitVec 1)), BitVec 1)
  -> (BitVec 1)
getReadyO (x # (_, r)) = r

lemma1: (x: BitVec n) -> (y: BitVec n) 
  -> ((x == y) = True) -> x = y

lemma2: (x: BitVec 1)
  -> ((x == BV {n=1} 1) = False) -> x = (BV {n=1} 0)
  
lemma3: forall x. (x `bvAnd` (BV {n=1} 0)) = (BV {n=1} 0)

prop1: (st: FifoTySt) 
  -> (d: BitVec 32) -> (l: BitVec 1) -> (ri: BitVec 1)
  -> ((getReadyO $ fifoFn (((BV {n=1} 1), (d, l)), ri) st) = (BV {n=1} 1))
  -> ((getCount' st) `bvLtu` (BV {n=3} 5)) = (BV {n=1} 1)
prop1 st d l ri prf with (ri == (BV {n=1} 1)) proof p
  prop1 st d l ri prf | True = ?rhs_t
  prop1 st d l ri prf | False = 
    let prf1 = lemma2 ri p
        -- prf2 = rewrite prf1 in prf
    in ?rhs_f
