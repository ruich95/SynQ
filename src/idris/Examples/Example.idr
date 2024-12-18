import SynQ

import Sym.CombL as CL


import Data.Linear
import Data.Nat
-- import Data.State


%hide Prelude.(=<<)
-- %hide Prelude.pure


%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

adder: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n) (BitVec n)
adder = lam $ \x => lower' n (add (proj1 x) (proj2 x))

inc: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n) (BitVec n)
inc = lam $ \x => app adder (prod x $ const (BV 1))

idC: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n) (BitVec n)
idC = (lam id)

repeat: {comb:_}
  -> (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} -> (n: Nat) 
  -> comb a a -> comb a a
repeat 0 f = lam id
repeat (S k) f = f << (repeat k f)

-- %macro
-- t1: Elab $ (BitVec 8) -> (BitVec 8)
-- t1 = genComb $ repeat 4 inc

t2: (BitVec 8) -> (BitVec 8)
t2 = runComb $ repeat 4 inc

adderTree: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n, BitVec n, BitVec n) 
          (BitVec n)
adderTree = reduce adder 

balance4: {comb:_} -> {n:_} 
  -> (Comb comb)
  => comb (BitVec n, BitVec n, BitVec n, BitVec n)
          ((BitVec n, BitVec n), (BitVec n, BitVec n))
balance4 = lam $ \xs 
  => prod (prod (proj1 xs) (proj1 $ proj2 xs))
          (proj2 $ proj2 xs)
                             
adderTreeBalance: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n, BitVec n, BitVec n) 
          (BitVec n)
adderTreeBalance = (reduce adder) << balance4
    
unitSnd: {comb: _} -> (Comb comb)
      => {auto aIsSig: Sig a}
      -> (comb () a) -> (comb () (a, ()))
unitSnd x = prod x unit

unitFst: {comb: _} -> (Comb comb)
      => {auto aIsSig: Sig a}
      -> (comb () a) -> (comb () ((), a))
unitFst x = prod unit x

dly: {comb: _} -> {seq: _} -> (Seq comb seq)
  => (1 reg: Reg comb seq) 
  -> {auto sIsState: St s} -> {auto aIsSig: Sig a}
  -> {auto similar: SameShape a s}
  -> (seq s a a)
dly (MkReg get set) = 
  abst $ \x => (pure $ lam proj1) 
           =<< (applySnd $ set x) 
           =<< (pure $ lam $ \y => prod y unit)
           =<< get

dly8: {comb: _} -> {seq: _} -> (Seq comb seq)
  => (1 reg: Reg comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
dly8 (MkReg get set) = 
  abst $ \x => (pure $ lam proj1) 
           =<< (applySnd $ set x) 
           =<< (pure $ lam $ \y => prod y unit)
           =<< get
           
adder': {comb: _} -> (Comb comb, Primitive comb)
     => comb (BitVec 8, BitVec 8) (BitVec 8, BitVec 8)
adder' =  (lam $ \x => prod x x) << adder

addern: {comb: _} -> (Comb comb, Primitive comb)
     => comb (BitVec 8, BitVec 8) (BitVec 8, BitVec 8)
addern =  normalise adder'

acc: {comb: _} -> {seq: _} -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
acc reg = scan reg adder'

acc3: {comb: _} -> {seq: _} -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
acc3 reg = (pure $ lam id) =<< (acc reg)

adder2: {comb: _} -> (Comb comb, Primitive comb)
     => comb () (BitVec 8) 
     -> comb ((), BitVec 8) (BitVec 8, BitVec 8)
adder2 x = lam $ \y => (lam $ \x => prod x x) << adder << (prod x (proj2 y))

acc2': {comb: _} -> {seq: _} -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) 
  -> comb () (BitVec 8) -> seq (!* (BitVec 8)) () (BitVec 8)
acc2' reg x = scan reg (adder2 x)

acc2: {comb: _} -> {seq: _} -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
acc2 reg = abst $ \x => acc2' reg x

dlyc': {comb: _} -> (Comb comb)
  => comb () (BitVec 8)
  -> comb ((), BitVec 8) (BitVec 8, BitVec 8)
dlyc' x = lam $ \y => prod (proj2 y) x

dlyc: {comb: _} -> {seq: _} -> (Seq comb seq)
  => (1 reg: Reg comb seq) 
  -> comb () (BitVec 8)
  -> seq (!* (BitVec 8)) () (BitVec 8)
dlyc reg x = scan reg (dlyc' x)

dly2: {comb: _} -> {seq: _} -> (Seq comb seq)
  => (1 reg: Reg comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
dly2 reg = abst $ \x => dlyc reg x

sysFn: {comb: _} -> (Comb comb, Primitive comb)
  => comb (BitVec 8, BitVec 8) (BitVec 8, BitVec 8)
sysFn = lam $ \xy => prod (proj2 xy) (app adder xy)

double: {comb: _} -> (Comb comb, Primitive comb)
  => comb (BitVec 8) (BitVec 8)
double = lam $ \x => (app adder $ prod x x)

sys: {comb: _} -> {seq: _} -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
sys reg = (pure double) =<< (scan reg sysFn)

readIn: IO (BitVec 8)
readIn = do str <- getLine
            Prelude.pure $ BitVec.fromInteger $ cast str

main: IO ()
main = reactMealy readIn (runSeq $ sys reg) (MkBang 0)
