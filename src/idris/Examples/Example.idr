import SynQ

import Sym.CombL as CL
import Impl.TAC

import Data.Linear
import Data.Nat
-- import Data.State


%hide Prelude.(=<<)
%hide CombLib.adder
%hide Linear.seq
-- %hide Prelude.pure


%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

adder: {n:_} -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n) (BitVec n)
adder = lam $ \x => lower' n (add (proj1 x) (proj2 x))

ttt: {n:_} -> (Comb comb, Primitive comb)
  => comb () (BitVec n)
ttt = app adder (prod (const $ BV 0) (const $ BV 1))

inc: {n:_} -> (Comb comb, Primitive comb)
  => comb (BitVec n) (BitVec n)
inc = lam $ \x => app adder (prod x $ const (BV 1))

swap: {n:_} -> (Comb comb)
  => comb (BitVec n, BitVec n) (BitVec n, BitVec n)
swap = lam $ \x => prod (proj2 x) (proj1 x)

idC: {n: _} -> (Comb comb, Primitive comb)
  => comb (BitVec n) (BitVec n)
idC = (lam id)

repeat: (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} -> (n: Nat) 
  -> comb a a -> comb a a
repeat 0 f = lam id
repeat (S k) f = f << (repeat k f)

-- %macro
-- t1: Elab $ (BitVec 8) -> (BitVec 8)
-- t1 = genComb $ repeat 4 inc

t2: (BitVec 8) -> (BitVec 8)
t2 = runComb $ repeat 4 inc

adderTree: {n: _} -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n, BitVec n, BitVec n) 
          (BitVec n)
adderTree = reduce adder 

balance4: {n:_} -> (Comb comb)
  => comb (BitVec n, BitVec n, BitVec n, BitVec n)
          ((BitVec n, BitVec n), (BitVec n, BitVec n))
balance4 = lam $ \xs 
  => prod (prod (proj1 xs) (proj1 $ proj2 xs))
          (proj2 $ proj2 xs)
                             
adderTreeBalance: {n:_} -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n, BitVec n, BitVec n) 
          (BitVec n)
adderTreeBalance = (reduce adder) << balance4
    
unitSnd: (Comb comb)
      => {auto aIsSig: Sig a}
      -> (comb () a) -> (comb () (a, ()))
unitSnd x = prod x unit

unitFst: (Comb comb)
      => {auto aIsSig: Sig a}
      -> (comb () a) -> (comb () ((), a))
unitFst x = prod unit x

dly: (Seq comb seq)
  => (1 reg: Reg a comb seq) 
  -> {auto sIsState: St s} -> {auto aIsSig: Sig a}
  -> {auto similar: SameShape a s}
  -> (seq s a a)
dly (MkReg get set) = 
  abst $ \x => (pure $ lam proj1) 
           =<< (applySnd $ set x) 
           =<< (pure $ lam $ \y => prod y unit)
           =<< get

dly8: (Seq comb seq)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
dly8 (MkReg get set) = 
  abst $ \x => (pure $ lam proj1) 
           =<< (applySnd $ set x) 
           =<< (pure $ lam $ \y => prod y unit)
           =<< get
           
adder': (Comb comb, Primitive comb)
     => comb (BitVec 8, BitVec 8) (BitVec 8, BitVec 8)
adder' =  (lam $ \x => prod x x) << adder

-- addern: (Comb comb, Primitive comb)
--      => comb (BitVec 8, BitVec 8) (BitVec 8, BitVec 8)
-- addern =  normalise adder'

acc: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
acc reg = scan reg adder'

acc3: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
acc3 reg = (pure $ lam id) =<< (acc reg)

adder2: (Comb comb, Primitive comb)
     => comb () (BitVec 8) 
     -> comb ((), BitVec 8) (BitVec 8, BitVec 8)
adder2 x = lam $ \y => (lam $ \x => prod x x) << adder << (prod x (proj2 y))

acc2': (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> comb () (BitVec 8) -> seq (!* (BitVec 8)) () (BitVec 8)
acc2' reg x = scan reg (adder2 x)

acc2: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
acc2 reg = abst $ \x => acc2' reg x

dlyc': (Comb comb)
  => comb () (BitVec 8)
  -> comb ((), BitVec 8) (BitVec 8, BitVec 8)
dlyc' x = lam $ \y => prod (proj2 y) x

dlyc: (Seq comb seq)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> comb () (BitVec 8)
  -> seq (!* (BitVec 8)) () (BitVec 8)
dlyc reg x = scan reg (dlyc' x)

dly2: (Seq comb seq)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
dly2 reg = abst $ \x => dlyc reg x

dly3: (Seq comb seq)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
dly3 (MkReg get set) = 
  abst $ \xin => do o <- get 
                    _ <- set xin
                    pure o

dly4: (Seq comb seq)
  => (1 reg: Reg (BitVec 8, BitVec 8) comb seq) 
  -> seq (LPair (!* (BitVec 8)) (!* (BitVec 8))) (BitVec 8) (BitVec 8)
dly4 (MkReg get set) = 
  abst $ \xin => do xs <- get 
                    let o = proj1 xs 
                        nxt = prod (proj2 xs) xin 
                    _ <- set nxt
                    Seq.pure o 

sysFn:(Comb comb, Primitive comb)
  => comb (BitVec 8, BitVec 8) (BitVec 8, BitVec 8)
sysFn = lam $ \xy => prod (proj2 xy) (app adder xy)

double: (Comb comb, Primitive comb)
  => comb (BitVec 8) (BitVec 8)
double = lam $ \x => (app adder $ prod x x)

sys:  (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 8) comb seq) 
  -> seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
sys reg = (pure double) =<< (scan reg sysFn)

readIn: IO (BitVec 8)
readIn = do str <- getLine
            Prelude.pure $ BitVec.fromInteger $ cast str

main: IO ()
main = reactMealy readIn (runSeq $ sys reg) (MkBang 0)
