module Sym.Seq.SeqLib

import Sym.Comb
import Sym.Seq.Seq
import Sym.Seq.SeqPrimitive

import Data.Signal
import Data.State

%hide Prelude.(>>=)

public export
applyFst: {comb: _} -> {seq: _} -> (Seq comb seq)
       => {auto sIsState: St s} -> {auto aIsSig: Sig a}
       -> {auto bIsSig: Sig b}  -> {auto cIsSig: Sig c}
       -> (1 _: seq s a b) -> seq s (a, c) (b, c)
applyFst fs = 
  abst $ \x => 
    (pure $ lam $ \y => prod y (proj2 x)) 
    =<< fs 
    =<< (pure $ proj1 x)

public export
applySnd: {comb: _} -> {seq: _} -> (Seq comb seq)
       => {auto sIsState: St s} -> {auto aIsSig: Sig a}
       -> {auto bIsSig: Sig b}  -> {auto cIsSig: Sig c}
       -> (1 _: seq s a b) -> seq s (c, a) (c, b)
applySnd fs = 
  abst $ \x => 
    (pure $ lam $ \y => prod (proj1 x) y) 
    =<< fs 
    =<< (pure $ proj2 x)

-- so that we can use do-notation
public export
(>>=): {comb:_} -> {seq:_}
  -> (Seq comb seq)
  => {auto sIsState: St s} 
  -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
  -> (1 _: seq s () a)
  -> (1 _: comb () a -> seq s () b) 
  -> seq s () b
(>>=) x f = (abst f) =<< x

public export
scan: {comb: _} -> {seq: _} -> (Seq comb seq)
  => (1 reg: Reg comb seq) 
  -> {auto sIsState: St s} -> {auto aIsSig: Sig a}
  -> {auto bIsSig: Sig b} -> {auto cIsSig: Sig c}
  -> {auto similar: SameShape c s}    
  -> (f: comb (a, c) (b, c)) -> seq s a b
scan (MkReg get set) f 
  = abst $ \xin => do cur_st  <- get {aIsSig=cIsSig}
                      res     <- pure $ app f (prod xin cur_st)
                      nxt_st  <- pure $ proj2 res
                      nxt_o   <- pure $ proj1 res
                      _       <- set nxt_st
                      pure $ nxt_o
