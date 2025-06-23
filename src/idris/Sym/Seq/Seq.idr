module Sym.Seq.Seq

import Sym.Comb

import Data.BitVec
import Data.Signal
import Data.State

%hide Data.Linear.Interface.seq

public export
interface Comb comb 
  => Seq (0 comb: Type -> Type -> Type)
         (0 seq: Type -> Type -> Type -> Type) | seq where
  
  abst: {0 a:_} -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
     -> {auto sIsState: St s}
     -> (1 _: comb () a -> seq s () b) -> seq s a b
     
  pure: {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
     -> {auto sIsState: St s}
     -> comb a b -> seq s a b
     
  (=<<): {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
      -> {auto cIsSig: Sig c} -> {auto sIsState: St s} 
      -> (1 _: seq s b c) -> (1 _: seq s a b) 
      -> seq s a c 
     
  (<<<): {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
      -> {auto cIsSig: Sig c} -> {auto s1IsState: St s1}
      -> {auto s2IsState: St s2} 
      -> (1 _: seq s2 b c) -> (1 _: seq s1 a b)
      -> seq (LPair s1 s2) a c
