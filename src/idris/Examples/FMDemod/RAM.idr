module Examples.FMDemod.RAM

import SynQ
import Language.Reflection
import Data.Vect

%hide Prelude.(>>=)
%hide Prelude.pure
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.(<<<)
%ambiguity_depth 8

%language ElabReflection

export
RAMSt': Nat -> Nat -> Type
RAMSt' d w = Repeat d (BitVec w)

export
isSig: {auto m:_} -> {auto n:_} -> Sig $ RAMSt' m n

export
RAMSt: Nat -> Nat -> Type
RAMSt d w = RepeatSt d (BitVec w)

export
isSt: {auto m:_} -> {auto n:_} -> St $ RAMSt m n

export
isSimilar: {auto m:_} -> {auto n:_} -> SameShape (RAMSt' m n) (RAMSt m n)

ramCore: (Seq comb seq, Primitive comb)
  => {width: Nat} -> {depth: Nat} 
  -> (1 regs: Reg (RAMSt' depth width) comb seq)
  -> LC ((en: comb () $ BitVec 1) -> (dat: comb () $ RAMSt' depth width) 
           -> seq (RAMSt depth width) () ())
        (seq (RAMSt depth width) () (RAMSt' depth width))
ramCore (MkReg get set) = 
  let sig = isSig {m=depth} {n=width}
      st  = isSt  {m=depth} {n=width}
      similar = isSimilar {m=depth} {n=width}
  in (\en, dat => 
        do dat' <- get
           _ <- set (if_ en dat dat')
           pure unit)
   # get

prf1: (x: Nat) -> LTE x x
prf1 0 = LTEZero
prf1 (S k) = LTESucc $ prf1 k
                  
prf2: (x: Nat) -> LTE x (S x)
prf2 0 = LTEZero
prf2 (S k) = LTESucc $ prf2 k

prf3: (x: Nat) -> 1 = minus (S x) x
prf3 0 = Refl
prf3 (S k) = prf3 k

prf4: (x: Nat) -> x = minus x 0
prf4 0 = Refl
prf4 (S k) = Refl

update: (Comb comb, Primitive comb)
  => {idxW: _} -> {width: _} -> {depth: _}
  -> (idx: comb () $ BitVec idxW) 
  -> (dat: comb () $ BitVec width)
  -> (comb () $ RAMSt' depth width)
  -> (comb () $ RAMSt' depth width)
update {depth = 0} idx dat x = x
update {depth = (S 0)} idx dat x = mux21 (eq idx (const $ BV 0)) dat x
update {depth = (S (S k))} idx dat x = 
  let sig = isSig {m = S k}  {n = width}
      hd  = proj1 x 
      tl  = proj2 x
  in if_ (eq idx (const $ BV $ cast (S k))) 
         (prod dat tl)
         (prod hd $ update idx dat tl)

sel: (Comb comb, Primitive comb)
  => {idxW: _} -> {width: _} -> {depth: _}
  -> (idx: comb () $ BitVec idxW) 
  -> (comb () $ RAMSt' depth width)
  -> (comb () $ BitVec width)
sel {depth = 0} idx x = const $ BV 0
sel {depth = (S 0)} idx x = x
sel {depth = (S (S k))} idx x = 
  let sig = isSig {m = S k}  {n = width}
      hd  = proj1 x 
      tl  = proj2 x
  in if_ (eq idx (const $ BV $ cast (S k))) 
         hd (sel idx tl)

ram: (Seq comb seq, Primitive comb)
  => {addrW: Nat} -> {width: Nat} -> {depth: Nat} 
  -> (1 regs: Reg (RAMSt' depth width) comb seq)
  -> LPair ((raddr: comb () $ BitVec addrW) 
         -> seq (RAMSt depth width) 
                () (BitVec width))
           ((en: comb () $ BitVec 1) 
         -> (waddr: comb () $ BitVec addrW) 
         -> (dat: comb () $ BitVec width) 
         -> seq (RAMSt depth width) () ())
ram regs = let (ramW' # ramR') = ramCore regs 
               sig = isSig {m=depth} {n=width}
               st  = isSt  {m=depth} {n=width}
               similar = isSimilar {m=depth} {n=width}
           in (\raddr => 
                  do dats <- ramR'
                     pure $ sel raddr dats) 
            # (\en, waddr, dat => 
                  do dats <- ramR' 
                     let dats' = update waddr dat dats
                     ramW' en dats')
