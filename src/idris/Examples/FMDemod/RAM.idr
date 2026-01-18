module Examples.FMDemod.RAM

import SynQ

%hide Prelude.(>>=)
%hide Prelude.pure
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.(<<<)
%ambiguity_depth 8


export
RAMSt': Nat -> Nat -> Type
RAMSt' d w = Repeat d (BitVec w)

export
%hint
isSig: {auto m:_} -> {auto n:_} -> Sig $ RAMSt' m n
isSig {m = 0} = U
isSig {m = (S 0)} = BV
isSig {m = (S (S k))} = P BV $ isSig {m=S k} {n=n}

export
RAMSt: Nat -> Nat -> Type
RAMSt d w = RepeatSt d (!* BitVec w)

export
%hint
RAMStIsSt: {auto m:_} -> {auto n:_} -> St $ RAMSt m n
RAMStIsSt = repeatStIsSt

export
isSimilar: {auto m:_} -> {auto n:_} -> SameShape (RAMSt' m n) (RAMSt m n)
isSimilar {m = 0} = U
isSimilar {m = (S 0)} = BV
isSimilar {m = (S (S k))} = P BV $ isSimilar {m=S k} {n=n}

sel2: (Comb comb, Primitive comb)
  => {width: Nat} -> {depth: Nat} 
  -> (comb () $ BitVec 1)
  -> (comb () $ RAMSt' depth width)
  -> (comb () $ RAMSt' depth width)
  -> (comb () $ RAMSt' depth width)
sel2 {depth = 0} b x y  = x
sel2 {depth = (S 0)} b x y = mux21 b x y
sel2 {depth = (S (S k))} b x y = 
  let _  = isSig {m=(S k)} {n=width}
      x' = proj1 x
      xs = proj2 x 
      y' = proj1 y
      ys = proj2 y 
  in prod (mux21 b x' y') (sel2 b xs ys)

sel2': (Comb comb, Primitive comb)
  => {width: Nat} -> {depth: Nat}
  -> comb (BitVec 1, RAMSt' depth width, RAMSt' depth width) (RAMSt' depth width)
sel2' = let _  = isSig {m=depth} {n=width}
        in lam $ \x => sel2 {width=width} {depth=depth} (proj1 x) (proj1 $ proj2 x) (proj2 $ proj2 x)

ramCore: (Seq comb seq, Primitive comb)
  => {width: Nat} -> {depth: Nat} 
  -> (1 regs: Reg (RAMSt' depth width) comb seq)
  -> LC ((en: comb () $ BitVec 1) -> (dat: comb () $ RAMSt' depth width) 
           -> seq (RAMSt depth width) () ())
        (seq (RAMSt depth width) () (RAMSt' depth width))
ramCore (MkReg get set) = 
  let sig = isSig {m=depth} {n=width}
      st  = RAMStIsSt {m=depth} {n=width}
      similar = isSimilar {m=depth} {n=width}
  in (\en, dat => 
        do dat' <- get
           _    <- set (sel2' << (prod en (prod dat dat')))
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
  in (sel2' {depth=(S $ S k)}) 
        << (prod (eq idx (const $ BV $ cast (S k))) 
                 (prod (prod dat tl) 
                       (prod hd $ update idx dat tl)))

update': (Comb comb, Primitive comb)
  => {idxW: _} -> {width: _} -> {depth: _}
  -> comb (BitVec idxW, BitVec width, RAMSt' depth width) 
          (RAMSt' depth width)
update' = 
  let _ : Sig (RAMSt' depth width) = isSig {m=depth} {n=width}
  in lam $ \x => let idx = proj1 x 
                     dat = proj1 $ proj2 x
                     datas = proj2 $ proj2 x
                 in update idx dat datas

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

sel': (Comb comb, Primitive comb)
  => {idxW: _} -> {width: _} -> {depth: _}
  -> comb (BitVec idxW, RAMSt' depth width) (BitVec width)
sel' = 
  let _ : Sig (RAMSt' depth width) = isSig {m=depth} {n=width}
  in lam $ \x => let idx = proj1 x 
                     datas =  proj2 x
                 in sel idx datas

export
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
               st  = RAMStIsSt {m=depth} {n=width}
               similar = isSimilar {m=depth} {n=width}
           in (\raddr => 
                  do dats <- ramR'
                     pure $ sel' << prod raddr dats) 
            # (\en, waddr, dat => 
                  do dats <- ramR' 
                     let dats' = update' << (prod waddr $ prod dat dats)
                     ramW' en dats')
export
initRAMSt: (depth: Nat) -> (width: Nat) -> (BitVec width) -> RAMSt depth width
initRAMSt 0 width x = ()
initRAMSt (S 0) width x = MkBang x
initRAMSt (S (S k)) width x = MkBang x # initRAMSt (S k) width x

export
show': (depth: Nat) -> (width: Nat) -> RAMSt depth width -> String
show' 0 width x = "()"
show' (S 0) width x = show x
show' (S (S k)) width (x # y) = "\{show x} # \{show' (S k) width y}"

export
{depth: Nat} -> {width: Nat} ->  Show (RAMSt depth width) where
  show x = show' depth width x
