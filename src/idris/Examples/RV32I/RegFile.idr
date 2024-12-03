module Examples.RV32I.RegFile

import SynQ

-- import Data.Linear

%hide Prelude.pure
-- %hide Data.Linear.seq

public export
repeat: (n: Nat) -> Type -> Type
repeat 0 ty = ()
repeat (S 0) ty = ty
repeat (S (S k)) ty = (ty, repeat (S k) ty)

-- lemma2: {n: _} -> {auto prf: LTE 1 n} -> repeat (S n) a = (a, repeat n a)
-- lemma2 {n = (S right)} {prf = (LTESucc x)} = Refl

lemma: {n:_} -> Sig a -> Sig $ repeat n a
lemma {n = 0} x = U
lemma {n = (S 0)} x = x
lemma {n = (S (S k))} x = P x (lemma x)

unpack: {comb:_} -> (Comb comb)
   => {auto aIsSig: Sig a} 
   -> {n:_} -> comb () (repeat (S n) a) 
   -> (comb () a, comb () (repeat n a))
unpack {n = 0} x = (x, unit)
unpack {n = (S k)} x = 
  let prf = lemma {n = S k} aIsSig 
  in (proj1 x, proj2 x)

take: {comb:_} -> (Comb comb)
   => {auto aIsSig: Sig a} 
   -> {n:_} -> (idx: Nat) 
   -> {auto prf: LT idx n} 
   -> comb () (repeat n a) -> comb () a
take 0 {prf=(LTESucc y)} x = fst $ unpack x
take (S k) {prf=LTESucc prf} x 
  = take k {prf=prf} (snd $ unpack x)

-- public export
repeatL: (n: Nat) -> Type -> Type
repeatL 0 ty = ()
repeatL (S 0) ty = (!* ty)
repeatL (S (S k)) ty = LPair (!* ty) (repeatL (S k) ty)

export
RegF: Type
RegF = repeatL 32 $ BitVec 32

repeatLBVIsSt: {m:_} -> (n: Nat) -> St $ repeatL n (BitVec m)
repeatLBVIsSt 0 = LU
repeatLBVIsSt (S 0) = LV
repeatLBVIsSt (S (S k)) = LP LV (repeatLBVIsSt (S k))


export
%hint
regfIsSt: St RegF
regfIsSt = repeatLBVIsSt {m=32} 32

-- prop: forall a. (n: Nat) -> SameShape (repeat n a) (repeatL n a)
-- prop 0 = U
-- prop (S 0) = BV
-- prop (S (S k)) = P BV (prop (S k))

update': {comb:_} -> (Primitive comb, Comb comb)
      => {n:_} 
      -> (idx: comb () (BitVec 5)) 
      -> (val: comb () (BitVec 32))
      -> (regs: comb () (repeat n $ BitVec 32))
      -> comb () (repeat n $ BitVec 32)
update' {n = 0}     _ _ regs = regs
update' {n = (S 0)} _ _ regs = regs
update' {n = (S (S k))} idx val regs = 
  let cur: comb () (BitVec 5) 
         = const $ fromInteger $ cast (S k)
      (cur_val, rest) = unpack regs
  in prod {bIsSig = lemma {n=S k} BV} 
          (mux21 (eq idx cur) val cur_val)
          (update' idx val rest)
          
update: {comb:_} -> (Primitive comb, Comb comb)
     => (idx: comb () (BitVec 5)) 
     -> (val: comb () (BitVec 32))
     -> (regs: comb () (repeat 32 $ BitVec 32))
     -> comb () (repeat 32 $ BitVec 32)        
update = update' {n=32}


wrRegF: {comb:_} -> {seq:_} 
     -> (Reg comb seq, Seq comb seq, 
         Primitive comb)
     => (idx: comb () (BitVec 5)) 
     -> (val: comb () (BitVec 32))
     -> seq RegF () ()
wrRegF idx val = (abst $ set) 
             =<< (pure $ lam $ update idx val) 
             =<< get 

regSel': {comb:_} -> (Primitive comb, Comb comb)
      => {n:_} -> {auto prf: LTE 1 n} 
      -> (idx: comb () (BitVec 5)) 
      -> (regs: comb () (repeat n $ BitVec 32))
      -> comb () (BitVec 32)
regSel' {n = (S 0)} {prf = (LTESucc prf')} idx regs = const 0
regSel' {n = (S (S k))} {prf = (LTESucc prf')} idx regs = 
  let cur: comb () (BitVec 5) 
         = const $ fromInteger $ cast (S k)
      (cur_val, rest) = unpack {n= S k} regs
  in mux21 (eq idx cur)
           cur_val
           (regSel' idx rest)

regSel: {comb:_} -> (Primitive comb, Comb comb)
  => comb () (BitVec 5) -> comb () (repeat 32 $ BitVec 32) 
  -> comb () (BitVec 32)
regSel idx regs = regSel' {n=32} idx regs

regSel'': {comb:_} -> (Primitive comb, Comb comb)
  => comb (BitVec 5, repeat 32 $ BitVec 32) (BitVec 32)
regSel'' = lam $ \xs => regSel' {n=32} (proj1 xs) (proj2 xs)


rdRegF': {comb:_} -> {seq:_} 
      -> (Reg comb seq, Primitive comb, 
          Seq comb seq)
      => (idx: comb () (BitVec 5)) 
      -> seq RegF () (BitVec 32)
rdRegF' idx = (pure (lam $ regSel idx)) =<< get

rdRegF: {comb:_} -> {seq:_} 
     -> (Reg comb seq, Primitive comb, 
         Seq comb seq)
     => (idx1: comb () (BitVec 5)) 
     -> (idx2: comb () (BitVec 5))
     -> seq RegF () (BitVec 32, BitVec 32)
rdRegF idx1 idx2 = applySnd (abst rdRegF')
               =<< (pure $ lam $ \x => prod x idx2)
               =<< (rdRegF' idx1)


public export
interface RegFile (comb: Type -> Type -> Type)
                  (seq: Type -> Type -> Type -> Type) where
  constructor MkRF
  1 read: (idx1: comb () (BitVec 5)) 
       -> (idx2: comb () (BitVec 5))
       -> seq RegF () (BitVec 32, BitVec 32)
       
  1 write: (idx: comb () (BitVec 5)) 
        -> (val: comb () (BitVec 32))
        -> seq RegF () ()
        
public export
regFile: {comb:_} -> {seq:_} 
      -> (Primitive comb, Reg comb seq, 
          Seq comb seq)
      => RegFile comb seq
regFile = MkRF rdRegF wrRegF

initRegF': {n:_} -> repeatL n (BitVec 32)
initRegF' {n = 0} = ()
initRegF' {n = (S 0)} = MkBang 64
initRegF' {n = (S (S k))} = (MkBang $ fromInteger $ cast $ (S k) + 100) # initRegF' {n=S k}

public export
initRegF: RegF
initRegF = initRegF' {n=32}

show': (n: Nat) -> (repeatL n (BitVec 32)) -> String
show' 0 x = "()"
show' (S 0) (MkBang x) = show x
show' (S (S k)) ((MkBang x) # xs) = "\{show' (S k) xs} | \{show x}"

public export
Show RegF where
 show r = show' 32 r

consume': (n: Nat) -> (1 _: repeatL n (BitVec 32)) -> ()
consume' 0 () = ()
consume' (S 0) (MkBang unrestricted) = ()
consume' (S (S k)) (MkBang _ # xs) = consume' (S k) xs

public export
Consumable RegF where
  consume = consume' 32
