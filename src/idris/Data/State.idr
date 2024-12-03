module Data.State

import public Data.Linear

import Data.BitVec
import Data.Signal

%hide Linear.seq

public export
data St: Type -> Type where
  LU: St ()
  LP: (st1: St a) -> (st2: St b) -> St $ LPair a b
  LV: {n: _} -> St $ !* (BitVec n)

public export
data SameShape: Type -> Type -> Type where
  U: SameShape () ()
  BV: SameShape a (!* a)
  P:  (prfa: SameShape a b)
   -> (prfb: SameShape c d)
   -> SameShape (a, c) (LPair b d)

export
sameShapeTrans: (p1: SameShape a s) -> (p2: SameShape b s) 
             -> a = b
sameShapeTrans U U = Refl
sameShapeTrans BV BV = Refl
sameShapeTrans (P p11 p12) (P p21 p22) = 
  let p1' = sameShapeTrans p11 p21 
      p2' = sameShapeTrans p12 p22 
  in rewrite p1' in rewrite p2' in Refl


export
stToSig: (1 st: s) -> {auto sIsState: St s}
      -> {auto aIsSig: Sig a}
      -> {auto similar: SameShape a s}
      -> (!* a)
stToSig () {similar = U} = MkBang ()
stToSig x {similar = BV} = x
stToSig (x # y) {sIsState = (LP st1 st2)} 
                {aIsSig = (P p1 p2)} 
                {similar = (P prfa prfb)} 
  = let (MkBang x') = stToSig x 
        (MkBang y') = stToSig y 
    in MkBang (x', y')

public export
sigToSt: a -> {auto sIsState: St s}
  -> {auto aIsSig: Sig a}
  -> {auto similar: SameShape a s} -> s
sigToSt x {similar = U} = x
sigToSt x {similar = BV} = MkBang x
sigToSt (x, y) {sIsState = (LP st1 st2)} {aIsSig = (P p1 p2)} {similar = (P prfa prfb)} 
  = sigToSt x # sigToSt y
  
export
stConsume: (1 _: s) -> {auto sIsSig: St s} 
  -> ()
stConsume x {sIsSig = LU} = x
stConsume (x # y) {sIsSig = (LP st1 st2)} = 
  let () = stConsume x
      () = stConsume y
  in ()
stConsume (MkBang _) {sIsSig = LV} = ()

--   U: SameShape (Sig ()) (St ())
--   P:  (prfa: SameShape (Sig a) (St a))
--    -> (prfb: SameShape (Sig b) (St b))
--    -> SameShape (Sig (a, b)) (St $ LPair a b)
--   V:  {n:_} -> SameShape (Sig $ BitVec n) (St $ BitVec n)
   
-- tmp: (1 _: a) -> (1 _: b) 
--   -> {p1: St a}
--   -> {p2: St b}
--   -> Res (St $ LPair a b) (const $ LPair a b)
-- tmp x y = LP p1 p2 # (x # y)

