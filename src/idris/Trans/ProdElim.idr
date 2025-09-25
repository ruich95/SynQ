module Trans.ProdElim 

import Sym.Comb
import Data.Signal
import Data.BitVec

public export
data PVal: (Type -> Type -> Type) 
        -> Type -> Type where
  V: comb () a -> PVal comb a
  P: PVal comb a -> PVal comb b -> PVal comb (a, b)

public export  
data PView: (Type -> Type -> Type) 
       -> Type -> Type -> Type where
  IsF: (PVal comb a -> PVal comb b) -> PView comb a b
  IsV: PVal comb a -> PView comb () a
  
  
export
fromVal: (Comb comb)
  => {auto aIsSig: Sig a}
  -> PVal comb a -> comb () a
fromVal (V x) = x
fromVal {aIsSig=P _ _} (P x y) = 
  prod (fromVal x) (fromVal y)

export
lower: (Comb comb)
  => {auto aIsSig: Sig a}
  -> PView comb () a -> PVal comb a
lower (IsF f) = f $ V unit
lower (IsV x) = x

export
(Comb comb) => Comb (PView comb) where
  lam f = IsF $ \x => lower $ f (IsV x)
  app (IsF f) e = 
    case lower e of
      (V x) => 
        IsV . V $ app (lam $ \x => fromVal $ f (V x)) x
      p@(P x y) => IsV . V . fromVal $ f p
  app x@(IsV _) e = x
  prod x y = IsV $ P (lower x) (lower y)
  proj1 x = 
    case lower x of
      (V x) => IsV . V $ proj1 x
      (P x y) => IsV x
  proj2 x = 
    case lower x of
      (V x) => IsV . V $ proj2 x
      (P x y) => IsV y
  unit = IsV $ V unit

export
lift: (Comb comb)
  => {auto aIsSig: Sig a}
  -> {auto bIsSig: Sig b}
  -> (comb () a -> comb () b)
  -> (PView comb () a -> PView comb () b)
lift f = IsV . V . f . fromVal . lower

export
lift2: (Comb comb)
  => {auto aIsSig: Sig a}
  -> {auto bIsSig: Sig b}
  -> {auto cIsSig: Sig c}
  -> (comb () a -> comb () b -> comb () c)
  -> (PView comb () a -> PView comb () b -> PView comb () c)
lift2 f x y = 
  IsV . V $ f (fromVal . lower $ x) 
              (fromVal . lower $ y)

export
(Comb comb, Primitive comb) => Primitive (PView comb) where
  const x     = IsV . V $ const x
  add x y     = lift2 add x y
  concat x y  = lift2 concat x y
  and x y     = lift2 and x y
  or x y      = lift2 or x y
  xor x y     = lift2 xor x y
  not x       = lift not x
  slice l u x = lift (slice l u) x
  eq x y      = lift2 eq x y
  ltu x y     = lift2 ltu x y
  lt x y      = lift2 lt x y
  mux21 b x y = lift2 (mux21 . fromVal . lower $ b) x y
  shiftLL k x = lift (shiftLL k) x
  shiftRL k x = lift (shiftRL k) x
  shiftRA k x = lift (shiftRA k) x

export
prodElim: (Comb comb)
  => {auto aIsSig: Sig a}
  -> {auto bIsSig: Sig b}
  -> PView comb a b -> comb a b
prodElim (IsF f) = lam $ \x => fromVal $ f (V x)
prodElim (IsV x) = fromVal x


-- prodElim: (Comb comb, Primitive comb)
--   => {auto aIsSig: Sig a}
--   -> {auto bIsSig: Sig b}
--   -> (forall comb' . (Comb comb', Primitive comb') => comb' a b) 
--   -> comb a b
-- prodElim f = prodElim' f
