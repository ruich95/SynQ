module Sym.Comb.ElabScripts.Lut

import Sym.Comb.CombPrimitive
import Language.Reflection
import Data.Nat
import Data.Vect
import Data.List1

import Data.BitVec
import Data.Signal
import Sym.Comb.ElabScripts.Unpack

public export
lutGen: (Primitive comb)
     => {idx_width: Nat}
     -> {data_width: Nat}
     -> (List1 $ BitVec data_width)
     -> Elab $ comb () (BitVec idx_width) -> comb () (BitVec data_width)
lutGen {idx_width} {data_width} xs
  = (lambda _ $ \idx => 
       do idx' <- unpack {n=idx_width} <*> pure idx 
          lutGen' idx_width data_width xs idx')
where
  hds: List1 a -> (n: Nat) -> Maybe $ List1 a
  hds (x ::: xs) 0 = Nothing
  hds (x ::: xs) (S 0) = Just $ x:::[]
  hds (x ::: []) (S (S k)) = Just $ (x ::: [])
  hds (x ::: (y :: xs)) (S (S k)) = 
    do tl <- hds (y:::xs) (S k)
       pure $ cons x tl
       
  tls: List1 a -> (n: Nat) -> Maybe $ List a
  tls (x ::: xs) 0 = Nothing
  tls (x ::: xs) (S 0) = Just xs
  tls (x ::: []) (S (S k)) = Just []
  tls (x ::: (y :: xs)) (S (S k)) = 
    tls (y:::xs) (S k)
  
  splitAt: List1 a -> (n: Nat) -> Maybe (List1 a, List a)
  splitAt xs n = pure MkPair <*> hds xs n <*> tls xs n
  
  lutGen': (idx_width: Nat)
        -> (data_width: Nat)
        -> (List1 $ BitVec data_width)
        -> Vect idx_width (comb () $ BitVec 1)
        -> Elab $ comb () (BitVec data_width)
  lutGen' 0 data_width xs [] = pure $ const $ head xs
  lutGen' (S 0) data_width xs (i :: []) = 
    case xs of 
      (x  ::: []) => pure $ const x
      (x1 ::: x2 :: xs) => pure $ mux21 i (const x2) (const x1)
  lutGen' (S (S k)) data_width xs (i1 :: i2 :: is) = 
    let partLen = (power 2 (S k))
    in case splitAt xs partLen of
         Just (hs, (t::ts)) => do
           t1 <- lutGen' (S k) data_width (t:::ts) (i2 :: is)
           t2 <- lutGen' (S k) data_width hs       (i2 :: is)
           pure $ mux21 i1 t1 t2
         _ => lutGen' (S k) data_width xs (i2 :: is)
