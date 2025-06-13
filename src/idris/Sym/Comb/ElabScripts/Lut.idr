module Sym.Comb.ElabScripts.Lut

import Sym.Comb.Comb
import Sym.Comb.CombPrimitive
import Language.Reflection
import Data.Nat
import Data.Vect
import Data.List1

import Data.BitVec
import Data.Signal
import Sym.Comb.ElabScripts.Unpack

namespace FromList1
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

namespace FromVect
  public export
  lutGen: (Primitive comb)
    => {idxWidth: Nat}
    -> {dataWidth: Nat}
    -> {numEle: Nat}
    -> (Vect numEle $ BitVec dataWidth)
    -> {auto 0 p: LTE 1 numEle}
    -> Elab $ (comb () $ BitVec idxWidth)
           -> comb () (BitVec dataWidth)                  
  lutGen xs = lambda _ $ \is => 
    do is <- Unpack.unpack {n=idxWidth} <*> pure is
       (selGen' idxWidth numEle {p'=p} is (map const xs))
  where  
    split': (m:_) -> Vect (m + n) a -> Elab $ (Vect m a, Vect n a)
    split' 0 xs = pure ([], xs)
    split' (S k) (x :: xs) = 
      do (xs', ys) <- split' k xs
         pure $ (x::xs', ys)
    
    lemma': (x:Nat) -> (y: Nat) -> (0 _: LTE x y)
      -> x + (minus y x) = y
    lemma' 0 y LTEZero = minusZeroRight y
    lemma' (S x) (S y) (LTESucc z) = cong S $ lemma' x y z
          
    lemma: (x:Nat) -> (y: Nat) -> (0 _: LTE x y)
        -> (z: _ ** (x + z) = y)
    lemma x y z = (minus y x ** lemma' x y z)
    
    lemma3: (k: Nat) -> (n:Nat) -> LTE 1 n -> LTE 1 (n + k)
    lemma3 0 n x = rewrite plusZeroRightNeutral n in x
    lemma3 (S k) n x = rewrite plusCommutative n (S k) in LTESucc LTEZero
    
    lemma2: (n:Nat) -> LTE 1 (power 2 n)
    lemma2 0 = LTESucc LTEZero
    lemma2 (S j) = 
      let prf = lemma2 j 
      in lemma3 ((power 2 j)+0) (power 2 j) prf
    
    selGen': (idxWidth': Nat)
      -> (numInputs': Nat)
      -> {auto 0 p': LTE 1 numInputs'}
      -> (Vect idxWidth' $ comb () (BitVec 1))
      -> (Vect numInputs' $ comb () (BitVec dataWidth))
      -> Elab $ comb () (BitVec dataWidth)
    selGen' 0 (S n) {p' = (LTESucc p')} is (x :: _) = pure x
    selGen' (S k) (S n) {p' = (LTESucc p')} is ys with (power 2 k) proof prf1
      selGen' (S k) (S n) {p' = (LTESucc p')} is ys 
          | partLen with (partLen `lte` (S n)) proof prf2
        selGen' (S k) (S n) {p' = (LTESucc p')} (i::is) ys | partLen | False = 
          selGen' k (S n) is ys
        selGen' (S k) (S n) {p' = (LTESucc p')} (i::is) ys | partLen | True = 
          let prf2 = lteReflectsLTE partLen (S n) prf2 
              p1: LTE 1 partLen = rewrite sym $ prf1 in lemma2 k 
              (restLen ** prf2) = lemma partLen (S n) prf2
          in case restLen of 
               0 => selGen' k (S n) is ys
               (S j) => do (xs1, xs2) <- split' partLen {n=restLen} (rewrite prf2 in ys)
                           t1 <- (selGen' k  partLen is xs1)
                           t2 <- (selGen' k  (S j) is xs2)
                           pure $ mux21 i t2 t1
