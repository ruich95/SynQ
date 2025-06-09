import Language.Reflection

import Sym.Comb

-- import Sym.CombPrimitive
-- import Sym.CombLib

import Impl.Compile
import Impl.Eval

import Data.Bits
import Data.Nat

import Data.BitVec
import Data.Signal
import Data.Vect
import Data.List1

UInt8: Type
UInt8 = BitVec 8

%language ElabReflection

fn: {comb:_} -> (Comb comb, Primitive comb)
   => comb (BitVec 1, BitVec 8, BitVec 8) (BitVec 8)
fn = lam $ \x => (mux21 (proj1 x) (proj1 $ proj2 x) (proj2 $ proj2 x))

-- fn in env with partial knowledge
fn': {comb:_} -> (Comb comb, Primitive comb)
   => comb (BitVec 8, BitVec 8) (BitVec 8)
fn' = (lam $ \x => app fn (prod (const 1) x))


term1: (BitVec 8, BitVec 8) -> (BitVec 8)
term1 = %runElab (genComb fn')

term2: (BitVec 8, BitVec 8) -> (BitVec 8)
term2 = runComb fn'


-- %hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

-- %hint
lteRefl: {n:Nat} -> LTE n n
lteRefl {n=0} = LTEZero
lteRefl {n=(S k)} = LTESucc (lteRefl)

0 minusZero: (n:Nat) -> n = minus n 0
minusZero 0 = Refl
minusZero (S k) = Refl

0 minusSucc: (n:Nat) -> 1 = minus (S n) n
minusSucc 0 = Refl
minusSucc (S k) = (minusSucc k)

unpack: (Primitive comb)
  => {n:_} -> comb () (BitVec n)
  -> Vect n (comb () $ BitVec 1)
unpack {n = 0} x = []
unpack {n = (S k)} x = 
  let b =  slice {prf_upper=lteRefl} {prf_lower=lteSucc k} k (S k) x 
      bs = slice {prf_upper=lteSucc k} 0 k x
  in (rewrite minusSucc k in b) :: unpack (rewrite minusZero k in bs)


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

lutGen': (Primitive comb)
     => (idx_width: Nat)
     -> (data_width: Nat)
     -> (List1 $ BitVec data_width)
     -> Vect idx_width (comb () $ BitVec 1)
     -> comb () (BitVec data_width)
lutGen' 0 data_width xs [] = const $ head xs
lutGen' (S 0) data_width xs (i :: []) = 
  case xs of 
    (x ::: []) => const x
    (x1 ::: x2 :: xs) => mux21 i (const x2) (const x1)
lutGen' (S (S k)) data_width xs (i1 :: i2 :: is) = 
  let partLen = (power 2 (S k))
  in if length xs <= partLen then lutGen' (S k) data_width xs (i2 :: is)
     else case splitAt xs partLen of
            Just (hs, []) => lutGen' (S k) data_width xs (i2 :: is)
            Just (hs, (t::ts)) => 
              mux21 i1 (lutGen' (S k) data_width (t:::ts) (i2 :: is))
                       (lutGen' (S k) data_width hs       (i2 :: is))
            _ => lutGen' (S k) data_width xs (i2 :: is)


lutGen: (Primitive comb)
     => {idx_width: Nat}
     -> {data_width: Nat}
     -> (List1 $ BitVec data_width)
     -> comb () (BitVec idx_width) 
     -> comb () (BitVec data_width)
lutGen {idx_width} {data_width} xs idx 
  = let idx' = unpack idx 
    in lutGen' idx_width data_width xs idx'
  
sine: List1 UInt8
sine = (BV 100) 
   ::: [BV 119, BV 138, BV 155] --, BV 170] -- , 183, 192, 198, 200, 198, 192, 183, 170,
                       -- 155, 138, 119, 100,  80,  61,  44,  29,  16,   7,   1,   0, 1,
                       -- 7,   16,  29,  44,  61,  80]

sineLut: (Comb comb, Primitive comb)
     => comb (BitVec 2) UInt8
sineLut = lam $ \idx => lutGen sine idx

t: (BitVec 2) -> UInt8
t = %runElab (genComb sineLut)

t1: (BitVec 2) -> UInt8
t1 = runComb sineLut
