module Data.BitVec2

import Data.Bool
import Data.Bool.Xor
import Data.Nat
import Data.Fin 

import Misc.Proofs

data BitVec: Nat -> Type where
  Nil: BitVec 0
  (::): Bool -> BitVec k -> BitVec (S k)
  
%name BitVec bv

show': BitVec n -> String
show' [] = ""
show' (False :: bv) = "0" ++ show' bv
show' (True  :: bv) = "1" ++ show' bv

[pretty] {n:_} -> Show (BitVec n) where 
  show [] = "<>"
  show bv@(_ :: _) = "\{show n}<\{show' bv}>0"

Show (BitVec n) where 
  show [] = "<>"
  show  bv@(_ :: _) = "<\{show' bv}>"

snoc: BitVec n -> Bool -> BitVec (S n)
snoc [] x = [x]
snoc (y :: bv) x = y :: snoc bv x

reverse: BitVec n -> BitVec n
reverse [] = []
reverse (x :: bv) = reverse bv `snoc` x

fromInteger: {n:_} -> Integer -> BitVec n
fromInteger {n = 0} i = []
fromInteger {n = (S k)} i = 
 if (i `mod` 2 == 1) 
 then (fromInteger (i `div` 2)) `snoc` True
 else (fromInteger (i `div` 2)) `snoc` False

(++): BitVec m -> BitVec n -> BitVec (m+n)
(++) [] bv1 = bv1
(++) (x :: bv) bv1 = x :: (bv ++ bv1)

map: (Bool -> Bool) -> BitVec n -> BitVec n
map f [] = []
map f (x :: bv) = (f x) :: map f bv

map2: (Bool -> Bool -> Bool) -> BitVec n -> BitVec n -> BitVec n
map2 f [] [] = []
map2 f (x :: bv1) (y :: bv2) = (f x y) :: map2 f bv1 bv2

scanr: (Bool -> Bool -> Bool) -> (ini: Bool) -> BitVec n -> BitVec n
scanr f ini [] = []
scanr f ini (y :: []) = [f ini y]
scanr f ini (y :: bv@(_ :: _)) with (scanr f ini bv)
  scanr f ini (y :: bv@(_ :: _)) | bv'@(acc :: _) = (f acc y) :: bv'

scan2r: (Bool -> Bool -> Bool -> Bool) 
  -> (ini: Bool) -> BitVec n -> BitVec n -> BitVec n
scan2r f ini [] [] = []
scan2r f ini (x :: []) (y :: []) = [f ini x y]
scan2r f ini (x :: bv1@(_ :: _)) (y :: bv2@(_ :: _)) = 
  case (scan2r f ini bv1 bv2) of 
    bv'@(acc :: _) => (f acc x y) :: bv'

and: BitVec n -> BitVec n -> BitVec n
and bv1 bv2 = map2 (\x,y => x && y) bv1 bv2

or: BitVec n -> BitVec n -> BitVec n
or bv1 bv2 = map2 (\x,y => x || y) bv1 bv2

xor: BitVec n -> BitVec n -> BitVec n
xor bv1 bv2 = map2 xor bv1 bv2

not: BitVec n -> BitVec n
not bv = map not bv

%spec cin
carry: (cin: Bool) -> BitVec n -> BitVec n -> BitVec (S n)
carry cin [] [] = [cin]
carry cin bv1@(_ :: _) bv2@(_ :: _) = 
  let pv = bv1 `xor` bv2 
      gv = bv1 `and` bv2 
  in (scan2r (\c, p, g => g || (c && p)) cin pv gv) `snoc` cin

%spec cin
fullAdd: (cin: Bool) -> BitVec n -> BitVec n -> (Bool, BitVec n)
fullAdd cin bv1 bv2 = 
  let cv = carry cin bv1 bv2 
      pv = False :: (bv1 `xor` bv2)
  in case pv `xor` cv of 
       (c :: bv) => (c, bv)

add: BitVec n -> BitVec n -> BitVec n
add bv1 bv2 = snd $ fullAdd False bv1 bv2

%spec n
zeroLike: BitVec n -> BitVec n
zeroLike [] = []
zeroLike (x :: bv) = False :: zeroLike bv

%spec n
oneLike: BitVec n -> BitVec n
oneLike [] = []
oneLike (x :: []) = [True]
oneLike (x :: bv@(_ :: _)) = False :: (oneLike bv)

complement: BitVec n -> BitVec n
complement bv = (not bv) `add` (oneLike bv)

Eq (BitVec n) where
  (==) [] [] = True
  (==) (x :: bv1) (y :: bv2) = (x == y) && (bv1 == bv2)

Ord (BitVec n) where
  (<) [] [] = False
  (<) (False :: bv1) (True  :: bv2) = True
  (<) (True  :: bv1) (False :: bv2) = False
  (<) (_ :: bv1) (_ :: bv2) = bv1 < bv2
  
ltu: BitVec n -> BitVec n -> Bool 
ltu = (<)

mult: BitVec n -> BitVec n -> BitVec n
mult bv1 bv2 = 
  if bv2 == (oneLike bv2) 
  then bv1
  else bv1 `add` (bv1 `mult` (bv2 `add` (complement $ oneLike bv2)))

test: (idx: Fin n) -> BitVec n -> Bool
test FZ (x :: []) = x
test FZ (x :: bv@(_ :: _)) = test FZ bv
test (FS x) (y :: bv) = test x bv

splitAt: (j: Nat) -> BitVec n 
  -> {auto 0 prf: n = j+k} -> (BitVec j, BitVec k)
splitAt 0 bv {prf} = rewrite sym prf in ([], bv)
splitAt (S j) bv {prf} = 
  let (x :: bv'): (BitVec $ (S j) + k) 
                = rewrite sym $ prf in bv 
      (bv1, bv2) = splitAt j bv'
  in (x::bv1, bv2)

lemma1: (m: Nat) -> (n: Nat) 
  -> (LTE m n) -> (k:Nat ** n = m + k)
lemma1 0 n LTEZero = (n ** Refl)
lemma1 (S m) (S n) (LTESucc x) = 
  let (k' ** prf') = lemma1 m n x
  in (k' ** cong S prf')

lemma1': (m: Nat) -> (n: Nat) 
  -> (k:Nat ** n = m + k)
  -> (LTE m n) 
lemma1' m n (0 ** snd) = 
  rewrite sym $ plusZeroRightNeutral m in 
  rewrite sym $ snd in lteRefl n
lemma1' 0 n ((S k) ** snd) = LTEZero
lemma1' (S j) n ((S k) ** snd) = 
  rewrite snd in 
  LTESucc $ ltePlus j

lemma2: (m: Nat) -> (n: Nat) -> (k: Nat)
  -> m = n + k
  -> (minus m n) = k
lemma2 0 0 0 prf = prf
lemma2 0 0 (S k) prf = absurd prf
lemma2 0 (S j) k prf = absurd prf
lemma2 (S j) 0 k prf = prf
lemma2 (S j) (S i) k prf = 
  lemma2 j i k $ eqPred prf
 
lemma4: (j: Nat) -> (k: Nat) -> LTE (j `minus` k) j
lemma4 0 k = LTEZero
lemma4 (S j) 0 = lteRefl (S j)
lemma4 (S j) (S k) = 
  lteRelaxRight (j `minus` k) j $ lemma4 j k

lemma3: (n: Nat) -> (m: Nat) -> (k: Nat)
  -> (prf1: LTE k n)
  -> (prf2: LTE m n)
  -> (prf3: n `minus` m = n `minus` k)
  -> m = k
lemma3 0 0 0 LTEZero LTEZero prf3 = Refl
lemma3 (S j) 0 0 prf1 prf2 prf3 = Refl
lemma3 (S j) 0 (S k) prf1 prf2 prf3 = 
  let prf4: (LTE (S j) j) = rewrite prf3 in lemma4 j k
  in case j of
       0     => absurd prf4
       (S i) => absurd prf4
lemma3 (S j) (S i) 0 prf1 prf2 prf3 = 
  let prf4: (LTE (S j) j) 
          = rewrite sym $ prf3 
            in lemma4 j i 
  in case j of
       0     => absurd prf4
       (S k) => absurd prf4
lemma3 (S j) (S i) (S k) (LTESucc prf1) (LTESucc prf2) prf3 = 
  cong S $ lemma3 j i k prf1 prf2 prf3

slice: {n: _} -> (lower: Nat) -> (upper: Nat) 
  -> {auto prf_upper: LTE upper n}
  -> {auto prf_lower: LTE lower upper}
  -> BitVec n -> BitVec (minus upper lower)
slice lower upper bv = 
  let prf1 = lteMinus upper n prf_upper
      0 (k ** prf2) = lemma1 (n `minus` upper) n prf1
      (_, bv1) = splitAt (n `minus` upper) bv {prf=prf2}
      0 prf3 = cong (\x => minus x k) prf2
      0 prf4: (minus n k = minus (plus k (minus n upper)) k) 
          = rewrite sym $ plusCommutative (n `minus` upper) k in prf3
      0 prf5: (minus n k = minus n upper) 
          = rewrite sym $ minusPlus {n=n `minus` upper} k in prf4
      0 prf2': (n = k + (n `minus` upper)) 
             = rewrite sym $ plusCommutative (n `minus` upper) k 
               in prf2
      0 prf6 = lemma1' k n ((n `minus` upper) ** prf2')
      0 prf7: (k = upper) = lemma3 n k upper prf_upper prf6 prf5
      bv1': (BitVec upper) = rewrite sym prf7 in bv1
      prf8 = lteMinus lower upper prf_lower
      0 (k ** prf9) = lemma1 (upper `minus` lower) upper prf8
      (bv2, _) = splitAt (upper `minus` lower) bv1' {prf=prf9}
  in bv2

tre: BitVec 32
tre = 65535
