module Data.BitVec2

import Data.Bool
import Data.Bool.Xor
import Data.Nat
import Data.Fin 

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

test: (idx: Fin n) -> BitVec n -> Bool
test FZ (x :: []) = x
test FZ (x :: bv@(_ :: _)) = test FZ bv
test (FS x) (y :: bv) = test x bv

splitAt: (j: Nat) -> BitVec n 
  -> {auto prf: n = j+k} -> (BitVec j, BitVec k)
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


tre: BitVec 32
tre = 65535
