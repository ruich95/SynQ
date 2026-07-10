||| Structural operations on bit vectors (concatenation, spliting, slicing, etc.)
module Data.BitVec.StructuralOps

import Data.BitVec.Base
import Data.Nat
import Syntax.PreorderReasoning

%default total

||| Concatenate two bit vectors, with the first vector as MSBs and the second vector as LSBs.
||| Example: (MSB True <: False) ++ (MSB False <: True) ==> MSB True <: False <: False <: True
public export
(++) : BitVec m -> BitVec n -> BitVec (m + n)
(++) {n = 1} bs1 (MSB x) = convertWidth (plusCommutative 1 m) $ bs1 <: x
(++) {n = (S n)} bs1 (msbs <: lsb) = 
  convertWidth (plusCommutative (S n) m) 
    $ (convertWidth (plusCommutative m n) $ bs1 ++ msbs) <: lsb

||| Get LSBs of a bit vector until (exclusive) the `k`-th (0-indexed) bit.
export
lsbsUntil : (k : Nat) 
  -> {auto prfLower : GT k 0} -> {auto prfUpper : LT k n}
  -> (bv : BitVec n) -> BitVec k
lsbsUntil 0 bv          = absurd prfLower
lsbsUntil (S k) (MSB x) = absurd prfUpper
lsbsUntil (S 0) (msbs <: lsb) = MSB lsb
lsbsUntil (S (S k)) {prfUpper = (LTESucc z)} (msbs <: lsb) = (lsbsUntil (S k) msbs) <: lsb

||| Get MSBs of a bit vector from (inclusive) the `k`-th (0-indexed) bit.
export
msbsFrom : (k : Nat) 
  -> {auto prfUpper : LT k n}
  -> (bv : BitVec n) -> BitVec (n `minus` k)
msbsFrom 0 bv = convertWidth (sym $ minusZeroRight n) bv
msbsFrom (S k) (MSB x) = absurd prfUpper
msbsFrom {n = S n} (S k) {prfUpper = (LTESucc z)} (msbs <: lsb) = msbsFrom k msbs

||| Split a bit vector at the `k`-th (0-indexed) bit.
export
splitAt : (k : Nat) 
  -> {auto prfLower : GT k 0} -> {auto prfUpper : LT k n}
  -> (bv : BitVec n) -> (BitVec (n `minus` k), BitVec k)
splitAt k bv = (msbsFrom k bv, lsbsUntil k bv)

public export
getMSB : (bv : BitVec n) -> Bool
getMSB (MSB x) = x
getMSB (msbs <: lsb) = getMSB msbs

export
mapCps : {0 r : Type} -> (f : Bool -> Bool) -> (bs : BitVec n) -> (BitVec n -> r) -> r
mapCps f (MSB b)  k = k (MSB (f b))
mapCps f (bs <: b) k = mapCps f bs (\bs' => k (bs' <: f b))

||| `map` implemented in the CPS style.
public export
map : (f : Bool -> Bool) -> (bs : BitVec n) -> BitVec n
map f bs = mapCps f bs id

export
zipWithCps : {0 r : Type} -> (f : Bool -> Bool -> Bool) 
  -> (bs1 : BitVec n) -> (bs2 : BitVec n) -> (BitVec n -> r) -> r
zipWithCps f (MSB x) (MSB y) g = g (MSB (f x y))
zipWithCps f (MSB x) (msbs <: lsb) g impossible
zipWithCps f (msbs <: lsb) (MSB y) g impossible
zipWithCps f (msbs <: lsb) (msbs2 <: lsb2) g = zipWithCps f msbs msbs2 (\bs' => g (bs' <: f lsb lsb2))

||| `zipWith` implemented in the CPS style.
public export
zipWith : (f : Bool -> Bool -> Bool) -> (bs1 : BitVec n) -> (bs2 : BitVec n) -> BitVec n
zipWith f bs1 bs2 = zipWithCps f bs1 bs2 id

public export
fold : (f : a -> Bool -> a) -> (init : a) -> (bs : BitVec n) -> a
fold f init (MSB x) = f init x
fold f init (msbs <: lsb) = fold f (f init lsb) msbs

export
scanCPS : (f : Bool -> Bool -> Bool) -> (init : Bool) -> (bs : BitVec n) -> (BitVec n -> r) -> r
scanCPS f init (MSB x) k = k $ MSB (f init x)
scanCPS f init (msbs <: lsb) k = scanCPS f (f init lsb) msbs (\bs' => k (bs' <: f init lsb))

public export
scan : (f : Bool -> Bool -> Bool) -> (init : Bool) -> (bs : BitVec n) -> BitVec n
scan f init bs = scanCPS f init bs Prelude.id

||| Properties of structural operations on bit vectors.
namespace Properties
    %default total

    export
    0 
    concatLemma : (xs : BitVec m) -> (ys : BitVec n) -> (z : Bool)
        -> (convertWidth (sym (plusSuccRightSucc m n)) $ xs ++ (ys <: z)) = ((xs ++ ys) <: z)
    concatLemma xs ys z = rewrite plusCommutative n m in Refl

    export
    0 
    lsbsUntilLemma : (k : Nat) -> (msbs : BitVec n) -> (lsb : Bool) 
        -> (prfLower : GT k 0) -> (prfUpper : LT k n)
        -> (lsbsUntil (S k) {prfUpper = LTESucc prfUpper} (msbs <: lsb)) = ((lsbsUntil k msbs) <: lsb)
    lsbsUntilLemma 0 msbs lsb prfLower prfUpper = absurd prfLower
    lsbsUntilLemma (S k) msbs lsb (LTESucc LTEZero) prfUpper = Refl

    0
    lemma1 : (n : Nat) -> BitVec n -> LTE 1 n
    lemma1 1 (MSB x) = LTESucc LTEZero
    lemma1 (S n) (msbs <: lsb) = LTESucc LTEZero

    0
    lemma_convertWidth_cons : (p : m = n) -> (msbs : BitVec m) -> (lsb : Bool)
      -> (convertWidth p msbs) <: lsb = convertWidth (cong S p) (msbs <: lsb)
    lemma_convertWidth_cons Refl msbs lsb = Refl

    0
    lemma_plus_SS : (m, k : Nat) -> m + (S (S k)) = S (S (m + k))
    lemma_plus_SS m k = 
      Calc $ 
        |~ (m + (S (S k))) 
        ~~ S (S (k + m)) ...(plusCommutative m (S $ S k))
        ~~ S (S (m + k)) ...(rewrite plusCommutative k m in Refl)

    export
    0 
    concatPreserveLSBs : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
        -> (prfLower : GT n 0) -> (prfUpper : LT n (m + n))
        -> lsbsUntil n {prfLower = prfLower} {prfUpper = prfUpper} (xs ++ ys) = ys
    concatPreserveLSBs m 0 xs ys prfLower prfUpper = absurd (lemma1 0 ys)
    concatPreserveLSBs m (S 0) xs (MSB x) prfLower prfUpper = Refl
    concatPreserveLSBs m (S 0) xs (msbs <: lsb) prfLower prfUpper = absurd msbs
    concatPreserveLSBs m (S (S k)) xs (msbs <: lsb) prfLower prfUpper 
      with (replace {p = \t => LT (S (S k)) t} (lemma_plus_SS m k) prfUpper)
      concatPreserveLSBs m (S (S k)) xs (msbs <: lsb) prfLower prfUpper | (LTESucc (LTESucc z)) 
        = cong (\v => v <: lsb) 
            (concatPreserveLSBs m (S k) xs msbs (LTESucc LTEZero) 
              (replace {p = \t => LTE (S (S k)) t} (plusSuccRightSucc m k) (LTESucc z)))

    0 
    lemma_minus_add : (m, k : Nat) -> minus (m + k) k = m
    lemma_minus_add m 0 =
      trans (cong (\t => minus t 0) (plusZeroRightNeutral m))
            (minusZeroRight m)
    lemma_minus_add m (S k) =
      trans (cong (\t => minus t (S k)) (sym (plusSuccRightSucc m k)))
            (lemma_minus_add m k)

    0 
    lemma_minus_eq : (m, k : Nat) -> minus (m + (S k)) (S k) = minus (m + k) k
    lemma_minus_eq m k = trans (lemma_minus_add m (S k)) (sym (lemma_minus_add m k))

    export
    0 
    concatPreserveMSBs : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
        -> (prfUpper : LT n (m + n))
        -> msbsFrom n {prfUpper = prfUpper} (xs ++ ys) 
         = convertWidth (rewrite plusCommutative m n in sym (minusPlus {n=m} n)) xs
    concatPreserveMSBs m 0 xs ys prfUpper = absurd (lemma1 0 ys)
    concatPreserveMSBs m (S 0) xs (MSB x) prfUpper 
      with (replace {p = \t => LT 1 t} (sym (plusSuccRightSucc m 0)) prfUpper)
      concatPreserveMSBs m (S 0) xs (MSB x) prfUpper | (LTESucc z) = Refl
    concatPreserveMSBs m (S k) xs (msbs <: lsb) prfUpper 
      with (replace {p = \t => LT (S k) t} (sym (plusSuccRightSucc m k)) prfUpper)
      concatPreserveMSBs m (S k) xs (msbs <: lsb) prfUpper | (LTESucc z) = 
        rewrite lemma_minus_eq m k in
        concatPreserveMSBs m k xs msbs z

    export
    0
    concatSplitIsoFrom : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
        -> (prfLower : GT n 0) -> (prfUpper : LT n (m + n))
        -> (splitAt n {prfLower = prfLower} {prfUpper = prfUpper} . (uncurry (++))) (xs, ys)
         = (convertWidth (rewrite plusCommutative m n in sym (minusPlus {n=m} n)) xs, ys)
    concatSplitIsoFrom m n xs ys prfLower prfUpper = 
        let prf1 = concatPreserveLSBs m n xs ys prfLower prfUpper
            prf2 = concatPreserveMSBs m n xs ys prfUpper
        in Calc $ 
            |~ (msbsFrom n (xs ++ ys), lsbsUntil n (xs ++ ys)) 
            ~~ (msbsFrom n (xs ++ ys), ys)                                                    ...(rewrite prf1 in Refl) 
            ~~ (convertWidth (rewrite plusCommutative m n in sym (minusPlus {n=m} n)) xs, ys) ...(rewrite prf2 in Refl) 

    0
    lemma_plus_minus_lte : (k, n : Nat) -> (prf : LTE (S k) n) -> S (k + minus n (S k)) = n
    lemma_plus_minus_lte k n prf =
      let prfMinus = plusMinusLte (S k) n prf
      in Calc $
        |~ S (k + minus n (S k))
        ~~ S (minus n (S k) + k)     ...(cong S (plusCommutative k (minus n (S k))))
        ~~ minus n (S k) + S k       ...(plusSuccRightSucc (minus n (S k)) k)
        ~~ n                          ...(prfMinus)

    export
    0
    concatSplitIsoTo : (k , n : Nat) -> (xs : BitVec n)
        -> (prfLower : GT k 0) -> (prfUpper : LT k n)
        -> ((uncurry (++)) . (splitAt k {prfLower = prfLower} {prfUpper = prfUpper})) xs
         = convertWidth (sym (plusMinusLte k n (lteSuccLeft prfUpper))) xs
    concatSplitIsoTo 0 _ _ prfLower _ = absurd (succNotLTEzero prfLower)
    concatSplitIsoTo (S k) 1 (MSB x) prfLower (LTESucc y) = absurd (succNotLTEzero y)
    concatSplitIsoTo (S 0) (S n) (msbs <: lsb) prfLower (LTESucc z) = 
      rewrite minusZeroRight n in
      Refl
    concatSplitIsoTo (S (S k)) (S n) (msbs <: lsb) prfLower (LTESucc x)
      = let rec = concatSplitIsoTo (S k) n msbs (LTESucc LTEZero) x
        in rewrite rec in 
           rewrite lemma_plus_minus_lte k n (lteSuccLeft x) in Refl
    
    
    0
    lemma_cw_irrel : (0 p, q : m = n) -> (bv : BitVec m) -> convertWidth p bv = convertWidth q bv
    lemma_cw_irrel Refl Refl bv = Refl

    export
    0
    cancelSplit : (m , n : Nat) -> (xs : BitVec m) -> (ys : BitVec n)
        -> (prfLower : GT n 0) -> (prfUpper : LT n (m + n))
        -> ((uncurry (++)) . splitAt n {prfLower = prfLower} {prfUpper = prfUpper}) ((uncurry (++)) (xs, ys))
         = (uncurry (++)) (convertWidth (sym (lemma_minus_add m n)) xs, ys)
    cancelSplit m n xs ys prfLower prfUpper = 
      rewrite concatPreserveLSBs m n xs ys prfLower prfUpper in
      rewrite concatPreserveMSBs m n xs ys prfUpper in
      cong (\v => v ++ ys) 
        (lemma_cw_irrel (rewrite plusCommutative m n in sym (minusPlus {n=m} n)) 
                        (sym (lemma_minus_add m n)) xs)

    ||| Lemma: appending a bit after `mapCps` with continuation `k` is the same as threading the append through the continuation.
    export
    0
    mapCpsAppendGen : (f : Bool -> Bool) -> (bs : BitVec n) -> (b : Bool) ->
                      (k : BitVec n -> BitVec m) ->
                      (mapCps f bs k <: f b) = mapCps f bs (\bs' => k bs' <: f b)
    mapCpsAppendGen f (MSB x) b k = Refl
    mapCpsAppendGen f (msbs <: lsb) b k = mapCpsAppendGen f msbs b (\bs' => k (bs' <: f lsb))

    ||| The classicial `map` function for bit vectors defined by induction on the structure of the bit vector.
    map : (f : Bool -> Bool) -> (bs : BitVec n) -> BitVec n
    map f (MSB b) = MSB (f b)
    map f (bs <: b) = Properties.map f bs <: f b

    0
    prfMap : (bs : BitVec n) -> (f : Bool -> Bool) -> Properties.map f bs = StructuralOps.map f bs
    prfMap (MSB x) f = Refl
    prfMap (msbs <: lsb) f = rewrite prfMap msbs f in mapCpsAppendGen f msbs lsb Prelude.id

    ||| Lemma: appending a bit after `zipWithCps` with continuation `k` is the same as threading the append through the continuation.
    export
    0
    zipWithCpsAppendGen : (f : Bool -> Bool -> Bool) -> (bs1 : BitVec n) -> (bs2 : BitVec n) -> (b1 : Bool) -> (b2 : Bool) ->
                          (k : BitVec n -> BitVec m) ->
                          (zipWithCps f bs1 bs2 k <: f b1 b2) = zipWithCps f bs1 bs2 (\bs' => k bs' <: f b1 b2)
    zipWithCpsAppendGen f (MSB x) (MSB y) b1 b2 k = Refl
    zipWithCpsAppendGen f (MSB x) (msbs <: lsb) b1 b2 k impossible
    zipWithCpsAppendGen f (msbs <: lsb) (MSB x) b1 b2 k impossible
    zipWithCpsAppendGen f (msbs <: lsb) (bv <: x) b1 b2 k = zipWithCpsAppendGen f msbs bv b1 b2 (\bs' => k (bs' <: f lsb x))

    ||| Classical `zipWith` function for bit vectors defined by induction on the structure of the bit vector.
    zipWith : (f : Bool -> Bool -> Bool) -> (bs1 : BitVec n) -> (bs2 : BitVec n) -> BitVec n
    zipWith f (MSB b1) (MSB b2) = MSB (f b1 b2)
    zipWith f (bs1 <: b1) (bs2 <: b2) = Properties.zipWith f bs1 bs2 <: f b1 b2

    0
    prfZipWith : (f : Bool -> Bool -> Bool) -> (bs1 : BitVec n) -> (bs2 : BitVec n) 
       -> Properties.zipWith f bs1 bs2 = zipWithCps f bs1 bs2 (\x => x)
    prfZipWith f (MSB x) (MSB y) = Refl
    prfZipWith f (MSB x) (msbs <: lsb) impossible
    prfZipWith f (msbs <: lsb) (MSB x) impossible
    prfZipWith f (msbs <: lsb) (bv <: x) = 
      rewrite prfZipWith f msbs bv in zipWithCpsAppendGen f msbs bv lsb x Prelude.id

    0
    foldLemma : (f : a -> Bool -> a) -> (init : a) 
      -> (msbs : BitVec m) -> (lsbs : BitVec n)
      -> (fold f (fold f init lsbs) msbs) = fold f init (msbs ++ lsbs)
    foldLemma f init msbs (MSB x) = Refl
    foldLemma f init msbs (lsbsMSBs <: lsb) = foldLemma f (f init lsb) msbs lsbsMSBs

    0
    lemma_getMSB_cons : (x : BitVec n) -> (y : Bool) -> getMSB (x <: y) = getMSB x
    lemma_getMSB_cons (MSB x) y = Refl
    lemma_getMSB_cons (msbs <: lsb) y = Refl

    0
    lemma_getMSB_scanCPS : {n, m, m' : Nat} -> (f : Bool -> Bool -> Bool) -> (init : Bool) -> (bs : BitVec n)
      -> (k : BitVec n -> BitVec m) -> (k' : BitVec n -> BitVec m')
      -> (prf : ((x : BitVec n) -> getMSB (k x) = getMSB (k' x)))
      -> getMSB (scanCPS f init bs k) = getMSB (scanCPS f init bs k')
    lemma_getMSB_scanCPS f init (MSB x) k k' prf = prf (MSB (f init x))
    lemma_getMSB_scanCPS f init (msbs <: lsb) k k' prf = 
      lemma_getMSB_scanCPS f (f init lsb) msbs 
        (\bs' => k (bs' <: f init lsb)) (\bs' => k' (bs' <: f init lsb))
        (\x => prf (x <: f init lsb))

    scanFoldLemma : (f : Bool -> Bool -> Bool) -> (init : Bool) -> (bv : BitVec n)
      -> (getMSB $ scan f init bv) = fold f init bv
    scanFoldLemma f init (MSB x) = Refl
    scanFoldLemma f init ((MSB x) <: lsb) = Refl
    scanFoldLemma f init ((msbs <: x) <: lsb) = 
      trans (lemma_getMSB_scanCPS f (f (f init lsb) x) msbs 
              (\bs' => (bs' <: f (f init lsb) x) <: f init lsb) id (\x => Refl))
            (scanFoldLemma f (f (f init lsb) x) msbs)

    0
    scanCpsKId : (f : Bool -> Bool -> Bool) -> (init : Bool) -> (bs : BitVec n)
      -> (k : BitVec n -> r)
      -> scanCPS f init bs k = k (scanCPS f init bs (\x => x))
    scanCpsKId f init (MSB x) k = Refl
    scanCpsKId f init (msbs <: lsb) k = 
      let ih1 = scanCpsKId f (f init lsb) msbs (\bs' => k (bs' <: f init lsb))
          ih2 = scanCpsKId f (f init lsb) msbs (\bs' => bs' <: f init lsb)
      in rewrite ih1 in rewrite ih2 in Refl

    ||| MSBs does not affect the LSBs of a scan.
    scanLsbsEq : (f : Bool -> Bool -> Bool) -> (init : Bool) -> (bv : BitVec n)
      -> (k : Nat) -> (prfLower : GT k 0) -> (prfUpper : LT k n)
      -> (lsbsUntil k {prfLower = prfLower} {prfUpper = prfUpper} (scan f init bv)) 
       = scan f init (lsbsUntil k {prfLower = prfLower} {prfUpper = prfUpper} bv)
    scanLsbsEq {n} f init bv 0 prfLower prfUpper = absurd prfLower
    scanLsbsEq {n = S Z} f init (MSB x) (S 0) prfLower prfUpper = absurd prfUpper
    scanLsbsEq {n = S (S Z)} f init ((MSB x) <: lsb) (S 0) prfLower prfUpper = Refl
    scanLsbsEq {n = S (S k)} f init ((msbs <: x) <: lsb) (S 0) prfLower prfUpper = 
      rewrite scanCpsKId f (f (f init lsb) x) msbs (\bs' => (bs' <: f (f init lsb) x) <: f init lsb) in Refl
    scanLsbsEq {n = S Z} f init (MSB x) (S (S k)) prfLower prfUpper = absurd prfUpper
    scanLsbsEq {n = S (S Z)} f init ((MSB x) <: lsb) (S (S k)) prfLower prfUpper = absurd prfUpper
    scanLsbsEq {n = S (S k)} f init ((msbs <: x) <: lsb) (S (S 0)) prfLower (LTESucc y) = 
      rewrite scanCpsKId f (f (f init lsb) x) msbs (\bs' => (bs' <: f (f init lsb) x) <: f init lsb) in Refl
    scanLsbsEq {n = S (S n')} f init ((msbs <: x) <: lsb) (S (S (S k))) prfLower (LTESucc y) with (y)
      scanLsbsEq {n = (S (S n'))} f init ((msbs <: x) <: lsb) (S (S (S k))) prfLower (LTESucc y) | (LTESucc z) = 
        rewrite scanCpsKId f (f (f init lsb) x) msbs (\bs' => (bs' <: f (f init lsb) x) <: f init lsb) in
        rewrite scanCpsKId {n = S k} f (f (f init lsb) x) (lsbsUntil (S k) msbs) (\bs' => (bs' <: f (f init lsb) x) <: f init lsb) in
        cong (\v => v <: f init lsb) $ cong (\v => v <: f (f init lsb) x) 
          (scanLsbsEq f (f (f init lsb) x) msbs (S k) (LTESucc LTEZero) z)
    