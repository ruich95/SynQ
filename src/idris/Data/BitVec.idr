module Data.BitVec

import Data.Bits
import public Data.Nat

public export
record BitVec (n: Nat) where
  constructor BV
  val: Bits64

public export
{len:_} -> Eq (BitVec len) where
  (==) (BV v1) (BV v2) = (v1 == v2)
  
export      
{len:_} -> Show (BitVec len) where
  show (BV v) = show len ++ "'d" ++ show v

lteSelf: (n: Nat) -> LTE n n
lteSelf 0 = LTEZero
lteSelf (S k) = LTESucc $ lteSelf k

lteRelax: (m: Nat) -> (n: Nat) -> LTE m n -> LTE m (S n)
lteRelax 0 0 LTEZero = LTEZero
lteRelax 0 (S k) LTEZero = LTEZero
lteRelax (S j) (S k) (LTESucc x) = LTESucc (lteRelax j k x)

lemma: (m: Nat) -> (n: Nat) -> (LTE (minus m n) m)
lemma 0 n = LTEZero
lemma (S k) 0 = lteSelf (S k)
lemma (S k) (S j) = lteRelax (minus k j) k $ lemma k j

toFin: (m: Nat) -> (n: Nat) -> {auto prf: LTE n $ S m} -> Fin (S m)
toFin m 0 {prf=LTEZero} = FZ
toFin 0 (S k) {prf=LTESucc x} = FZ
toFin (S j) (S k) {prf=LTESucc x} = FS $ toFin j k {prf=x}


export
fromInteger: {n:_} -> Integer -> BitVec n
fromInteger {n} i = 
  let sht = toFin 63 (minus 64 n) {prf = lemma 64 n}
      msk = shiftR (the Bits64 oneBits) sht
  in BV $ msk .&. (cast i)

---------------------------------------------------------------

lib_bv : String -> String
lib_bv fn = "C:" ++ fn ++ ",libbv"

natToBits8: Nat -> Bits8
natToBits8 k with (k < 64)
  natToBits8 k | False = 64
  natToBits8 k | True 
    = case k of
        0     => 0
        (S j) => 1 + natToBits8 j

%foreign (lib_bv "bv_eq")
bv_eq: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvEq: {n:_} -> BitVec n -> BitVec n -> BitVec 1 
bvEq {n} x y = 
  let len = natToBits8 n 
      res = bv_eq len x.val y.val
  in BV res

%foreign (lib_bv "bv_add")
bv_add: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvAdd: {n:_} -> BitVec n -> BitVec n -> BitVec (S n) 
bvAdd {n} x y = 
  let len = natToBits8 n 
      res = bv_add len x.val y.val
  in BV res

%foreign (lib_bv "bv_slice")
bv_slice: Bits8 -> Bits8 -> Bits8 -> Bits64 -> Bits64

export
bvSlice: {n:_} -> (lower: Nat) -> (upper: Nat) -> BitVec n -> BitVec (minus upper lower) 
bvSlice lower upper x = 
  let len = natToBits8 n 
      lb = natToBits8 lower
      ub = natToBits8 upper
      res = bv_slice lb ub len x.val
  in BV res


%foreign (lib_bv "bv_ltu")
bv_ltu: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvLtu: {n:_} -> BitVec n -> BitVec n -> BitVec 1 
bvLtu {n} x y = 
  let len = natToBits8 n 
      res = bv_ltu len x.val y.val
  in BV res

%foreign (lib_bv "bv_lt")
bv_lt: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvLt: {n:_} -> BitVec n -> BitVec n -> BitVec 1 
bvLt {n} x y = 
  let len = natToBits8 n 
      res = bv_lt len x.val y.val
  in BV res
      
%foreign (lib_bv "bv_and")
bv_and: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvAnd: {n:_} -> BitVec n -> BitVec n -> BitVec n
bvAnd x y = 
  let len = natToBits8 n 
      res = bv_and len x.val y.val
  in BV res

%foreign (lib_bv "bv_xor")
bv_xor: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvXor: {n:_} -> BitVec n -> BitVec n -> BitVec n
bvXor x y = 
  let len = natToBits8 n 
      res = bv_xor len x.val y.val
  in BV res

%foreign (lib_bv "bv_or")
bv_or: Bits8 -> Bits64 -> Bits64 -> Bits64

export
bvOr: {n:_} -> BitVec n -> BitVec n -> BitVec n
bvOr x y = 
  let len = natToBits8 n 
      res = bv_or len x.val y.val
  in BV res

%foreign (lib_bv "bv_neg")
bv_neg: Bits8 -> Bits64 -> Bits64

export
bvNot: {n:_} -> BitVec n -> BitVec n
bvNot x = 
  let len = natToBits8 n 
      res = bv_neg len x.val
  in BV res
  
%foreign (lib_bv "bv_concatenate")
bv_concatenate: Bits8 -> Bits64 -> Bits8 -> Bits64 -> Bits64

export
bvConcat: {m:_} -> {n:_} -> BitVec m -> BitVec n -> BitVec (m+n)
bvConcat x y = 
  let len1 = natToBits8 m
      len2 = natToBits8 n
      z = bv_concatenate len1 x.val len2 y.val
  in BV z

%foreign (lib_bv "bv_srl_2")
bv_srl_2: Bits8 -> Bits8 -> Bits64 -> Bits64

export
bvSrl: {n:_} -> (sht: Nat) -> BitVec n -> BitVec n
bvSrl sht x = 
    let sht' = natToBits8 sht
        len  = natToBits8 n
    in BV $ bv_srl_2 sht' len x.val

%foreign (lib_bv "bv_sll_2")
bv_sll_2: Bits8 -> Bits8 -> Bits64 -> Bits64

export
bvSll: {n:_} -> (sht: Nat) -> BitVec n -> BitVec n
bvSll sht x = 
    let sht' = natToBits8 sht
        len  = natToBits8 n
    in BV $ bv_sll_2 sht' len x.val
    
%foreign (lib_bv "bv_sra_2")
bv_sra_2: Bits8 -> Bits8 -> Bits64 -> Bits64

export
bvSra: {n:_} -> (sht: Nat) -> BitVec n -> BitVec n
bvSra sht x = 
    let sht' = natToBits8 sht
        len  = natToBits8 n
    in BV $ bv_sra_2 sht' len x.val



