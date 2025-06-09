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


%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

0 minusZero: (n:Nat) -> n = minus n 0
minusZero 0 = Refl
minusZero (S k) = Refl

lutGen': (Comb comb, Primitive comb)
     => (idx_width: Nat)
     -> (data_width: Nat)
     -> (List1 $ BitVec data_width)
     -> (start: comb () $ BitVec idx_width)
     -> comb () (BitVec idx_width) 
     -> comb () (BitVec data_width)
lutGen' idx_width data_width (x ::: []) start idx = const x
lutGen' idx_width data_width (x ::: (y :: xs)) start idx = 
  let next_start = rewrite minusZero idx_width 
                   in slice 0 idx_width $ add start $ const $ BV 1
  in mux21 (eq start idx) (const x) 
           (lutGen' idx_width data_width (y:::xs) next_start idx)


lutGen: (Comb comb, Primitive comb)
     => {idx_width: Nat}
     -> {data_width: Nat}
     -> (List1 $ BitVec data_width)
     -> comb () (BitVec idx_width) 
     -> comb () (BitVec data_width)
lutGen {idx_width} {data_width} (x1 ::: (x2 :: x3 :: xs)) idx 
  = mux21 (ltu idx $ const (BV 2)) 
          (lutGen' idx_width data_width (x1:::[x2]) (const $ BV 0) idx)
          (lutGen' idx_width data_width (x3:::xs) (const $ BV 2) idx)
lutGen {idx_width} {data_width} xs idx 
  = lutGen' idx_width data_width xs (const $ BV 0) idx
  
sine: List1 UInt8
sine = (BV 100) 
   ::: [BV 119, BV 138, BV 155] --, BV 170] -- , 183, 192, 198, 200, 198, 192, 183, 170,
                       -- 155, 138, 119, 100,  80,  61,  44,  29,  16,   7,   1,   0, 1,
                       -- 7,   16,  29,  44,  61,  80]

sineLut: (Comb comb, Primitive comb)
     => comb UInt8 UInt8
sineLut = lam $ \idx => lutGen sine idx

t: UInt8 -> UInt8
t = %runElab (genComb sineLut)
