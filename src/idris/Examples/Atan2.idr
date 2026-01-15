module Examples.Atan2

import SynQ
import System.File
import Data.Vect
import Language.Reflection

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide Prelude.const
%hide Prelude.pure
%hide Prelude.concat
%hide Data.LState.infixr.(<<<)

%language ElabReflection

private infixl 9 <<<

lut16: Vect 16 (BitVec 32)
lut16 = [BV 421657428, BV 248918914, BV 131521918, BV 66762579, 
         BV 33510843,  BV 16771757,  BV 8387925,   BV 4194218, 
         BV 2097141,   BV 1048574,   BV 524287,    BV 262143, 
         BV 131071,    BV 65535,     BV 32767,     BV 16383]
         
atan2Lut: (Primitive comb)
  => comb () (BitVec 4) -> comb () (BitVec 32)
atan2Lut = %runElab lutGen lut16

export
ATAN2St': Type
ATAN2St' = (BitVec 4, BitVec 32, BitVec 32, BitVec 32)

export
ATAN2St: Type
ATAN2St = LPair (!* BitVec 4) $ LPair (!* BitVec 32) $ LPair (!* BitVec 32) (!* BitVec 32)

export
%hint
ATAN2StIsSt: St ATAN2St
ATAN2StIsSt = LP LV (LP LV (LP LV LV))

export
neg: (Primitive comb)
  => {auto n: _} 
  -> comb () (BitVec n)
  -> comb () (BitVec n)
neg x = adder' (not x) (const $ BV 1)

prf1: (x: Nat) -> LTE x x
prf1 0 = LTEZero
prf1 (S k) = LTESucc $ prf1 k

prf2: (x: Nat) -> LTE x (S x)
prf2 0 = LTEZero
prf2 (S k) = LTESucc $ prf2 k

prf3: (x: Nat) -> 1 = minus (S x) x
prf3 0 = Refl
prf3 (S k) = prf3 k

export
signExt: (Primitive comb)
  => {auto m:_} -> {auto n:_} 
  -> {auto prf: LT m n}
  -> comb () (BitVec m)
  -> comb () (BitVec n)
signExt {m = 0} x = const $ BV 0
signExt {m = (S k)} x = 
  let sign = rewrite prf3 k in slice {prf_upper = prf1 (S k)} {prf_lower = prf2 k}  k (S k) x
      nbits = minus n (S k)
      signs: comb () (BitVec nbits) = 
        mux21 sign 
          (not $ const $ BV {n=nbits} 0)
          (const $ BV {n=nbits} 0)
      extended: comb () (BitVec $ nbits + (S k))
        = concat signs x
      prf: n === (nbits + (S k)) = believe_me ()
  in rewrite prf in extended



unpack: (Comb comb)
  => comb () ATAN2St'
  -> (comb () (BitVec 4),  comb () (BitVec 32), 
      comb () (BitVec 32), comb () (BitVec 32))
unpack x = (proj1 x, (proj1 $ proj2 x), (proj1 $ proj2 $ proj2 x), (proj2 $ proj2 $ proj2 x))

atan2: (Seq comb seq, Primitive comb)
  => (st: Reg ATAN2St' comb seq)
  -> (valid: comb () $ BitVec 1)
  -> (x    : comb () $ BitVec 16)
  -> (y    : comb () $ BitVec 16)
  -> seq ATAN2St () (BitVec 1, BitVec 16)  
atan2 (MkReg get set) valid x y = 
  let x = signExt {m=16} {n=32} x
      y = signExt {m=16} {n=32} y
  in do stVal <- get
        let (state, xAcc, yAcc, zAcc) = unpack stVal
            oValid = eq state (const $ BV 0)
            output = slice 16 32 zAcc
            nxtState = mux21 valid (const $ BV 1) (adder' state (const $ BV 1))
            xAcc' = 
              mux21 valid 
                (mux21 (not $ x `lt` (const $ BV 0)) 
                       (shiftLL 13 x) 
                       (shiftLL 13 $ neg {n=32} x))
                xAcc
            yAcc' = 
              mux21 valid 
                (mux21 (not $ x `lt` (const $ BV 0)) 
                       (shiftLL 13 y) 
                       (shiftLL 13 $ neg {n=32} y))
                yAcc
            zAcc' = 
        ?atan2_rhs
