module Examples.FMDemod.CordicAtan2
{- Atan2 implemented with Cordic and q29 format-}

import SynQ
import Examples.FMDemod.BarrelShifter
import Data.Vect
import Language.Reflection

%language ElabReflection


neg: (Primitive comb)
  => comb () (BitVec 32)
  -> comb () (BitVec 32)
neg x = adder' x (not $ const $ BV 0)

nextXY: (Comb comb, Primitive comb)
  => comb (BitVec 32, BitVec 32, BitVec 5) (BitVec 32, BitVec 32)
nextXY = 
  lam $ \ins => 
    let x  = proj1 ins 
        y  = proj1 $ proj2 ins
        st = proj2 $ proj2 ins
        x' = barrelShifterRA32 st x
        y' = barrelShifterRA32 st y
    in if_ (y `lt` (const $ BV 0)) 
           (prod (adder' x (neg y')) (adder' y x'))
           (prod (adder' x y') (adder' y (neg x')))

lutVal: Vect 30 (BitVec 32)
lutVal = [BV 421657428, BV 248918914, BV 131521918, BV 66762579, BV 33510843, BV 16771757, 
          BV 8387925,   BV 4194218,   BV 2097141,   BV 1048574,  BV 524287,   BV 262143, 
          BV 131071,    BV 65535,     BV 32767,     BV 16383,    BV 8191,     BV 4095, 
          BV 2047,      BV 1023,      BV 511,       BV 255,      BV 127,      BV 63, 
          BV 31,        BV 15,        BV 7,         BV 4,        BV 2,        BV 1]

lut: (Primitive comb)
  => comb () (BitVec 5) -> comb () (BitVec 32)
lut = %runElab lutGen lutVal

nextZ: (Comb comb, Primitive comb)
  => comb (BitVec 32, BitVec 32, BitVec 32, BitVec 5) (BitVec 32)
nextZ = 
  lam $ \ins => 
    let y      = proj1 ins 
        z      = proj1 $ proj2 ins
        lutVal = proj1 $ proj2 $ proj2 ins
        st     = proj2 $ proj2 $ proj2 ins
    in mux21 (y `lt` (const $ BV 0)) 
             (adder' z (neg lutVal))
             (adder' z lutVal)
             
unpackIn: (Comb comb)
  => comb () (BitVec 32, BitVec 32, BitVec 32, BitVec 5)
  -> (comb () (BitVec 32), comb () (BitVec 32), 
      comb () (BitVec 32), comb () (BitVec 5))
unpackIn x = (proj1 x, proj1 (proj2 x), proj1 (proj2 (proj2 x)), proj2 (proj2 (proj2 x)))

updateXYZ: (Comb comb, Primitive comb)
  => comb (BitVec 32, BitVec 32, BitVec 32, BitVec 5) ((BitVec 32, BitVec 32), BitVec 32)
updateXYZ = 
  lam $ \ins => 
    let (x, y, z, st) = unpackIn ins
        lutVal: comb () (BitVec 32) = lut st
    in prod (app nextXY $ prod x $ prod y st) 
            (app nextZ  $ prod y $ prod z $ prod lutVal st)
