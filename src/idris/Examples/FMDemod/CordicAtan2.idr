module Examples.FMDemod.CordicAtan2
{- Atan2 implemented with Cordic and q2.29 format-}

import SynQ
import Examples.FMDemod.BarrelShifter
import Data.Vect
import Language.Reflection
import System.File

import Impl.TAC

%language ElabReflection
%hide Linear.Interface.seq

private infixl 9 <<<
%hide Data.LState.infixr.(<<<)
%hide Prelude.(>>=)
%hide Data.LState.(>>=)

neg: (Primitive comb)
  => comb () (BitVec 32)
  -> comb () (BitVec 32)
neg x = adder' (not x) (const $ BV 1)

small: (Primitive comb)
  => comb () (BitVec 32)
  -> comb () (BitVec 1)
small x = x `eq` (const $ BV 0)

if': (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a}
  -> comb (BitVec 1, a, a) a
if' = lam $ \x => if_ (proj1 x) (proj1 $ proj2 x) (proj2 $ proj2 x)

nextXY: (Comb comb, Primitive comb)
  => comb ((BitVec 32, BitVec 32), BitVec 5) (BitVec 32, BitVec 32)
nextXY = 
  lam $ \ins => 
    let x  = proj1 $ proj1 ins 
        y  = proj2 $ proj1 ins
        st = proj2 ins
        x' = shifterRA st x -- barrelShifterRA32 st x
        y' = shifterRA st y
    in -- if_ (small y) (prod x y)
           (if_ (y `lt` (const $ BV 0)) 
                (prod (adder' x (neg y')) (adder' y x'))
                (prod (adder' x y') (adder' y (neg x'))))

loadXY: (Comb comb, Primitive comb)
  => comb (BitVec 32, BitVec 32) 
          (BitVec 32, BitVec 32)
loadXY = 
  lam $ \ins => 
    let (xin, yin) = unpack ins
        x = mux21 (const (BV 0) `lt` xin)
                  xin (neg xin)
        y = mux21 (const (BV 0) `lt` xin)
                  yin (neg yin)
    in (prod x y)
  where
  unpack: comb () (BitVec 32, BitVec 32)
    -> (comb () (BitVec 32), comb () (BitVec 32))
  unpack x = (proj1 x, proj2 x)

updateXY: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 32, BitVec 32) comb seq)
  -> (en: comb () (BitVec 1))
  -> (x : comb () (BitVec 32))
  -> (y : comb () (BitVec 32))
  -> (st: comb () (BitVec 5))
  -> seq (LPair (!* BitVec 32) (!* BitVec 32)) () (BitVec 32)
updateXY (MkReg get set) en x y st = 
  do acc <- get
     let nxtAcc = app nextXY (prod acc st)
         ldAcc  = app loadXY (prod x y)
         acc'   = app if' (prod en $ prod ldAcc nxtAcc)
     _ <- set acc'
     pure $ proj2 acc
     
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
    in -- mux21 (small y) z
         (mux21 (y `lt` (const $ BV 0)) 
                (adder' z (neg lutVal))
                (adder' z lutVal))
            
loadZ: (Comb comb, Primitive comb)
  => comb (BitVec 32, BitVec 32) (BitVec 32)
loadZ = 
  lam $ \ins => 
    let (xin, yin) = unpack ins
        z = mux21 (const (BV 0) `lt` xin)
                  (const (BV 0))
                  (mux21 (const (BV 0) `lt` yin)
                         (const $ BV 1686629713)
                         (neg $ const $ BV 1686629713))
    in z
  where
  unpack: comb () (BitVec 32, BitVec 32)
    -> (comb () (BitVec 32), comb () (BitVec 32))
  unpack x = (proj1 x, proj2 x)

updateZ: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 32) comb seq)
  -> (en: comb () (BitVec 1))
  -> (x: comb () (BitVec 32))
  -> (y: comb () (BitVec 32))
  -> (yAcc: comb () (BitVec 32))
  -> (st: comb () (BitVec 5))
  -> seq (!* BitVec 32) () (BitVec 32)
updateZ (MkReg get set) en x y yAcc st = 
  do z <- get
     let nxtZ = app nextZ (prod yAcc $ prod z $ prod (lut st) st)
         ldZ  = app loadZ (prod x y)
         z'   = mux21 en ldZ nxtZ
     _ <- set z'
     pure z
     
updateSt: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 5) comb seq)
  -> (en: comb () (BitVec 1))
  -> seq (!* BitVec 5) () (BitVec 5)
updateSt (MkReg get set) en = 
  do st <- get
     let st' = mux21 en 
                 (const $ BV 0) 
                 (mux21 (eq st (not $ const $ BV 0))
                        (not $ const $ BV 0)
                        (adder' st (const $ BV 1)))
     _ <- set st'
     pure st
     
CAtan2St': Type
CAtan2St' = ((BitVec 32, BitVec 32), BitVec 32, BitVec 5)

CAtan2St: Type
CAtan2St = LPair (LPair (!* BitVec 32) (!* BitVec 32)) (LPair (!* BitVec 32) (!* BitVec 5))

cordicAtan2: (Seq comb seq, Primitive comb)
  => (1 stReg: Reg (BitVec 5) comb seq)
  -> (1 xyReg: Reg (BitVec 32, BitVec 32) comb seq)
  -> (1 zReg : Reg (BitVec 32) comb seq)
  -> (en: comb () (BitVec 1))
  -> (y: comb () (BitVec 32))
  -> (x: comb () (BitVec 32))
  -> seq CAtan2St () (BitVec 1, BitVec 32)
cordicAtan2 stReg xyReg zReg en y x = 
  let updateXY = updateXY xyReg en x y
      updateZ  = updateZ zReg en x y
      updateSt = updateSt stReg en
  in do st   <- updateSt        <<< (pure unit)       <<< pure unit
        yAcc <- (pure $ lam id) <<< (pure $ lam id)   <<< updateXY st
        res  <- (pure $ lam id) <<< (updateZ yAcc st) <<< pure unit
        pure (prod (eq st (const $ BV 30)) res)

cordicAtan2': (Seq comb seq, Primitive comb)
  => (1 stReg: Reg (BitVec 5) comb seq)
  -> (1 xyReg: Reg (BitVec 32, BitVec 32) comb seq)
  -> (1 zReg : Reg (BitVec 32) comb seq)
  -> seq CAtan2St (BitVec 1, BitVec 32, BitVec 32) (BitVec 1, BitVec 32)
cordicAtan2' stReg xyReg zReg = 
  abst $ \x => cordicAtan2 stReg xyReg zReg (proj1 x) (proj1 $ proj2 x) (proj2 $ proj2 x)
  
%unhide Prelude.(>>=)
%ambiguity_depth 8

read: IO (BitVec 1, BitVec 32, BitVec 32)
read = do putStr "en: \n"
          fflush stdout
          en <- (pure $ BitVec.fromInteger . cast) <*> getLine
          putStr "x: \n"
          fflush stdout
          x <- (pure $ BitVec.fromInteger . cast) <*> getLine
          putStr "y: \n"
          fflush stdout
          y <- (pure $ BitVec.fromInteger . cast) <*> getLine
          pure (en, x, y)
          
atan2: IO ()
atan2 = reactMealy read (runSeq $ cordicAtan2' reg reg reg) 
                   (((MkBang $ BV 0) # (MkBang $ BV 0)) 
                   # (MkBang $ BV 0) # (MkBang $ BV 0))
                   
emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "atan2" $ shareExp $ elimDead $ flatTAC $ genTAC (cordicAtan2' reg reg reg)

emitVerilog: IO ()
emitVerilog = dumpVerilog "atan2" $ shareExp $ elimDead $ flatTAC $ genTAC (cordicAtan2' reg reg reg)

emitPP: IO ()
emitPP = ppDump "atan2" $ pprint $ shareExp $ elimDead $ flatTAC $ genTAC (cordicAtan2' reg reg reg)
