module Examples.FMDemod.FIRCoef

import SynQ
import Language.Reflection
import Data.Vect
import System.File

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)

%language ElabReflection

-- lpf fc = 0.05fs fs = 0.125fs
coef_01_025: Vect 32 (BitVec 18)
coef_01_025 = 
  [BV 0x001ab, BV 0x00203, BV 0x00229, BV 0x00126, BV 0x3feab, BV 0x3faf3, BV 0x3f6f3, BV 0x3f445, 
   BV 0x3f4d6, BV 0x3fa50, BV 0x0057e, BV 0x015d0, BV 0x0293b, BV 0x03c8d, BV 0x04c25, BV 0x054da, 
   BV 0x054da, BV 0x04c25, BV 0x03c8d, BV 0x0293b, BV 0x015d0, BV 0x0057e, BV 0x3fa50, BV 0x3f4d6, 
   BV 0x3f445, BV 0x3f6f3, BV 0x3faf3, BV 0x3feab, BV 0x00126, BV 0x00229, BV 0x00203, BV 0x001ab]
   

lut_01_025: (Primitive comb)
  => comb () (BitVec 5)
  -> comb () (BitVec 18)
lut_01_025 = %runElab lutGen coef_01_025

CoefSt': Type
CoefSt' = BitVec 5

CoefSt: Type
CoefSt = (!* BitVec 5)

firCoef: (Seq comb seq, Primitive comb)
  => (1 reg: Reg CoefSt' comb seq)
  -> (lut: comb () (BitVec 5) -> comb () (BitVec 18))
  -> (en: comb () (BitVec 1))
  -> seq CoefSt () (BitVec 18)
firCoef (MkReg get set) lut en = 
  do idx <- get
     let curIdx = mux21 en (const $ BV 0) 
                           idx 
         nxtIdx = adder' curIdx (const $ BV 1)
     _ <- set nxtIdx
     pure $ lut curIdx
     
lpf_01_025_coef: (BitVec 1) -> LState (CoefSt) (BitVec 18)
lpf_01_025_coef = runSeq $ abst $ firCoef reg lut_01_025

%unhide Prelude.(>>=)
read: IO (BitVec 1)
read = do putStr "en: \n"
          fflush stdout
          en <- (pure $ BitVec.fromInteger . cast) <*> getLine
          pure en

lpfCoef01025Prog: IO ()
lpfCoef01025Prog = reactMealy read lpf_01_025_coef $ (MkBang $ BV 0)
