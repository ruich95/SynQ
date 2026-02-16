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

-- lpf fc = 0.075fs fs = 0.175fs
coef_cic3d128_comp: Vect 32 (BitVec 18)
coef_cic3d128_comp = 
  [BV 0x3ff3c, BV 0x3fed4, BV 0x3ff2b, BV 0x000fb, BV 0x003fb, BV 0x00673, BV 0x005c8, BV 0x0001e,
   BV 0x3f661, BV 0x3ed3d, BV 0x3ebeb, BV 0x3f8c9, BV 0x0155c, BV 0x03c04, BV 0x06135, BV 0x07807,
   BV 0x07807, BV 0x06135, BV 0x03c04, BV 0x0155c, BV 0x3f8c9, BV 0x3ebeb, BV 0x3ed3d, BV 0x3f661,
   BV 0x0001e, BV 0x005c8, BV 0x00673, BV 0x003fb, BV 0x000fb, BV 0x3ff2b, BV 0x3fed4, BV 0x3ff3c]
   
 -- lpf fc = 75kHz (0.3125) fs = 120kHz (0.5) @ sample rate 480kHz
coef_lpf_03125_05: Vect 32 (BitVec 18)
coef_lpf_03125_05 = 
  [BV 0x000c4, BV 0x3ff68, BV 0x3fdb6, BV 0x3ff14, BV 0x003b8, BV 0x0048d, BV 0x3fcb2, BV 0x3f585,
   BV 0x3fdca, BV 0x0100e, BV 0x00fcf, BV 0x3f055, BV 0x3d6e8, BV 0x3fcb3, BV 0x06470, BV 0x0c201,
   BV 0x0c201, BV 0x06470, BV 0x3fcb3, BV 0x3d6e8, BV 0x3f055, BV 0x00fcf, BV 0x0100e, BV 0x3fdca,
   BV 0x3f585, BV 0x3fcb2, BV 0x0048d, BV 0x003b8, BV 0x3ff14, BV 0x3fdb6, BV 0x3ff68, BV 0x000c4]
   
coef_cic4d128_comp_64: Vect 64 (BitVec 18)
coef_cic4d128_comp_64 = 
  [BV 0x3ffe3, BV 0x3ffb6, BV 0x3ff76, BV 0x3ff3a, BV 0x3ff26, BV 0x3ff61, BV 0x3fffc, BV 0x000e2, 
   BV 0x001c9, BV 0x00247, BV 0x001f5, BV 0x000a8, BV 0x3fe9a, BV 0x3fc77, BV 0x3fb36, BV 0x3fbb6, 
   BV 0x3fe54, BV 0x00291, BV 0x00709, BV 0x009ca, BV 0x0090c, BV 0x00402, BV 0x3fb82, BV 0x3f224, 
   BV 0x3ebb8, BV 0x3ec2e, BV 0x3f62a, BV 0x009e1, BV 0x02498, BV 0x0411c, BV 0x0590e, BV 0x066b8, 
   BV 0x066b8, BV 0x0590e, BV 0x0411c, BV 0x02498, BV 0x009e1, BV 0x3f62a, BV 0x3ec2e, BV 0x3ebb8, 
   BV 0x3f224, BV 0x3fb82, BV 0x00402, BV 0x0090c, BV 0x009ca, BV 0x00709, BV 0x00291, BV 0x3fe54, 
   BV 0x3fbb6, BV 0x3fb36, BV 0x3fc77, BV 0x3fe9a, BV 0x000a8, BV 0x001f5, BV 0x00247, BV 0x001c9,
   BV 0x000e2, BV 0x3fffc, BV 0x3ff61, BV 0x3ff26, BV 0x3ff3a, BV 0x3ff76, BV 0x3ffb6, BV 0x3ffe3]
  
   

lut_01_025: (Primitive comb)
  => comb () (BitVec 5)
  -> comb () (BitVec 18)
lut_01_025 = %runElab lutGen coef_01_025

export
lut_cic3d128_comp: (Primitive comb)
  => comb () (BitVec 5)
  -> comb () (BitVec 18)
lut_cic3d128_comp = %runElab lutGen coef_cic3d128_comp

export
lut_lpf_03125_05: (Primitive comb)
  => comb () (BitVec 5)
  -> comb () (BitVec 18)
lut_lpf_03125_05 = %runElab lutGen coef_lpf_03125_05

export
CoefSt': Type
CoefSt' = BitVec 5

export
CoefSt: Type
CoefSt = (!* BitVec 5)

export
coefInit: CoefSt
coefInit = (MkBang $ BV 0)


export
show': CoefSt -> String
show' x = show x

export
%hint
CoefStIsSt: St CoefSt
CoefStIsSt = LV

export
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

export
lut_cic4d128_comp_64: (Primitive comb)
  => comb () (BitVec 6)
  -> comb () (BitVec 18)
lut_cic4d128_comp_64 = %runElab lutGen coef_cic4d128_comp_64

export
CoefSt64: Type
CoefSt64 = (!* BitVec 6)

export
CoefSt64': Type
CoefSt64' = (BitVec 6)

export
coef64Init: CoefSt64
coef64Init = (MkBang $ BV 0)

export
%hint
CoefSt64IsSt: St CoefSt64
CoefSt64IsSt = LV

export
firCoef64: (Seq comb seq, Primitive comb)
  => (1 reg: Reg CoefSt64' comb seq)
  -> (lut: comb () (BitVec 6) -> comb () (BitVec 18))
  -> (en: comb () (BitVec 1))
  -> seq CoefSt64 () (BitVec 18)
firCoef64 (MkReg get set) lut en = 
  do idx <- get
     let curIdx = mux21 en (const $ BV 0) 
                           idx 
         nxtIdx = adder' curIdx (const $ BV 1)
     _ <- set nxtIdx
     pure $ lut curIdx
