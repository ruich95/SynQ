module Examples.FMDemod.FIR

import SynQ
import Impl.TAC
import Examples.FMDemod.FIRInBuffer
import Examples.FMDemod.FIRCoef
import Examples.FMDemod.MACC
import Examples.FMDemod.AddrGen
import Examples.FMDemod.RAM

import System.File

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)

private infixl 9 <<<
%hide Data.LState.infixr.(<<<)

%ambiguity_depth 8

decodeRst: (Primitive comb)
  => comb () (BitVec 6)
  -> comb () (BitVec 1)
decodeRst st = st `eq` (const $ BV 2)

decodeValid: (Primitive comb)
  => comb () (BitVec 6)
  -> comb () (BitVec 1)
decodeValid st = st `eq` (const $ BV 34)

updateSt: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 6) comb seq)
  -> (en: comb () (BitVec 1))
  -> seq (!* BitVec 6) () (BitVec 6)
updateSt (MkReg get set) en = 
  do st <- get 
     let o   = mux21 en (const $ BV 0) st
         st' = mux21 en 
                 (const $ BV 1) 
                 (mux21 (st `eq` (const $ BV 35)) 
                    st
                    (adder' st (const $ BV 1)))
     _ <- set st'
     pure o
     
%hint
bufferStIsSt: St (FIRBufferSt 18)
bufferStIsSt = FIRBufferStIsSt 18

FIRSt: Type
FIRSt = LPair MACCSt $ LPair CoefSt $ LPair (FIRBufferSt 18) (!* BitVec 6)

%hint
FIRStIsSt: St FIRSt
FIRStIsSt = LP MACCStIsSt (LP CoefStIsSt (LP (FIRBufferStIsSt 18) LV))

firCIC3D128Comp: (Seq comb seq, Primitive comb, Mult18 comb)
  => (1 stReg: Reg (BitVec 6) comb seq)
  -> (1 maccRegs: MACCRegs comb seq)
  -> (1 inBufRegs: InBufRegs comb seq)
  -> (1 coefReg: Reg CoefSt' comb seq)
  -> (en: comb () $ BitVec 1)
  -> (dat: comb () $ BitVec 18)
  -> seq FIRSt () (BitVec 1, BitVec 48)
firCIC3D128Comp stReg (maccReg1 # maccReg2 # maccReg3) (inBufReg1 # inBufReg2) coefReg en dat = 
  let inBuffer = firInBuffer inBufReg1 inBufReg2 en dat
      coefGen  = firCoef coefReg lut_cic3d128_comp en
      macc     = macc maccReg1 maccReg2 maccReg3
      stManger = updateSt stReg en
  in do st   <- stManger <<< (pure unit) <<< (pure unit) <<< (pure unit)
        let rst      = decodeRst st
            valid    = decodeValid st
        coef <- (pure $ lam id) <<< (pure $ lam id) <<< coefGen         <<< (pure unit)
        val  <- (pure $ lam id) <<< inBuffer        <<< (pure unit)     <<< (pure unit)
        out  <- (pure $ lam id) <<< (pure $ lam id) <<< (pure $ lam id) <<< macc rst (prod val coef)
        pure $ prod valid out

show': FIRSt -> String
show' (x # (y # (z # w))) = 
  "macc state: \{MACC.show' x}, coef state: \{FIRCoef.show' y}, in buffer state, \{FIRInBuffer.show' 18 z}, fir state \{show w}"
  
Show FIRSt where
  show = show'
  
%unhide Prelude.(>>=)
read: IO (BitVec 1, BitVec 18)
read = do putStr "en: \n"
          fflush stdout
          rstStr <- getLine
          let en = (BitVec.fromInteger {n=1} . cast) rstStr
          putStr "data: \n"
          fflush stdout
          x1Str <- getLine
          let dat = (BitVec.fromInteger {n=18} . cast) x1Str
          pure (en, dat)

firCIC3D128Comp': (Seq comb seq, Primitive comb, Mult18 comb)
  => (1 stReg: Reg (BitVec 6) comb seq)
  -> (1 maccRegs: MACCRegs comb seq)
  -> (1 inBufRegs: InBufRegs comb seq)
  -> (1 coefReg: Reg CoefSt' comb seq)
  -> seq FIRSt (BitVec 1, BitVec 18) (BitVec 1, BitVec 48)
firCIC3D128Comp' stReg maccRegs inBufRegs coefReg = 
  abst $ \x => firCIC3D128Comp stReg maccRegs inBufRegs coefReg (proj1 x) (proj2 x)

firCIC3D128CompProg: IO ()
firCIC3D128CompProg = 
  reactMealy read 
    (runSeq $ firCIC3D128Comp' reg (reg # reg # reg) (reg # reg) reg)
    (maccInit # coefInit # initBufferSt 18 # (MkBang $ BV 0))

emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "cic3d128comp" $ shareExp $ elimDead $ flatTAC $ genTAC (firCIC3D128Comp' reg (reg # reg # reg) (reg # reg) reg)
