module Examples.FMDemod.DDC

import SynQ
import Data.Vect
import Examples.FMDemod.Mult18
import Examples.FMDemod.Mixer
import Examples.FMDemod.PipelinedCIC
import Examples.FMDemod.FIR
import Impl.TAC

%hide Linear.Interface.seq
%hide Data.LState.infixr.(<<<)

private infixl 9 <<<

DDCBranchSt: Type
DDCBranchSt = LPair MixerSt $ LPair CIC4d128St FIRSt64

CICRegsTy: (Type -> Type -> Type) -> (Type -> Type -> Type -> Type) -> Type
CICRegsTy comb seq = 
  LPair (CICIntRegs [44, 37, 31, 26] comb seq) 
    $ LPair (Reg (Decimator128St' 23) comb seq)
            (CICCombRegs [23, 22, 21, 20] comb seq)

CICCompRegsTy: (Type -> Type -> Type) -> (Type -> Type -> Type -> Type) -> Type
CICCompRegsTy comb seq = 
  LPair (Reg (BitVec 7) comb seq) 
    $ LPair (MACCRegs comb seq) 
        $ LPair (InBuf64Regs comb seq) (Reg CoefSt64' comb seq)

trunc: (Comb comb, Primitive comb)
  => comb (BitVec 36) (BitVec 16)
trunc = lam $ slice 20 36

buf: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 1, BitVec 18) comb seq)
  -> seq (LPair (!* BitVec 1) (!* BitVec 18))
         (BitVec 1, BitVec 18)
         (BitVec 1, BitVec 18)
buf (MkReg get set) = 
  abst $ \x => do st <- get
                  _ <- set x
                  pure st


ddcBranch: (Seq comb seq, Primitive comb, Mult18 comb)
  => (1 mixerReg: Reg MixerSt' comb seq)
  -> (1 cicRegs: CICRegsTy comb seq)
  -> (1 cicCompRegs: CICCompRegsTy comb seq)
  -> seq DDCBranchSt (BitVec 18, BitVec 16) (BitVec 1, BitVec 48)
ddcBranch mixerReg (intRegs # decReg # combReg) 
          (compStReg # maccRegs # inBufRegs # coefRegs) 
  = let mixer        = mixer' mixerReg
        cicDecimator = cic4d128' intRegs decReg combReg
        cicComp      = firCIC4D128Comp64' compStReg maccRegs inBufRegs coefRegs
    in cicComp <<< (cicDecimator =<< (pure trunc)) <<< mixer
    
-- DDCSt: Type
-- DDCSt = LPair DDCBranchSt DDCBranchSt

-- %ambiguity_depth 5

-- ddc: (Seq comb seq, Primitive comb, Mult18 comb)
--   => (1 mixerIReg: Reg MixerSt' comb seq)
--   -> (1 cicIRegs: CICRegsTy comb seq)
--   -> (1 cicCompIRegs: CICCompRegsTy comb seq)
--   -> (1 mixerQReg: Reg MixerSt' comb seq)
--   -> (1 cicQRegs: CICRegsTy comb seq)
--   -> (1 cicCompQRegs: CICCompRegsTy comb seq)
--   -> seq DDCSt ((BitVec 18, BitVec 18), BitVec 16) (BitVec 1, BitVec 48, BitVec 48)
-- ddc mixerIReg cicIRegs cicCompIRegs mixerQReg cicQRegs cicCompQRegs = 
--   abst $ \xin => 
--     let ddcI = ddcBranch mixerIReg cicIRegs cicCompIRegs
--         ddcQ = ddcBranch mixerQReg cicQRegs cicCompQRegs 
--         loI = proj1 $ proj1 xin
--         loQ = proj2 $ proj1 xin
--         sig = proj2 xin
--     in do resI <- (pure $ lam id) <<< (ddcI =<< (pure $ prod loI sig))
--           resQ <- (ddcQ =<< (pure $ prod loQ sig)) <<< (pure unit)
--           pure $ prod (proj1 resI) $ prod (proj2 resI) (proj2 resQ)

-- emitLLVMIR: IO ()
-- emitLLVMIR = dumpLLVMIR "ddc" 
--            $ shareExp 
--            $ elimDead 
--            $ flatTAC 
--            $ genTAC 
--            $ ddc reg 
--                  ((reg # reg # reg # reg) # reg # (reg # reg # reg # reg)) 
--                  (reg # (reg # reg # reg) # (reg # reg) # reg)
--                  reg 
--                  ((reg # reg # reg # reg) # reg # (reg # reg # reg # reg)) 
--                  (reg # (reg # reg # reg) # (reg # reg) # reg)
       

emitVerilog: IO ()
emitVerilog = dumpVerilog "ddc_branch" 
           $ shareExp 
           $ elimDead 
           $ flatTAC 
           $ genTAC 
           $ ddcBranch reg 
                 ((reg # reg # reg # reg) # reg # (reg # reg # reg # reg)) 
                 (reg # (reg # reg # reg) # (reg # reg) # reg)
