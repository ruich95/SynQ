module Examples.FMDemod.Mixer

import SynQ
import Impl.TAC
import Examples.FMDemod.Mult18

%hide Linear.Interface.seq
%hide Prelude.(>>=)

export
MixerSt': Type
MixerSt' = ((BitVec 18, BitVec 18), BitVec 36)

export
MixerSt: Type
MixerSt = LPair (LPair (!* BitVec 18) (!* BitVec 18)) (!* BitVec 36)

%hint
export
MixerStIsSt: St MixerSt
MixerStIsSt = LP (LP LV LV) LV

mixer: (Seq comb seq, Mult18 comb, Primitive comb)
  => (1 reg: Reg MixerSt' comb seq)
  -> (lo: comb () (BitVec 18))
  -> (sig: comb () (BitVec 16))
  -> seq MixerSt () (BitVec 36)
mixer (MkReg get set) lo sig = 
  do st <- get 
     let curA = proj1 $ proj1 st
         curB = proj2 $ proj1 st
         curO = proj2 st
         nxtA: (comb () (BitVec 18)) = concat sig (const $ BV 0)
         nxtB = lo
         nxtO = mult18 curA curB
     _ <- set $ prod (prod nxtA nxtB) nxtO
     pure curO

export
mixer': (Seq comb seq, Mult18 comb, Primitive comb)
  => (1 reg: Reg MixerSt' comb seq)
  -> seq MixerSt (BitVec 18, BitVec 16) (BitVec 36)
mixer' reg = abst $ \x => mixer reg (proj1 x) (proj2 x)

emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "mixer" $ shareExp $ elimDead $ flatTAC $ genTAC (mixer' reg)
