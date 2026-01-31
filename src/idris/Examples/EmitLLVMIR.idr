import SynQ
import Impl.TAC

%hide Linear.Interface.seq

sys: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 7) comb seq)
  -> (seq (!* BitVec 7) (BitVec 7) (BitVec 7, BitVec 6))
sys (MkReg get set) = 
  abst $ \x => 
    do prev <- get 
       let sum = adder' prev x
       _ <- set sum
       pure $ (prod sum (slice 1 7 $ shiftRA 3 sum))
       
emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "sys" $ shareExp $ elimDead $ flatTAC $ genTAC (sys reg)

emitPP: IO ()
emitPP = ppDump "sys" $ pprint $ shareExp $ elimDead $ flatTAC $ genTAC (sys reg)
