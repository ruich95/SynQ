module Examples.FMDemod.UnwrapDiff

import SynQ
import Impl.TAC

%hide Linear.Interface.seq
%hide Prelude.(>>=)
%hide LState.(>>=)

inRange: (Comb comb, Primitive comb)
  => comb (BitVec 33) (BitVec 1, BitVec 1)
inRange = lam $ \diff => 
  prod (diff `lt` (const $ BV 0x6487ed51))
       ((const $ BV 0x19b7812af) `lt` diff)

unwrapDiffStg1: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 33) comb seq)
  -> seq (!* BitVec 33) (BitVec 1, BitVec 33) (BitVec 1, BitVec 33)
unwrapDiffStg1 (MkReg get set) = 
  abst $ \xin => do prev <- get
                    let en  = proj1 xin
                        cur = proj2 xin
                        diff = adder' cur (adder' (not prev) (const $ BV 1))
                    _ <- set $ mux21 en cur prev
                    pure $ prod en diff

unwrapDiffStg2: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 1, BitVec 33) comb seq)
  -> seq (LPair (!* BitVec 1) (!* BitVec 33)) 
         (BitVec 1, BitVec 33) 
         (BitVec 1, BitVec 33)
unwrapDiffStg2 (MkReg get set) = 
  abst $ \xin => do st <- get
                    let en   = proj1 st
                        diff = proj2 st
                        inRange = inRange << diff
                        inRangePos = proj1 inRange
                        inRangeNeg = proj2 inRange
                        out = mux21 (inRangePos `and` inRangeNeg)
                                diff
                                (mux21 ((not inRangePos) `and` inRangeNeg)
                                   (adder' diff (adder' (not $ const $ BV 0xc90fdaa2) (const $ BV 1)))
                                   (adder' diff (const $ BV 0xc90fdaa2)))
                    _ <- set xin
                    pure (prod en out)

unwrapDiff'': (Seq comb seq, Primitive comb)
  => (1 reg1: Reg (BitVec 33) comb seq)
  -> (1 reg2: Reg (BitVec 1, BitVec 33) comb seq)
  -> seq (LPair (!* BitVec 33) (LPair (!* BitVec 1) (!* BitVec 33)))
         (BitVec 1, BitVec 33) 
         (BitVec 1, BitVec 33)
unwrapDiff'' reg1 reg2 =  (unwrapDiffStg2 reg2) <<< (unwrapDiffStg1 reg1)

buf: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 1, BitVec 32) comb seq)
  -> seq (LPair (!* BitVec 1) (!* BitVec 32)) 
         (BitVec 1, BitVec 32) (BitVec 1, BitVec 32)
buf (MkReg get set) = 
  abst $ \x => do o <- get
                  _ <- set x
                  pure o
                  
inTrunc: (Comb comb, Primitive comb)
  => comb (BitVec 1, BitVec 32) (BitVec 1, BitVec 33)
inTrunc = lam $ \x =>
  let dat = proj2 x
      sign = slice 31 32 dat
  in prod (proj1 x)
          (concat sign $ proj2 x)

outTrunc: (Comb comb, Primitive comb)
  => comb (BitVec 1, BitVec 33) (BitVec 1, BitVec 32)
outTrunc = lam $ \x =>
  let dat = proj2 x
  in prod (proj1 x)
          (slice 0 32 dat)

export
UnwrapDiffSt: Type
UnwrapDiffSt = (LPair (LPair (!* BitVec 33) $ LPair (!* BitVec 1) (!* BitVec 33)) $ LPair (!* BitVec 1) (!* BitVec 32))

%hint
export
UnwrapDiffStIsSt: St UnwrapDiffSt
UnwrapDiffStIsSt = LP (LP LV (LP LV LV)) (LP LV LV)


export
UnwrapDiffRegs: (Type -> Type -> Type) -> (Type -> Type -> Type -> Type) -> Type
UnwrapDiffRegs comb seq = LPair (Reg (BitVec 33) comb seq) $ 
                          LPair (Reg (BitVec 1, BitVec 33) comb seq)
                                (Reg (BitVec 1, BitVec 32) comb seq)

export
unwrapDiffRegs: UnwrapDiffRegs TACComb TACSeq
unwrapDiffRegs = reg # reg # reg

export
unwrapDiff': (Seq comb seq, Primitive comb)
  => (1 regs: UnwrapDiffRegs comb seq)
  -> seq UnwrapDiffSt 
         (BitVec 1, BitVec 32) 
         (BitVec 1, BitVec 32)
unwrapDiff' (reg1 # reg2 # bufReg) = 
  (buf bufReg) <<< ((pure outTrunc) =<< (unwrapDiff'' reg1 reg2) =<< (pure inTrunc))

-- emitLLVMIR: IO ()
-- emitLLVMIR = dumpLLVMIR "unwrap_diff" $ shareExp $ elimDead $ flatTAC $ genTAC (unwrapDiff reg reg reg)

-- emitVerilog: IO ()
-- emitVerilog = dumpVerilog "unwrap_diff" $ shareExp $ elimDead $ flatTAC $ genTAC (unwrapDiff reg reg reg)
