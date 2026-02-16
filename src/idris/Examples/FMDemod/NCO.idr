module Examples.FMDemod.NCO

import SynQ
import Impl.TAC

%hide Linear.Interface.seq

export
NCOSt': Type
NCOSt' = BitVec 24

export
NCOSt: Type
NCOSt = !* (BitVec 24)

export
%hint
NCOStIsSt: St NCOSt
NCOStIsSt = LV

idxDecode: (Comb comb, Primitive comb)
     => comb (BitVec 14) (BitVec 12)
idxDecode = 
  lam $ \idx => 
    let sign2 = slice 12 13 idx
        raw_idx  = slice 0 12 idx
    in mux21 sign2
         (adder' (const $ BV 4095)
                 (adder' (not raw_idx) 
                         (const $ BV 1)))
         raw_idx
                           
lutDecode: (Comb comb, Primitive comb)
     => comb (BitVec 14, BitVec 18) (BitVec 18)
lutDecode = 
  lam $ \ins => 
    let idx = proj1 ins
        dat = proj2 ins
        sign1 = slice 13 14 idx
    in mux21 sign1 dat
         (adder' (const $ BV 0x3ffff)
                 (adder' (not dat) 
                         (const $ BV 1)))


export
nco: (Seq comb seq, Primitive comb) 
 => (1 acc: Reg NCOSt' comb seq)
 -> (tw: comb () $ BitVec 24)
 -> seq NCOSt () (BitVec 14, BitVec 14)
nco (MkReg get set) tw = 
  do acc_val <- get
     let nxt_acc = adder' acc_val tw
         lo_i  = slice 10 24 acc_val
         lo_q  = slice 10 24 (adder' acc_val $ shiftLL 22 (const $ BV 1))
     _ <- set nxt_acc
     pure $ prod lo_i lo_q
     
emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "nco" $ shareExp $ elimDead $ flatTAC $ genTAC (abst $ nco reg)

idxDecode': (Seq comb seq, Primitive comb)
     => seq () (BitVec 14) (BitVec 12)
idxDecode' = pure idxDecode

idxDecIR: IO ()
idxDecIR = dumpLLVMIR "idxDec" $ shareExp $ elimDead $ flatTAC $ genTAC (idxDecode' {comb=TACComb})

lutDecode': (Seq comb seq, Primitive comb)
  => seq () (BitVec 14, BitVec 18) (BitVec 18)
lutDecode' = pure lutDecode

lutDecIR: IO ()
lutDecIR = dumpLLVMIR "lutDec" $ shareExp $ elimDead $ flatTAC $ genTAC (lutDecode' {comb=TACComb})

ncoVerilog: IO ()
ncoVerilog = dumpVerilog "nco_iq" $ shareExp $ elimDead $ flatTAC $ genTAC (abst $ nco reg)

idxDecVerilog: IO ()
idxDecVerilog = dumpVerilog "idx_decoder" $ shareExp $ elimDead $ flatTAC $ genTAC (idxDecode' {comb=TACComb})

lutDecVerilog: IO ()
lutDecVerilog = dumpVerilog "lut_decoder" $ shareExp $ elimDead $ flatTAC $ genTAC (lutDecode' {comb=TACComb})
