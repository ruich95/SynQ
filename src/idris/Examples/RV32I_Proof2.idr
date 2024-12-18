module Examples.RV32I_Proof2

import Examples.RV32I
import Examples.RV32I.RegFile

import SynQ

getRegF': (1 _: LPair RegF StateType) -> RegF
getRegF' (x # y) = 
  let () = stConsume {sIsState= LP (LP LV LV) (LP LV (LP LV (LP LV LV)))} y 
  in x
  
getRegF: (1 _: LC (LPair RegF StateType) a) -> RegF
getRegF (l # _) = getRegF' l

rdRegF': {comb: _} -> {seq: _} 
  -> (RegFile comb seq, Seq comb seq, Primitive comb)
  => (idx: comb () $ BitVec 5)
  -> seq RegF () $ BitVec 32
rdRegF' idx = (pure $ lam proj1) =<< read idx idx

rdRegF: (BitVec 5) -> LState RegF (BitVec 32)
rdRegF = runSeq (abst rdRegF' {comb=Eval.Combinational} {seq=Eval.Sequential})

prop_add: (en: BitVec 1) -> (pc: BitVec 32) -> (inst: BitVec 32)
  -> (reg_file: RegF)
  -> (ctx_en: en = BV 1)
  -> (funct7: (bvSlice 25 32 inst) = BV 0)
  -> (funct3: (bvSlice 12 15 inst) = BV 0)
  -> (opcode: (bvSlice 0  7  inst) = BV 51)
  -> (getRegF $ runState (rv32iFn (en, inst, pc)) (reg_file # initSt)) = reg_file
prop_add en pc inst reg_file ctx_en funct7 funct3 opcode
  =  rewrite ctx_en in 
     rewrite funct7 in 
     rewrite funct3 in 
     rewrite opcode in 
     ?rhs_prop
