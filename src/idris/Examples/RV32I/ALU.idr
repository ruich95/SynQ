module Examples.RV32I.ALU

import SynQ

import Examples.RV32I.Common

barrelShtGen: {comb:_} -> (Comb comb, Primitive comb)
   => (n: Nat) 
   -> (shtFn: Nat -> comb () (BitVec 32) -> comb () (BitVec 32))
   -> (sht: comb () $ BitVec 5)
   -> (dat: comb () $ BitVec 32)
   -> comb () $ BitVec 32
barrelShtGen 0 shtFn sht dat = dat -- ?sll'_rhs_0
barrelShtGen (S k) shtFn sht dat = 
  mux21 (eq sht (const $ fromInteger $ cast (S k)))
        (shtFn (S k) dat)
        (barrelShtGen k shtFn sht dat) 

alu': {comb:_} -> (Comb comb, Primitive comb)
  => comb (BitVec 10, BitVec 32, BitVec 32) $ BitVec 32
alu' = 
  lam {aIsSig = P BV (P BV BV)} $ \ins => 
    let aluop = proj1 ins
        op1 = proj1 $ proj2 ins
        op2 = proj2 $ proj2 ins
    in mux21 (test 0 aluop) 
             (adder op1 op2)
      (mux21 (test 1 aluop) 
             (adder op1 
                   (adder (not op2) $ const 1))
      (mux21 (test 2 aluop) 
             (mux21 (lt op1 op2) 
                    (const 1) 
                    (const 0)) 
      (mux21 (test 3 aluop)
             (mux21 (ltu op1 op2) 
                    (const 1) 
                    (const 0))
      (mux21 (test 4 aluop) 
             (xor op1 op2)
      (mux21 (test 5 aluop) 
             ((barrelShtGen 31 shiftLL) (slice 0 5 op2) op1)
      (mux21 (test 6 aluop) 
             ((barrelShtGen 31 shiftRL) (slice 0 5 op2) op1)
      (mux21 (test 7 aluop) 
             ((barrelShtGen 31 shiftRA) (slice 0 5 op2) op1)
      (mux21 (test 8 aluop)
             (or op1 op2)
             (and op1 op2)))))))))

public export
alu: {comb:_} -> (Comb comb, Primitive comb)
  => (opcode: comb () $ BitVec 7)
  -> (aluop: comb () $ BitVec 10)
  -> (op1: comb () $ BitVec 32)
  -> (rs2Data: comb () $ BitVec 32)
  -> (imm: comb () $ BitVec 32)
  -> comb () $ BitVec 32
alu opcode aluop op1 rs2Data imm = 
  let op2 = mux21 (eq opcode $ instToOpCode RR) rs2Data imm
  in app alu' (prod aluop (prod op1 op2))


-- aluC: {comb:_} -> (Comb comb, Primitive comb)
--   => comb (BitVec 7, BitVec 10, 
--            BitVec 32, BitVec 32, 
--            BitVec 32) 
--           $ BitVec 32
-- aluC = lam {aIsSig = P BV (P BV (P BV (P BV BV)))} 
--   $ \ins => 
--          let opcode = proj1 ins
--              aluop  = proj1 $ proj2 ins
--              op1 = proj1 $ proj2 $ proj2 ins
--              rs2Data = proj1 $ proj2 $ proj2 $ proj2 ins
--              imm = proj2 $ proj2 $ proj2 $ proj2 ins
--          in alu opcode aluop op1 rs2Data imm
