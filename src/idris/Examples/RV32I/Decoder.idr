module Examples.RV32I.Decoder

import SynQ

import Examples.RV32I.Common

%hide Prelude.concat

public export
decoderAluOp: {comb:_} -> (Primitive comb)
           => (opcode: comb () $ BitVec 7)
           -> (funct3: comb () $ BitVec 3)
           -> (funct7: comb () $ BitVec 7)
           -> comb () $ BitVec 10
decoderAluOp opcode funct3 funct7 = 
  mux21 (eq funct3 (const $ BV 0))
        (mux21 (eq opcode $ instToOpCode RI)
               (aluOpEncode ADD)
               (mux21 (eq funct7 (const $ BV 32))
                      (aluOpEncode SUB)   -- sub
                      (aluOpEncode ADD)))  -- add
 (mux21 (eq funct3 (const $ BV 1))
        (aluOpEncode SLL)          -- sll
 (mux21 (eq funct3 (const $ BV 2))
        (aluOpEncode SLT)          -- slt
 (mux21 (eq funct3 (const $ BV 3))
        (aluOpEncode SLTU)         -- sltu
 (mux21 (eq funct3 (const $ BV 4))
        (aluOpEncode XOR)          -- xor
 (mux21 (eq funct3 (const $ BV 5)) 
        (mux21 (eq funct7 (const $ BV 32))
               (aluOpEncode SRA) -- sra
               (aluOpEncode SRL)) -- srl
 (mux21 (eq funct3 (const $ BV 6))
        (aluOpEncode OR)        -- or
        (aluOpEncode AND)))))))  -- and
        

decoderImm': {comb:_} -> (Primitive comb)
         => (mode: ImmMode)
         -> (rd:     comb () $ BitVec 5)
         -> (funct3: comb () $ BitVec 3)
         -> (rs1:    comb () $ BitVec 5)
         -> (rs2:    comb () $ BitVec 5)
         -> (funct7: comb () $ BitVec 7)
         -> comb () $ BitVec 32
decoderImm' I_IMM _ _ _ rs2 funct7 = 
  signExt 20 (concat funct7 rs2)
decoderImm' S_IMM rd _ _ _  funct7 = 
  signExt 20 (concat funct7 rd)
decoderImm' B_IMM rd _ _ _  funct7 = 
  let b11    = test 0 rd 
      b_4_0  = rd `and` (not $ const $ BV 1)
      b12    = test 6 funct7
      b_10_5 = slice 0 6 funct7
      imm    = concat (concat b12 b11) 
                      (concat b_10_5 b_4_0)
  in signExt 19 imm
decoderImm' U_IMM _ funct3 rs1 rs2 funct7 = 
  let imm = concat (concat funct7 rs2)
                   (concat rs1 funct3)
  in concat imm (const 0)
decoderImm' J_IMM _ funct3 rs1 rs2 funct7 = 
  let b_19_12 = concat rs1 funct3
      b11     = test 0 rs2
      b20     = test 6 funct7
      b_10_0  = concat (slice 0 6 funct7) 
                       (and rs2 (not $ const 1))
      imm = concat (concat b20 b_19_12)
                   (concat b11 b_10_0)
  in signExt 11 imm

public export
decoderImm: {comb:_} -> (Primitive comb)
         => (opcode: comb () $ BitVec 7)
         -> (rd:     comb () $ BitVec 5)
         -> (funct3: comb () $ BitVec 3)
         -> (rs1:    comb () $ BitVec 5)
         -> (rs2:    comb () $ BitVec 5)
         -> (funct7: comb () $ BitVec 7)
         -> comb () $ BitVec 32
decoderImm opcode rd funct3 rs1 rs2 funct7 = 
  mux21 (or (eq opcode $ instToOpCode RI) 
        (or (eq opcode $ instToOpCode LOAD) 
            (eq opcode $ instToOpCode JALR)))
        (decoderImm' I_IMM rd funct3 rs1 rs2 funct7)
        
 (mux21 (eq opcode $ instToOpCode STORE) 
        (decoderImm' S_IMM rd funct3 rs1 rs2 funct7)
        
 (mux21 (eq opcode $ instToOpCode B) 
        (decoderImm' B_IMM rd funct3 rs1 rs2 funct7)
        
 (mux21 (or (eq opcode $ instToOpCode LUI) 
            (eq opcode $ instToOpCode AUIPC))
        (decoderImm' U_IMM rd funct3 rs1 rs2 funct7)
        
 (mux21 (eq opcode $ instToOpCode JAL)
        (decoderImm' J_IMM rd funct3 rs1 rs2 funct7)
        (const $ BV 0)))))
        
public export        
decoderRd: {comb:_} -> (Primitive comb)
        => (opcode: comb () $ BitVec 7)
        -> (rd: comb () $ BitVec 5)
        -> comb () $ BitVec 5
decoderRd opcode rd = 
  mux21 (or (or
        (or (eq opcode $ instToOpCode JAL)
            (eq opcode $ instToOpCode JALR))
            
        (or (eq opcode $ instToOpCode AUIPC) 
            (eq opcode $ instToOpCode LUI)))
        
        (or (eq opcode $ instToOpCode RI) 
            (eq opcode $ instToOpCode RR)))
        rd
        (const $ BV 0)
