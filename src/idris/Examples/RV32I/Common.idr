module Examples.RV32I.Common

import SynQ

-- import Sym.Comb
-- import Sym.CombPrimitive
-- import Sym.CombLib

import Data.Bits

public export
data ALUOP: Type where
  ADD:  ALUOP
  SUB:  ALUOP
  SLT:  ALUOP
  SLTU: ALUOP
  XOR:  ALUOP
  SLL:  ALUOP
  SRL:  ALUOP
  SRA:  ALUOP
  OR:   ALUOP
  AND:  ALUOP

public export
aluOpEncode: {comb:_} -> (Primitive comb)
  => ALUOP -> comb () (BitVec 10)
aluOpEncode ADD  = const $ BV 1
aluOpEncode SUB  = const $ BV (shiftL 1 1)
aluOpEncode SLT  = const $ BV (shiftL 1 2)
aluOpEncode SLTU = const $ BV (shiftL 1 3)
aluOpEncode XOR  = const $ BV (shiftL 1 4)
aluOpEncode SLL  = const $ BV (shiftL 1 5)
aluOpEncode SRL  = const $ BV (shiftL 1 6)
aluOpEncode SRA  = const $ BV (shiftL 1 7)
aluOpEncode OR   = const $ BV (shiftL 1 8)
aluOpEncode AND  = const $ BV (shiftL 1 9)

public export
data ImmMode: Type where
  I_IMM: ImmMode
  S_IMM: ImmMode
  B_IMM: ImmMode
  U_IMM: ImmMode
  J_IMM: ImmMode

public export
data ALUSnd: Type where
  REG: ALUSnd
  IMM: ALUSnd
  
public export
aluSndEncode: {comb:_} -> (Primitive comb)
  => ALUSnd -> comb () (BitVec 1)
aluSndEncode REG = const 1
aluSndEncode IMM = const 0

public export
data InstTy: Type where
  RR:    InstTy
  RI:    InstTy
  STORE: InstTy
  LOAD:  InstTy
  B:     InstTy
  JAL:   InstTy
  JALR:  InstTy
  LUI:   InstTy
  AUIPC: InstTy
  
public export
instToOpCode: {comb:_} -> (Primitive comb) 
           => InstTy -> comb () $ BitVec 7
instToOpCode RR    = const 51  -- 0110011
instToOpCode RI    = const 19  -- 0010011
instToOpCode STORE = const 35  -- 0100011
instToOpCode LOAD  = const 3   -- 0000011
instToOpCode B     = const 99  -- 1100011
instToOpCode JAL   = const 111 -- 1101111
instToOpCode JALR  = const 103 -- 1100111
instToOpCode LUI   = const 55  -- 0110111
instToOpCode AUIPC = const 23  -- 0010111

lemma: (n: Nat) -> minus (S n) n = 1
lemma 0 = Refl
lemma (S k) = lemma k

lemma2: (n: Nat) -> LTE n (S n)
lemma2 0 = LTEZero
lemma2 (S k) = LTESucc (lemma2 k)

lemma3: (n: Nat) -> LTE n n
lemma3 0 = LTEZero
lemma3 (S k) = LTESucc (lemma3 k)

public export
adder: {n:_} -> {comb:_} -> (Comb comb, Primitive comb)
      => comb () (BitVec n) -> comb () (BitVec n)
      -> comb () (BitVec n)
adder x y = (lower {prf=lemma2 n} n)  << add x y


public export
test: {n:_} -> {comb:_} -> (Primitive comb)
   => (idx: Nat) -> {auto prf: LT idx n}
   -> comb () (BitVec n) -> comb () (BitVec 1)
test idx x = rewrite sym $ lemma idx 
             in slice idx (S idx) {prf_lower = lemma2 idx} x

public export
signExt: {n:_} -> {comb:_} -> (Primitive comb)
      => (m: Nat) -> comb () (BitVec n)
      -> comb () (BitVec $ m+n)
signExt {n = 0} m x = 
  rewrite plusCommutative m 0 
  in (const 0)
signExt {n = (S k)} m x = 
  let sign = mux21 (test {prf=lemma3 (S k)} k x) 
                   (not $ const 0)
                   (const 0)
  in concat sign x

public export
zeroExt: {n:_} -> {comb:_} -> (Primitive comb)
      => (m: Nat) -> comb () (BitVec n)
      -> comb () (BitVec $ m+n)
zeroExt {n = 0} m x = 
  rewrite plusCommutative m 0 
  in (const 0)
zeroExt {n = (S k)} m x = 
  CombPrimitive.concat (const 0) x

public export
data BOP: Type where
  BEQ : BOP
  BNE : BOP
  BLT : BOP
  BGE : BOP
  BLTU: BOP
  BGEU: BOP
  
public export
bopToFunct3: {comb:_} -> (Primitive comb) 
  => BOP -> comb () $ BitVec 3
bopToFunct3 BEQ  = (const 0)
bopToFunct3 BNE  = (const 1)
bopToFunct3 BLT  = (const 4)
bopToFunct3 BGE  = (const 5)
bopToFunct3 BLTU = (const 6)
bopToFunct3 BGEU = (const 7)

public export
data MemWidth: Type where
  MemW: MemWidth
  MemH: MemWidth
  MemB: MemWidth
  MemHU: MemWidth
  MemBU: MemWidth
  
public export
memWidthToFunct3: {comb:_} -> (Primitive comb) 
  => MemWidth -> comb () $ BitVec 3
memWidthToFunct3 MemW = (const 2)
memWidthToFunct3 MemH = (const 1)
memWidthToFunct3 MemB = (const 0)
memWidthToFunct3 MemHU = (const 5)
memWidthToFunct3 MemBU = (const 4)
