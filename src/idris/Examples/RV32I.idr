module Examples.RV32I

import SynQ

import Examples.RV32I.Common
import Examples.RV32I.Decoder
import Examples.RV32I.ALU
import Examples.RV32I.RegFile
import Examples.RV32I.Utils

-- import Sym.Comb
-- import Sym.CombPrimitive
-- import Sym.CombLib
-- import Sym.Seq
-- import Sym.SeqPrimitive
-- import Sym.SeqLib

-- import Data.LState

-- import Impl.Eval
-- import Impl.HDL

-- import Data.Bits
-- import Data.Linear
-- import Data.State

%hide Prelude.concat
%hide Prelude.(=<<)
%hide Prelude.pure
-- %hide Linear.seq

%language ElabReflection

packInst: {comb:_} -> (Comb comb, Primitive comb)
  => (opcode:  comb () $ BitVec 7)  --************
  -> (rd:      comb () $ BitVec 5)  --
  -> (funct3:  comb () $ BitVec 3)  -- unpacked raw 
  -> (rs1:     comb () $ BitVec 5)  -- binary inst
  -> (rs2:     comb () $ BitVec 5)  --
  -> (funct7:  comb () $ BitVec 7)  --************
  -> comb () $ BitVec 32
packInst opcode rd funct3 rs1 rs2 funct7 = 
  concat (concat (concat funct7 rs2)
                 (concat rs1 funct3))
         (concat rd opcode)


updatePcBr: {comb:_} -> (Comb comb, Primitive comb)
  => (funct3:  comb () $ BitVec 3)
  -> (imm:     comb () $ BitVec 32)
  -> (pc:      comb () $ BitVec 32)
  -> comb (BitVec 1, BitVec 1, BitVec 1) $ BitVec 32
updatePcBr funct3 imm pc = 
  lam $ \x => 
    let eq12  = proj1 x
        lt12  = proj1 $ proj2 x
        ltu12 = proj2 $ proj2 x
        condEq = (or (and (eq funct3 $ bopToFunct3 BEQ) eq12)
                     (and (eq funct3 $ bopToFunct3 BNE) (not eq12)))
        condLt = (or (and (eq funct3 $ bopToFunct3 BLT) lt12)
                     (and (eq funct3 $ bopToFunct3 BGE) (not lt12)))
        condLtu = (or (and (eq funct3 $ bopToFunct3 BLTU) ltu12)
                      (and (eq funct3 $ bopToFunct3 BGEU) (not ltu12)))
    in mux21 (or condEq (or condLt condLtu))
             (adder pc imm)
             (adder pc (const 4))

updatePC: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)
  -> (funct3:  comb () $ BitVec 3)
  -> (r1Data:  comb () $ BitVec 32)
  -> (r2Data:  comb () $ BitVec 32)
  -> (imm:     comb () $ BitVec 32)
  -> (pc:      comb () $ BitVec 32)
  -> (inStg2:  comb () $ BitVec 1)
  -> (pcSaved: comb () $ BitVec 32)
  -> comb () $ BitVec 32
updatePC en opcode funct3 r1Data r2Data imm pc inStg2 pcSaved = 
  mux21 (not en) (const 0)
 (mux21 inStg2 pcSaved -- restore previous pc
        (mux21 (or (eq opcode $ instToOpCode STORE) 
                   (eq opcode $ instToOpCode LOAD))
               (adder r1Data imm) -- pc to mem data address
        (mux21 (eq opcode $ instToOpCode JAL) 
               (adder pc imm)     -- pc + offset
        (mux21 (eq opcode $ instToOpCode JALR)
               (and (adder r1Data imm) (not $ const 1)) -- lsb -> 0 (rs1 (base) + imm (offset))
        (mux21 (eq opcode $ instToOpCode B)
               (app (updatePcBr funct3 imm pc)
                    (prod (eq r1Data r2Data) 
                          (prod (lt r1Data r2Data) 
                                (ltu r1Data r2Data))))
               (adder pc $ const 4)))))) -- default


ldMemCast: {comb:_} -> (Comb comb, Primitive comb)
  => (funct3: comb () $ BitVec 3)
  -> (memDat: comb () $ BitVec 32)
  -> comb () $ BitVec 32
ldMemCast funct3 memDat = 
  mux21 (eq funct3 $ memWidthToFunct3 MemH) 
        (signExt 16 $ slice 0 16 memDat)
 (mux21 (eq funct3 $ memWidthToFunct3 MemB) 
        (signExt 24 $ slice 0 8 memDat)
 (mux21 (eq funct3 $ memWidthToFunct3 MemHU) 
        (zeroExt 16 $ slice 0 16 memDat)
 (mux21 (eq funct3 $ memWidthToFunct3 MemBU)
        (zeroExt 24 $ slice 0 8 memDat)
        memDat)))

getRdData: {comb:_} -> (Comb comb, Primitive comb)
  => (opcode:  comb () $ BitVec 7)
  -> (fn3Saved:  comb () $ BitVec 3)
  -> (inStg2:  comb () $ BitVec 1)
  -> (store :  comb () $ BitVec 1)
  -> (aluRes:  comb () $ BitVec 32)
  -> (pc:      comb () $ BitVec 32)
  -> (memDat:  comb () $ BitVec 32)
  -> (imm:     comb () $ BitVec 32)
  -> comb () $ BitVec 32
getRdData opcode fn3Saved inStg2 store aluRes pc memDat imm = 
  mux21 inStg2 (mux21 store (const 0) (ldMemCast fn3Saved memDat))
        (mux21 (eq opcode $ instToOpCode LUI) 
               imm 
        (mux21 (eq opcode $ instToOpCode AUIPC)
               (adder pc imm) 
        (mux21 (or (eq opcode $ instToOpCode JAL)
                   (eq opcode $ instToOpCode JALR))
               (adder pc $ const 4)
        (mux21 (or (eq opcode $ instToOpCode RR)
                   (eq opcode $ instToOpCode RI))
               aluRes
               (const 0)))))

getRd: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode:   comb () $ BitVec 7)
  -> (inStg2:   comb () $ BitVec 1)
  -> (store :   comb () $ BitVec 1)
  -> (rd:       comb () $ BitVec 5)
  -> (regSaved: comb () $ BitVec 5)
  -> comb () $ BitVec 5
getRd en opcode inStg2 store rd regSaved = 
  mux21 (not en) (const 0)
 (mux21 (inStg2) 
        (mux21 store (const 0) regSaved) 
        (decoderRd opcode rd))

getWen: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (inStg2: comb () $ BitVec 1)
  -> (store : comb () $ BitVec 1)
  -> comb () $ BitVec 1
getWen en inStg2 store = 
  mux21 (not en) (const 0)
 (mux21 (inStg2) 
        (mux21 store (const 1) (const 0)) 
        (const 0))

stMemCast: {comb:_} -> (Comb comb, Primitive comb)
  => (funct3: comb () $ BitVec 3)
  -> (dataSaved: comb () $ BitVec 32)
  -> (memDat    : comb () $ BitVec 32)
  -> comb () $ BitVec 32
stMemCast funct3 dataSaved memDat =
  mux21 (eq funct3 $ memWidthToFunct3 MemH) 
        (concat (slice 16 32 memDat) (slice 0 16 dataSaved))
 (mux21 (eq funct3 $ memWidthToFunct3 MemB) 
        (concat (slice 8 32 memDat) (slice 0 8 dataSaved))
        dataSaved)

getWdata: {comb:_} -> (Comb comb, Primitive comb)
  => (fn3Saved: comb () $ BitVec 3)
  -> (inStg2: comb () $ BitVec 1)
  -> (store : comb () $ BitVec 1)
  -> (dataSaved: comb () $ BitVec 32)
  -> (memDat   : comb () $ BitVec 32)
  -> comb () $ BitVec 32
getWdata fn3Saved inStg2 store dataSaved memDat =
  mux21 (inStg2)
        (mux21 store (stMemCast fn3Saved dataSaved memDat) (const 0)) 
        (const 0)

getWaddr: {comb:_} -> (Comb comb, Primitive comb)
  => (pc: comb () $ BitVec 32)
  -> comb () $ BitVec 32
getWaddr = id


updatePcSaved: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (pc: comb () $ BitVec 32)
  -> comb () $ BitVec 32
updatePcSaved en pc = mux21 (not en) 
                            (const 0) 
                            (adder pc (const 4))

updateRegSaved: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode: comb () $ BitVec 7)
  -> (rs2:    comb () $ BitVec 5)
  -> (rd:     comb () $ BitVec 5)
  -> comb () $ BitVec 5
updateRegSaved en opcode rs2 rd = 
  mux21 (not en) (const 0)
 (mux21 (eq opcode $ instToOpCode STORE) rs2 rd)
  
updateDataSaved: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (r2Dat:  comb () $ BitVec 32)
  -> comb () $ BitVec 32
updateDataSaved en r2Dat = mux21 (not en) (const 0) r2Dat

updateFn3Saved: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (funct3:  comb () $ BitVec 3)
  -> comb () $ BitVec 3
updateFn3Saved en funct3 = mux21 (not en) (const 0) funct3

updateInStg2: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode: comb () $ BitVec 7)
  -> (inStg2: comb () $ BitVec 1)
  -> comb () $ BitVec 1
updateInStg2 en opcode inStg2 = 
  mux21 (not en) (const 0)
 (mux21 inStg2 (const 0)
        (mux21 (or (eq opcode $ instToOpCode STORE)
                   (eq opcode $ instToOpCode LOAD))
               (const 1) (const 0)))
               
updateStore: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode: comb () $ BitVec 7)
  -> (inStg2: comb () $ BitVec 1)
  -> comb () $ BitVec 1
updateStore en opcode inStg2 = 
  mux21 (not en) (const 0)
 (mux21 inStg2 (const 0)
        (mux21 (eq opcode $ instToOpCode STORE)
               (const 1) (const 0)))

rv32iComb': {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)   --**************
  -> (rd:      comb () $ BitVec 5)   --
  -> (funct3:  comb () $ BitVec 3)   -- unpacked raw 
  -> (rs1:     comb () $ BitVec 5)   -- binary inst
  -> (rs2:     comb () $ BitVec 5)   --
  -> (funct7:  comb () $ BitVec 7)   --**************
  -> (pc:      comb () $ BitVec 32)  --**************
  -> (inStg2:  comb () $ BitVec 1)   --**************
  -> (store:   comb () $ BitVec 1)   -- context            
  -> (pcSaved: comb () $ BitVec 32)  --  info
  -> (regSaved: comb () $ BitVec 5)  -- 
  -> (dataSaved:comb () $ BitVec 32) --
  -> (fn3Saved: comb () $ BitVec 3)  --**************
  -> (r1Data:   comb () $ BitVec 32)
  -> (r2Data:   comb () $ BitVec 32)
  -> (imm:      comb () $ BitVec 32)
  -> comb () ((((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
                (BitVec 32)),                      -- pc
                (BitVec 5, BitVec 32)),            -- rd rData
               ((BitVec 1, BitVec 1),              -- inStg2 store
                (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
rv32iComb' en opcode rd funct3 rs1 rs2 funct7 pc 
           inStg2 store pcSaved regSaved dataSaved fn3Saved
           r1Data r2Data imm 
  = let memDat = packInst opcode rd funct3 rs1 rs2 funct7
        wen    = getWen en inStg2 store
        wdata  = getWdata fn3Saved inStg2 store dataSaved memDat
        waddr  = getWaddr pc
        memSig = prod wen (prod waddr wdata)
        nextPc = updatePC en opcode funct3 r1Data r2Data imm pc inStg2 pcSaved
        --******************
        outSig = prod memSig nextPc
        --******************
        finalRd = getRd en opcode inStg2 store rd regSaved
        aluOp = decoderAluOp opcode funct3 funct7
        aluRes = alu opcode aluOp r1Data r2Data imm
        rdData = getRdData opcode fn3Saved inStg2 store aluRes pc memDat imm
        --******************
        regFSig = prod finalRd rdData
        --******************
        nextInStg2 = updateInStg2 en opcode inStg2
        nextStore  = updateStore en opcode inStg2
        --******************
        nextState = prod nextInStg2 nextStore
        --******************
        nextRegSaved = updateRegSaved en opcode rs2 rd
        nextDataSaved = updateDataSaved en r2Data
        nextPcSaved = updatePcSaved en pc
        nextFn3Saved = updateFn3Saved en funct3
        --******************
        nextContext = (prod nextRegSaved $ prod nextDataSaved $ prod nextPcSaved nextFn3Saved)
        --******************
    in prod (prod outSig regFSig) (prod nextState nextContext)
    
  
rv32iCombFlat: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)   --**************
  -> (rd:      comb () $ BitVec 5)   --
  -> (funct3:  comb () $ BitVec 3)   -- unpacked raw 
  -> (rs1:     comb () $ BitVec 5)   -- binary inst
  -> (rs2:     comb () $ BitVec 5)   --
  -> (funct7:  comb () $ BitVec 7)   --**************
  -> (pc:      comb () $ BitVec 32)  --**************
  -> (inStg2:  comb () $ BitVec 1)   --**************
  -> (store:   comb () $ BitVec 1)   -- context            
  -> (pcSaved: comb () $ BitVec 32)  --  info
  -> (regSaved: comb () $ BitVec 5)  -- 
  -> (dataSaved:comb () $ BitVec 32) 
  -> (fn3Saved: comb () $ BitVec 3) --**************
  -> (r1Data:   comb () $ BitVec 32)
  -> (r2Data:   comb () $ BitVec 32)
  -> comb () ((((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
                (BitVec 32)),                      -- pc
                (BitVec 5, BitVec 32)),            -- rd rData
               ((BitVec 1, BitVec 1),              -- inStg2 store
                (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
rv32iCombFlat en opcode rd funct3 rs1 rs2 funct7 pc 
              inStg2 store pcSaved regSaved dataSaved fn3Saved
              r1Data r2Data 
  = let comb = lam $ rv32iComb' en opcode rd funct3 rs1 rs2 funct7 pc 
                                inStg2 store pcSaved regSaved dataSaved fn3Saved
                                r1Data r2Data
        imm = decoderImm opcode rd funct3 rs1 rs2 funct7
    in app comb imm

rv32iComb: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)   --**************
  -> (rd:      comb () $ BitVec 5)   --
  -> (funct3:  comb () $ BitVec 3)   -- unpacked raw 
  -> (rs1:     comb () $ BitVec 5)   -- binary inst
  -> (rs2:     comb () $ BitVec 5)   --
  -> (funct7:  comb () $ BitVec 7)   --**************
  -> (pc:      comb () $ BitVec 32)  --**************
  -> comb ((BitVec 32, BitVec 32), 
           (BitVec 1, BitVec 1),
           (BitVec 5, BitVec 32, BitVec 32, BitVec 3))
          ((((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
             (BitVec 32)),                      -- pc
             (BitVec 5, BitVec 32)),            -- rd rData
            ((BitVec 1, BitVec 1),              -- inStg2 store
             (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
rv32iComb en opcode rd funct3 rs1 rs2 funct7 pc 
  = lam {aIsSig = prfHelper} $ \ins => 
      let regData   = proj1 ins 
          state   = proj1 $ proj2 ins
          saved = proj2 $ proj2 ins
      in rv32iCombFlat en opcode rd funct3 rs1 rs2 funct7 pc 
                      (proj1 state) (proj2 state) 
                      (proj1 $ proj2 $ proj2 saved) (proj1 saved) (proj1 $ proj2 saved) 
                      (proj2 $ proj2 $ proj2 saved)
                      (proj1 regData) (proj2 regData)
    where 
      prfHelper: Sig ((BitVec 32, BitVec 32),
                      (BitVec 1, BitVec 1),
                      (BitVec 5, BitVec 32, BitVec 32, BitVec 3))
      prfHelper = (P (P BV BV) (P (P BV BV) (P BV (P BV $ P BV BV))))

StateType: Type 
StateType = LPair (LPair (!* BitVec 1) (!* BitVec 1)) 
                  (LPair (!* BitVec 5) $ LPair (!* BitVec 32) 
                                               (LPair (!* BitVec 32) (!* BitVec 3)))

StateIOType: Type 
StateIOType =  ((BitVec 1, BitVec 1),
                (BitVec 5, BitVec 32, BitVec 32, BitVec 3))
                
initState: StateType
initState = (MkBang 0 # MkBang 0) # (MkBang 0 # (MkBang 0 # (MkBang 0 # MkBang 0)))
                
sameShape1: SameShape StateIOType StateType
sameShape1 = P (P BV BV) (P BV (P BV $ P BV BV))

rv32iInner: {comb:_} -> {seq:_} 
  -> (Comb comb, Primitive comb, Seq comb seq)
  => (1 reg: Reg comb seq)
  -> (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)   --**************
  -> (rd:      comb () $ BitVec 5)   --
  -> (funct3:  comb () $ BitVec 3)   -- unpacked raw 
  -> (rs1:     comb () $ BitVec 5)   -- binary inst
  -> (rs2:     comb () $ BitVec 5)   --
  -> (funct7:  comb () $ BitVec 7)   --**************
  -> (pc:      comb () $ BitVec 32)  --**************
  -> seq StateType (BitVec 32, BitVec 32) 
                   (((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
                     (BitVec 32)),                      -- pc
                     (BitVec 5, BitVec 32))             -- rd rData
rv32iInner reg en opcode rd funct3 rs1 rs2 funct7 pc 
  = let combPart = rv32iComb {comb=comb} en opcode rd funct3 rs1 rs2 funct7 pc
    in scan reg {similar=sameShape1} combPart

rv32i': {comb:_} -> {seq:_} 
  -> (Comb comb, Primitive comb, Seq comb seq)
  => (1 reg: Reg comb seq)
  -> (1 regFile: RegFile comb seq)
  -> (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)   --**************
  -> (rd:      comb () $ BitVec 5)   --
  -> (funct3:  comb () $ BitVec 3)   -- unpacked raw 
  -> (rs1:     comb () $ BitVec 5)   -- binary inst
  -> (rs2:     comb () $ BitVec 5)   --
  -> (funct7:  comb () $ BitVec 7)   --**************
  -> (pc:      comb () $ BitVec 32)  --**************
  -> seq (LPair RegF StateType) 
         () 
         ((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
           (BitVec 32))             -- pc
rv32i' reg (MkRF read write) en opcode rd funct3 rs1 rs2 funct7 pc 
  = let inner = rv32iInner {comb=comb} {seq=seq} reg en opcode rd funct3 rs1 rs2 funct7 pc 
        bypass = (pure $ lam id)
    in (bypass <<< (abst $ \ins => (pure $ proj1 ins) 
                               =<< write (proj1 $ proj2 ins) 
                                         (proj2 $ proj2 ins))) 
   =<< (inner  <<< (read rs1 rs2))

-- -- innerT: {comb:_} -> {seq:_} 
-- --   -> (Comb comb, Primitive comb, Seq comb seq)
-- --   => (1 reg: Reg comb seq)
-- --   -> (1 regFile: RegFile comb seq)
-- --   -> seq (LPair RegF StateType)  () 
-- --                    (((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
-- --                      (BitVec 32)))             -- rd rData
-- -- innerT reg regFile = rv32i' reg regFile(const 0) (const 1) (const 2) (const 3) (const 4) (const 5) (const 6)


unpackInst: {comb:_} -> (Comb comb, Primitive comb)
  => (inst: comb () $ BitVec 32)
  -> (comb () (BitVec 7), (comb () (BitVec 3), comb () (BitVec 7)), 
     (comb () (BitVec 5), comb () (BitVec 5), comb () (BitVec 5)))
unpackInst inst = -- here we use believe_me to accelecrate type checking by skip some known true proof
  let opcode = slice 0  7  {prf_upper= believe_me ()} {prf_lower= believe_me ()} inst
      rd     = slice 7  12 {prf_upper= believe_me ()} {prf_lower= believe_me ()} inst
      funct3 = slice 12 15 {prf_upper= believe_me ()} {prf_lower= believe_me ()} inst
      rs1    = slice 15 20 {prf_upper= believe_me ()} {prf_lower= believe_me ()} inst
      rs2    = slice 20 25 {prf_upper= believe_me ()} {prf_lower= believe_me ()} inst
      funct7 = slice 25 32 {prf_upper= believe_me ()} {prf_lower= believe_me ()} inst
  in (opcode, (funct3, funct7), (rd, rs1, rs2))

rv32i: {comb:_} -> {seq:_} 
  -> (Comb comb, Primitive comb, Seq comb seq)
  => (1 reg: Reg comb seq)
  -> (1 regFile: RegFile comb seq)
  -> seq (LPair RegF StateType) 
         (BitVec 1, BitVec 32, BitVec 32) -- en inst pc
         ((BitVec 1, BitVec 32, BitVec 32), (BitVec 32)) -- wen waddr wdata pc
rv32i reg regFile = 
  abst $ \ins => 
    let (opcode, (funct3, funct7), (rd, rs1, rs2)) = unpackInst (proj1 $ proj2 ins)
        pc = proj2 $ proj2 ins
        en = proj1 ins
    in rv32i' reg regFile en opcode rd funct3 rs1 rs2 funct7 pc


rv32iFn: (BitVec 1, BitVec 32, BitVec 32) 
  -> LState (LPair RegF StateType) 
            ((BitVec 1, BitVec 32, BitVec 32), (BitVec 32))
rv32iFn = runSeq (rv32i reg regFile)

initSt: LPair RegF StateType
initSt = (initRegF # initState)

main: IO ()
main = reactMealy readIn rv32iFn initSt

genVerilog: (nm: String) -> IO ()
genVerilog nm = writeVerilog nm (rv32i reg regFile)
