module Examples.RV32I_Proof

import SynQ

import Examples.RV32I
import Examples.RV32I.Common
import Examples.RV32I.Decoder
import Examples.RV32I.ALU

-- import Impl.Compile

%language ElabReflection

UnRTy: Type
UnRTy = (((BitVec 32),                                 -- pc
            (BitVec 5, BitVec 5)),                       -- rs1 rs2
           ((BitVec 32, BitVec 32),                      -- r1Data r2Data
            (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved

-- unpack: {comb:_} -> (Comb comb, Primitive comb)
--   => comb () UnRTy
--   -> (((comb () $ BitVec 32), 
--        (comb () $ BitVec 5, 
--         comb () $ BitVec 5)),
--        (comb () $ BitVec 32, 
--         comb () $ BitVec 32),
--        (comb () $ BitVec 5, 
--         comb () $ BitVec 32, 
--         comb () $ BitVec 32, 
--         comb () $ BitVec 3))
-- unpack ins = (((proj1 $ proj1 ins), 
--                (proj1 $ proj2 $ proj1 ins, 
--                 proj2 $ proj2 $ proj1 ins)),
--                (proj1 $ proj1 $ proj2 ins,
--                 proj2 $ proj1 $ proj2 ins),
--                (proj1 $ proj2 $ proj2 ins, 
--                 proj1 $ proj2 $ proj2 $ proj2 ins, 
--                 proj1 $ proj2 $ proj2 $ proj2 $ proj2 ins, 
--                 proj2 $ proj2 $ proj2 $ proj2 $ proj2 ins))
                
getPC:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 32)
getPC x = proj1 $ proj1 x

getRS1:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 5)
getRS1 xs = proj1 . proj2 . proj1 $ xs

getRS2:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 5)
getRS2 xs = proj2 . proj2 . proj1 $ xs

getR1Data:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 32)
getR1Data xs = proj1 $ proj1 $ proj2 xs

getR2Data:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 32)
getR2Data xs = proj2 $ proj1 $ proj2 xs

getRSaved:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 5)
getRSaved xs = proj1 $ proj2 $ proj2 xs

getDSaved:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 32)
getDSaved xs = proj1 $ proj2 $ proj2 $ proj2 xs

getPCSaved:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 32)
getPCSaved xs = proj1 $ proj2 $ proj2 $ proj2 $ proj2 xs

getFn3Saved:  {comb:_} -> (Comb comb, Primitive comb)
  => comb () UnRTy
  -> comb () (BitVec 3)
getFn3Saved xs = proj2 $ proj2 $ proj2 $ proj2 $ proj2 xs

rv32iComb: {comb:_} -> (Comb comb, Primitive comb)
  => (en: comb () $ BitVec 1)
  -> (opcode:  comb () $ BitVec 7)   --**************
  -> (funct3:  comb () $ BitVec 3)   -- unpacked raw 
  -> (funct7:  comb () $ BitVec 7)   --**************
  -> (inStg2:  comb () $ BitVec 1)   --**************
  -> (store:   comb () $ BitVec 1)   -- context            
  -> (rd: comb () $ BitVec 5)
  -> comb (((BitVec 32),                                -- pc
            (BitVec 5, BitVec 5)),                      -- rs1 rs2
           ((BitVec 32, BitVec 32),                     -- r1Data r2Data
            (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
          ((((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
             (BitVec 32)),                      -- pc
             (BitVec 5, BitVec 32)),            -- rd rData
            ((BitVec 1, BitVec 1),              -- inStg2 store
             (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
rv32iComb en opcode funct3 funct7 inStg2 store rd
  = lam $ \ins => 
        let pc        = getPC ins
            rs1       = getRS1 ins
            rs2       = getRS2 ins
            r1Data    = getR1Data ins
            r2Data    = getR2Data ins
            regSaved  = getRSaved ins
            dataSaved = getDSaved ins
            pcSaved   = getPCSaved ins
            fn3Saved  = getFn3Saved ins
        in rv32iCombFlat en opcode rd funct3 rs1 rs2 funct7 pc 
                         inStg2 store pcSaved regSaved dataSaved fn3Saved
                         r1Data r2Data
                         

combAdd: {comb:_} -> (Comb comb, Primitive comb)
  => (rd: comb () $ BitVec 5)
  -> comb (((BitVec 32),                                -- pc
            (BitVec 5, BitVec 5)),                      -- rs1 rs2
           ((BitVec 32, BitVec 32),                     -- r1Data r2Data
            (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
          ((((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
             (BitVec 32)),                      -- pc
             (BitVec 5, BitVec 32)),            -- rd rData
            ((BitVec 1, BitVec 1),              -- inStg2 store
             (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved
combAdd rd = 
  let en: comb () (BitVec 1) = const $ BV 1
      opcode: comb () (BitVec 7) = instToOpCode RR
      funct3: comb () (BitVec 3) = const $ BV 0
      funct7: comb () (BitVec 7) = const $ BV 0
      inStg2: comb () (BitVec 1) = const $ BV 0
      store : comb () (BitVec 1) = const $ BV 0
  in rv32iComb en opcode funct3 funct7 inStg2 store rd
  

InTy: Type
InTy = (BitVec 5,  --rd
       (((BitVec 32),                                -- pc
         (BitVec 5, BitVec 5)),                      -- rs1 rs2
        ((BitVec 32, BitVec 32),                     -- r1Data r2Data
         (BitVec 5, BitVec 32, BitVec 32, BitVec 3)))) -- regSaved dataSaved pcSaved fn3Saved

OutTy: Type
OutTy = ((((BitVec 1, BitVec 32, BitVec 32),  -- wen waddr wdata
             (BitVec 32)),                      -- pc
             (BitVec 5, BitVec 32)),            -- rd rData
            ((BitVec 1, BitVec 1),              -- inStg2 store
             (BitVec 5, BitVec 32, BitVec 32, BitVec 3))) -- regSaved dataSaved pcSaved fn3Saved

combAddFn: InTy -> OutTy
combAddFn = runComb $ lam $ \xs => app (combAdd (proj1 xs)) (proj2 xs)

getInRd: InTy -> BitVec 5
getInRd x = fst x

getOutRd: OutTy -> BitVec 5
getOutRd x = fst $ snd $ fst x

lemma1: forall n. (bvOr (BV {n=n} 0) (BV {n=n} 0)) = BV {n=n} 0

lemma2: {n:_} -> (bvOr {n=n} (BV 0) (BV 1)) = BV {n=n} 1

lemma3: (bvNot {n=1} (BV 1)) = BV 0

lemma4: (bvOr {n=1} (bvOr {n=1} (bvOr {n=1} (BV 0) (BV 0)) 
                                (bvOr {n=1} (BV 0) (BV 0))) 
                    (bvOr {n=1} (BV 0) (BV 1))) 
      = BV {n=1} 1
lemma4 = rewrite lemma2 {n=1} in 
         rewrite lemma1 {n=1} in 
         rewrite lemma1 {n=1} in 
         rewrite lemma2 {n=1} in Refl
         
lemma5: {n:_} -> (bvOr {n=n} (BV 1) (BV 0)) = BV {n=n} 1

prop_add_rd: (ins: InTy) -> getOutRd (combAddFn ins) = getInRd ins
prop_add_rd ins = rewrite lemma3 in rewrite lemma4 in Refl

getInRData: InTy -> (BitVec 32, BitVec 32)
getInRData x = fst $ snd $ snd x

getOutRData: OutTy -> BitVec 32
getOutRData x = snd $ snd $ fst x

lemma6: bvSlice {n=10} 0 1 (BV 1) = BV 1

prop_add_rdata: (ins: InTy) -> getOutRData (combAddFn ins) 
                            = (bvSlice 0 32 $ bvAdd (fst $ getInRData ins) 
                                                    (snd $ getInRData ins))
prop_add_rdata ins = rewrite lemma5 {n=1} in 
                     rewrite lemma1 {n=1} in 
                     rewrite lemma6 in Refl


-- -- prop_add_rd': (ins: InTy) -> getInRd (combAddFn' ins) = getInRd ins
