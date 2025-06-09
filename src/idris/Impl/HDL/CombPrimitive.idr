module Impl.HDL.CombPrimitive

import Sym.Comb.CombPrimitive

import Impl.HDL.Module
import Impl.HDL.Port
import Impl.HDL.NetList

import Data.Name
import Data.Value
import Data.BitVec
import Data.Nat

import Control.Monad.State

addDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec $ S n)
addDecl = MkModuleDecl 
            "add" ["LEN"] 
            (CP (SP (NM "add_in_1") n UV) (SP (NM "add_in_2") n UV)) 
            (SP (NM "add_out") (S n) UV)

concatDecl: {m:_} -> {n:_} 
  -> ModuleDecl (BitVec m, BitVec n) (BitVec $ m + n)
concatDecl = MkModuleDecl 
            "concat" ["LEN1", "LEN2"] 
            (CP (SP (NM "concat_in_1") m UV) (SP (NM "concat_in_2") n UV)) 
            (SP (NM "concat_out") (m + n) UV)

notDecl: {n:_}
  -> ModuleDecl (BitVec n) (BitVec n)
notDecl = MkModuleDecl 
            "not_comp" ["LEN"] 
            (SP (NM "not_comp_in_1") n UV)
            (SP (NM "not_comp_out") n UV)

andDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec n)
andDecl = MkModuleDecl 
            "and_comp" ["LEN"] 
            (CP (SP (NM "and_comp_in_1") n UV) (SP (NM "and_comp_in_2") n UV)) 
            (SP (NM "and_comp_out") n UV)

orDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec n)
orDecl = MkModuleDecl 
            "or_comp" ["LEN"] 
            (CP (SP (NM "or_comp_in_1") n UV) (SP (NM "or_comp_in_2") n UV)) 
            (SP (NM "or_comp_out") n UV)

xorDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec n)
xorDecl = MkModuleDecl 
            "xor_comp" ["LEN"] 
            (CP (SP (NM "xor_comp_in_1") n UV) (SP (NM "xor_comp_in_2") n UV)) 
            (SP (NM "xor_comp_out") n UV)

sliceDecl: {n:_} -> (lower: Nat) -> (upper: Nat) 
      -> {auto 0 prf_upper: LTE upper n}
      -> {auto 0 prf_lower: LTE lower upper}
      -> ModuleDecl (BitVec n) (BitVec $ minus upper lower)
sliceDecl lower upper = 
   MkModuleDecl 
     "slice" ["LEN", "LOWER", "UPPER"] 
     (SP (NM "slice_in_1") n UV)
     (SP (NM "slice_out") (minus upper lower) UV)

eqDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec 1)
eqDecl = MkModuleDecl 
           "eq" ["LEN"] 
           (CP (SP (NM "eq_in_1") n UV) (SP (NM "eq_in_2") n UV)) 
           (SP (NM "eq_out") 1 UV)

ltuDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec 1)
ltuDecl = MkModuleDecl 
           "ltu" ["LEN"] 
           (CP (SP (NM "ltu_in_1") n UV) (SP (NM "ltu_in_2") n UV)) 
           (SP (NM "ltu_out") 1 UV)

ltDecl: {n:_} -> ModuleDecl (BitVec n, BitVec n) (BitVec 1)
ltDecl = MkModuleDecl 
           "lt" ["LEN"] 
           (CP (SP (NM "lt_in_1") n UV) (SP (NM "lt_in_2") n UV)) 
           (SP (NM "lt_out") 1 UV)

sllDecl: {n:_} -> ModuleDecl (BitVec n) (BitVec n)
sllDecl = MkModuleDecl 
           "sll" ["LEN", "SHAMT"] 
           (SP (NM "sll_in_1") n UV)
           (SP (NM "sll_out") n UV)
                                                                          
srlDecl: {n:_} -> ModuleDecl (BitVec n) (BitVec n)
srlDecl = MkModuleDecl 
           "srl" ["LEN", "SHAMT"] 
           (SP (NM "srl_in_1") n UV)
           (SP (NM "srl_out") n UV)                                                                                 

sraDecl: {n:_} -> ModuleDecl (BitVec n) (BitVec n)
sraDecl = MkModuleDecl 
           "sra" ["LEN", "SHAMT"] 
           (SP (NM "sra_in_1") n UV)
           (SP (NM "sra_out") n UV)           
           
mux21Decl: {n:_} 
 -> ModuleDecl (BitVec 1, BitVec n, BitVec n) 
               (BitVec n)
mux21Decl = MkModuleDecl 
             "mux21_comp" ["LEN"] 
             (CP (SP (NM "mux21_comp_sel") 1 UV) 
                 (CP (SP (NM "mux21_comp_in_1") n UV) 
                     (SP (NM "mux21_comp_in_2") n UV)))
             (SP (NM "mux21_comp_out") n UV)           

public export
Primitive Combinational where
  const x = MkComb 
    $ ST $ \c 
      => Id (c, {oPort := SP UN n (V x)} emptyCNL)
  
  add x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) (S n) UV
                        adder = instinate 
                                  addDecl
                                  c [n] 
                                  (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [adder]))
                                   
  concat x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) (m + n) UV
                        concat = instinate 
                                   concatDecl
                                   c [m, n]
                                   (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [concat]))
  
  not x = MkComb 
    $ do x' <- genComb x
         ST $ \c => let oP = SP (NM $ show c) n UV 
                        not = instinate 
                                notDecl 
                                c [n] 
                                x'.oPort oP
                    in Id (S c, MkCNL (UP UN) oP 
                                  x'.assignedPorts 
                                  (x'.instModules ++ [not]))
    
  and x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) n UV
                        and = instinate andDecl c [n]
                                (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [and]))
  
  or x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) n UV
                        or = instinate orDecl c [n]
                                (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [or]))
  
  xor x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) n UV
                        xor = instinate xorDecl c [n]
                                (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [xor]))
  
         
  slice lower upper x = MkComb 
    $ do x' <- genComb x
         ST $ \c => let oP = SP (NM $ show c) 
                                (minus upper lower) UV 
                        slice = instinate 
                                  (sliceDecl lower upper) 
                                  c [n, lower, upper] 
                                  x'.oPort oP
                    in Id (S c, MkCNL (UP UN) oP 
                                  x'.assignedPorts 
                                  (x'.instModules ++ [slice]))
  eq x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) 1 UV
                        eq = instinate 
                               eqDecl 
                               c [n] 
                               (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [eq]))
  ltu x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) 1 UV
                        ltu = instinate 
                                ltuDecl 
                                c [n] 
                                (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [ltu]))
                                   
  lt x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) 1 UV
                        lt = instinate 
                                ltDecl 
                                c [n] 
                                (CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                  (x'.assignedPorts ++ 
                                   y'.assignedPorts)
                                  (x'.instModules ++ 
                                   y'.instModules ++ 
                                   [lt]))
                                   
  mux21 b x y = MkComb 
    $ do b' <- genComb b
         x' <- genComb x
         y' <- genComb y
         ST $ \c => let oP = SP (NM $ show c) n UV
                        mux21 = instinate 
                                  mux21Decl 
                                  c [n] 
                                  (CP b'.oPort 
                                    $ CP x'.oPort y'.oPort) oP
                    in Id (S c, MkCNL (UP UN) oP
                                      (b'.assignedPorts ++ 
                                       x'.assignedPorts ++ 
                                       y'.assignedPorts)
                                      (b'.instModules ++ 
                                       x'.instModules ++ 
                                       y'.instModules ++ 
                                       [mux21]))
                                       
  shiftLL sht x = MkComb 
    $ do x' <- genComb x
         ST $ \c => let oP = SP (NM $ show c) n UV 
                        sll = instinate sllDecl 
                                  c [n, sht] 
                                  x'.oPort oP
                    in Id (S c, MkCNL (UP UN) oP 
                                  x'.assignedPorts 
                                  (x'.instModules ++ [sll]))

  shiftRL sht x = MkComb 
    $ do x' <- genComb x
         ST $ \c => let oP = SP (NM $ show c) n UV 
                        srl = instinate srlDecl 
                                  c [n, sht] 
                                  x'.oPort oP
                    in Id (S c, MkCNL (UP UN) oP 
                                  x'.assignedPorts 
                                  (x'.instModules ++ [srl]))

    
  shiftRA sht x = MkComb 
    $ do x' <- genComb x
         ST $ \c => let oP = SP (NM $ show c) n UV 
                        sra = instinate sraDecl 
                                  c [n, sht] 
                                  x'.oPort oP
                    in Id (S c, MkCNL (UP UN) oP 
                                  x'.assignedPorts 
                                  (x'.instModules ++ [sra]))

