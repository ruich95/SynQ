module Examples.FMDemod.Mult18

import SynQ
import Impl.TAC
import Impl.HDL.Module
import Impl.HDL.Port
import Impl.HDL.NetList
import Data.Name
import Data.Value
import Control.Monad.State

public export
interface Mult18 (0 comb: Type -> Type -> Type) where
  mult18: comb () (BitVec 18) -> comb () (BitVec 18)
       -> comb () (BitVec 36)

public export       
mult18Decl: ModuleDecl (BitVec 18, BitVec 18) (BitVec 36)
mult18Decl = MkModuleDecl 
            "mult18" [] 
            (CP (SP (NM "mult18_in_1") 18 UV) (SP (NM "mult18_in_2") 18 UV)) 
            (SP (NM "mult18_out") 36 UV)
       
public export
Mult18 HDL.NetList.Combinational where
  mult18 x y = 
    MkComb $ do x' <- genComb x
                y' <- genComb y
                ST $ \c => let oP = SP (NM $ show c) 36 UV
                               mult = instinate 
                                        mult18Decl c [] 
                                        (CP x'.oPort y'.oPort) oP
                            in Id (S c, MkCNL (UP UN) oP
                                     (x'.assignedPorts ++ 
                                      y'.assignedPorts)
                                     (x'.instModules ++ 
                                      y'.instModules ++ 
                                     [mult]))
public export                        
Mult18 Eval.Eval.Combinational where
  mult18 (MkComb x) (MkComb y) = MkComb $ Prelude.const $ bvMult18 (x ()) (y ())

public export                        
Mult18 TACComb where
  mult18 (MkTACC x) (MkTACC y) = 
    MkTACC $ do 
      (MkTAC _ outX _ opsX) <- x
      (MkTAC _ outY _ opsY) <- y
      dst <- GenTAC.genVar (Impl.TAC.Data.BvTy $ 36)
      let op = TAC.MULT outX outY dst
      pure $ MkTAC U dst (MkSt U)
                    (opsX ++ opsY ++ [op])
