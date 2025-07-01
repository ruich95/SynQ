module Impl.HDL.NetList

import Impl.HDL.Port
import Impl.HDL.Module
import Impl.HDL.LPort

import Control.Monad.State
import Data.Name

import Data.LState2
import Data.LC

public export
record CombNL a b where
  constructor MkCNL
  iPort: TPort a
  oPort: TPort b
  assignedPorts: List PortAssign
  instModules  : List ModuleInst

export
emptyCNL: CombNL () ()
emptyCNL = MkCNL (UP UN) (UP UN) [] []

export
(.): CombNL b c -> CombNL a b -> CombNL a c
(.) g f = 
  let p = fromTPA $ TPA g.iPort f.oPort
  in MkCNL f.iPort g.oPort 
           (f.assignedPorts ++ g.assignedPorts ++ [p])
           (f.instModules ++ g.instModules)
           
-- do not touch IO
replaceInnerPortCNL: 
     (p: Port) -> (prfp: SimplePort p)
  -> (q: Port) -> (prfq: SimplePort q) 
  -> CombNL a b -> CombNL a b
replaceInnerPortCNL p prfp q prfq nl = 
  let fPA = replacePortAssignWith p prfp q prfq 
      fM  = replacePortInModule p prfp q prfq 
  in {assignedPorts $= map fPA, instModules $= map fM} nl

replaceAllInnerPortCNL': 
  List (p':Port ** (q':Port ** (SimplePort p', SimplePort q'))) -> CombNL a b -> CombNL a b
replaceAllInnerPortCNL' [] nl = nl
replaceAllInnerPortCNL' ((p ** (q ** (prfp, prfq))) :: xs) nl = 
  replaceAllInnerPortCNL' xs (replaceInnerPortCNL p prfp q prfq nl)
  
replaceAllInnerPortCNL: (p: TPort c) -> (q: TPort c) 
  -> CombNL a b -> CombNL a b
replaceAllInnerPortCNL p q nl = 
  let pairs = flatT p q 
  in replaceAllInnerPortCNL' pairs nl
  
replaceTPort': List (b:Type ** (p':TPort b ** (q':TPort b ** (SimpleTPort p', SimpleTPort q'))))
  -> (p: TPort a) -> TPort a
replaceTPort' [] p = p
replaceTPort' ((b ** (p' ** (q' ** (prfp, prfq)))) :: xs) p = 
  replaceTPort' xs (replaceTPortWith p' prfp q' prfq p)
  
replaceTPort: (p: TPort b) -> (q: TPort b)
  -> (pp: TPort a) -> TPort a
replaceTPort p q pp = 
  let pairs = flatTP p q 
  in replaceTPort' pairs pp 

public export infixr 9 <<=

export
(<<=): CombNL b c -> CombNL a b -> CombNL a c
(<<=) g f = 
  let g' = replaceAllInnerPortCNL g.iPort f.oPort g
      oP = replaceTPort g.iPort f.oPort g.oPort
  in MkCNL f.iPort oP -- g.oPort 
           (f.assignedPorts ++ g'.assignedPorts)
           (f.instModules ++ g'.instModules)


public export
record Combinational a b where
  constructor MkComb
  genComb: State Nat (CombNL a b)

public export
data NetList: Type -> Type -> Type -> Type where
  MkNL: (iPort: TPort a) -> (oPort: TPort b)
     -> (1 lPort: LPort s)
     -> (assignedPorts: List PortAssign)
     -> (instModules  : List ModuleInst)
     -> NetList s a b

public export
fromComb: CombNL a b -> (1 lPort: LPort s) 
       -> NetList s a b
fromComb comb lPort = 
  MkNL comb.iPort comb.oPort lPort 
       comb.assignedPorts comb.instModules
       
public export
unpackSeqNL: (1 _: NetList s a b) 
          -> LC (LPort s) (CombNL a b)
unpackSeqNL (MkNL iPort oPort lPort 
                  assignedPorts instModules) = 
  lPort # MkCNL iPort oPort 
                assignedPorts instModules

public export
record Sequential s a b where
  constructor MkSeq
  1 genSeq: LState2 Nat (NetList s a b)
  
public export
genSeq': (1 _: Sequential s a b) -> LState2 Nat (NetList s a b)
genSeq' (MkSeq f) = f
