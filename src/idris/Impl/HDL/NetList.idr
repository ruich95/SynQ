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
