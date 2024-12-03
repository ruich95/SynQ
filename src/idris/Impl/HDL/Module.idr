module Impl.HDL.Module

import Impl.HDL.Port

import Data.List

public export
record ModuleDecl a b where
  constructor MkModuleDecl
  name  : String
  params: List String
  iPort : TPort a
  oPort : TPort b

public export
record ModuleInst where
  constructor MkModuleInst
  name: String
  idx : Nat
  params: List (String, Nat)
  iPA: PortAssign
  oPA: PortAssign
  

assignParams: List String -> List Nat -> List (String, Nat)
assignParams strs ks = zip strs ks

export  
instinate: ModuleDecl a b -> (idx: Nat) -> (param_vals: List Nat)
        -> (iPort: TPort a) -> (oPort: TPort b)
        -> ModuleInst
instinate (MkModuleDecl name params p1 p2) 
          idx param_vals 
          iPort oPort 
  = let aParams = assignParams params param_vals
        iPA = fromTPA $ (TPA p1 iPort)
        oPA = fromTPA $ (TPA p2 oPort)
    in MkModuleInst name idx aParams iPA oPA
    
