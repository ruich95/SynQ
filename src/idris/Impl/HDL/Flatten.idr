module Impl.HDL.Flatten

import Data.List
import Data.String
import Data.Nat
import Data.Linear

import Impl.HDL.Port
import Impl.HDL.LPort
import Impl.HDL.Module
import Impl.HDL.NetList


import Data.Name
import Data.Value
import Data.BitVec
import Data.LC

public export
data AtomicPort: Type where
  AP: Name -> (len: Nat) -> Value len -> AtomicPort

lemma: (m:Nat) -> (n:Nat) -> (equalNat m n = True) -> m = n
lemma 0 0 prf = Refl
lemma 0 (S k) prf impossible
lemma (S k) 0 prf impossible
lemma (S k) (S j) prf = eqSucc k j (lemma k j prf)

public export
Eq AtomicPort where
  (==) (AP nm1 len1 val1) (AP nm2 len2 val2) with (len1 == len2) proof prf
    (==) (AP nm1 len1 val1) (AP nm2 len2 val2) | False = False
    (==) (AP nm1 len1 val1) (AP nm2 len2 val2) | True 
      = let prf' = lemma len1 len2 prf
            val2' = rewrite prf' in val2
        in (nm1 == nm2) && (val1 == val2')

Show AtomicPort where
  show (AP UN len UV) = "unknown"
  show (AP nm len (V x)) = show x
  show (AP (NM str) len UV) = str ++ "|\{show len}"

public export
record AtomicPortAssign where
  constructor APA
  lhs: AtomicPort
  rhs: AtomicPort

public export
Eq AtomicPortAssign where
  (==) (APA lhs1 rhs1) (APA lhs2 rhs2) 
    = (lhs1 == lhs2) && (rhs1 == rhs2)

Show AtomicPortAssign where
  show (APA lhs rhs) = "\{show lhs} := \{show rhs}"
      
public export
record FlattenModuleInst where
  constructor MkFlattenModule
  name: String
  idx : Nat
  params: List (String, Nat)
  iPA: List AtomicPortAssign
  oPA: List AtomicPortAssign
  
Show FlattenModuleInst where
  show (MkFlattenModule name idx params iPA oPA) 
    = let nmStr = name ++ "_\{show idx}"
          paramsStr = joinBy ", " $ map (\x => "(\{fst x}: \{show (snd x)})") params
          iPAStr = joinBy ", " $ map (show) iPA
          oPAStr = joinBy ", " $ map (show) oPA
      in "\{nmStr} [params: \{paramsStr}; inputs: \{iPAStr}; outputs: \{oPAStr};]"

public export
record FlattenCombNL where
  constructor MkFCNL
  iPort: List AtomicPort
  oPort: List AtomicPort
  assignedPorts: List AtomicPortAssign
  instModules  : List FlattenModuleInst

export
Show FlattenCombNL where
  show (MkFCNL iPort oPort assignedPorts instModules) 
    = let iPStr = joinBy ", " $ map (show) iPort
          oPStr = joinBy ", " $ map (show) oPort
          aPStr = joinBy ", " $ map (show) assignedPorts
          mIStr = joinBy ", " $ map (show) instModules
      in "{input: \{iPStr}; output: \{oPStr}; assigns: \{aPStr}; modules: \{mIStr};}"

export
flatPort: Port -> List AtomicPort
flatPort (SP nm len val) = [AP nm len val]
flatPort (CP p1 p2) = (flatPort p1) 
                   ++ (flatPort p2)
flatPort (UP nm) = []

flatPortAssign: PortAssign -> List AtomicPortAssign
flatPortAssign (PA (SP lnm llen lval) (SP rnm rlen rval)) 
  = [APA (AP lnm llen lval) (AP rnm rlen rval)]
flatPortAssign (PA (CP lp1 lp2) (CP rp1 rp2)) 
  =  flatPortAssign (PA lp1 rp1) 
  ++ flatPortAssign (PA lp2 rp2) 
flatPortAssign _ = []

flatModuleInst: ModuleInst -> FlattenModuleInst
flatModuleInst (MkModuleInst name idx params iPA oPA) 
  = MkFlattenModule name idx params (flatPortAssign iPA) (flatPortAssign oPA)

export
flatCombNL: CombNL a b -> FlattenCombNL 
flatCombNL (MkCNL iPort oPort assignedPorts instModules) 
  = MkFCNL (flatPort $ fromTP iPort) 
           (flatPort $ fromTP oPort)
           (flatPortAssign =<< assignedPorts) 
           (map flatModuleInst instModules)

public export
record FlattenNetList where
  constructor MkFNL
  iPort: List AtomicPort
  oPort: List AtomicPort
  lPort: List AtomicPortAssign
  assignedPorts: List AtomicPortAssign
  instModules  : List FlattenModuleInst

flatLPorts: (1 _: LPort s) -> !* (List AtomicPortAssign)
flatLPorts (MkLP prf (MkBang lpIn) (MkBang lpOut)) 
  = MkBang ((flatPortAssign . fromTPA) $ TPA lpIn lpOut)
  
public export
flatNetList: (1 _: NetList s a b) -> (!* FlattenNetList)
flatNetList nl = 
  let (lp # combNL) = unpackSeqNL nl
      MkBang lPorts = flatLPorts lp
      MkFCNL i o ap im = flatCombNL combNL
  in MkBang (MkFNL i o lPorts ap im)
  
export
unpackNetList: FlattenNetList -> (FlattenCombNL, List AtomicPortAssign)
unpackNetList (MkFNL iPort oPort lPort assignedPorts instModules) = 
  (MkFCNL iPort oPort assignedPorts instModules, lPort)
