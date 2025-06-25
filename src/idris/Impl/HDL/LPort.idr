module Impl.HDL.LPort

import Data.Linear

import Data.State
import Impl.HDL.Port
import Data.BitVec
import Data.Name
import Data.Signal
import Data.Value
import Data.LC

public export
getType: St s -> (a: Type ** SameShape a s)
getType LU = (() ** U)
getType (LP st1 st2) = 
  ((fst $ getType st1, fst $ getType st2) 
  ** P (snd $ getType st1) (snd $ getType st2))
  -- let (ty1 ** prf1) = getType st1
  --     (ty2 ** prf2) = getType st2
  -- in ((ty1, ty2) ** P prf1 prf2)
getType (LV {n}) = (BitVec n ** BV)

public export
data LPort: Type -> Type where
  MkLP: (prf: SameShape a s)
      -> (1 lpIn: !* (TPort a)) 
      -> (1 lpOut: !* (TPort a))
      -> LPort s
      
stToSig: St s -> {auto prf: SameShape a s} -> Sig a
stToSig LU {prf = U} = U
stToSig (LP st1 st2) {prf = (P prfa prfb)} = 
  let p1 = stToSig st1 {prf=prfa} 
      p2 = stToSig st2 {prf=prfb} 
  in P p1 (stToSig st2)
stToSig LV {prf = BV} = BV

export
stToPort: St s -> (nm: String) -> {auto prf: SameShape a s} -> TPort a
stToPort st nm = fromSig (stToSig st) nm

export
stToPort': St s -> (idx: Nat) -> {auto prf: SameShape a s} -> (Nat, TPort a)
stToPort' st idx = fromSig' (stToSig st) idx

public export
fromSt: St s -> (nm: String) -> {auto prf: SameShape a s} -> LPort s
fromSt st nm = 
  let pi = stToPort st nm --"\{nm}_i" 
      po = stToPort st nm -- "\{nm}_o" 
  in MkLP prf (MkBang pi) (MkBang po)

public export
fromSt': St s -> (idx: Nat) -> {auto prf: SameShape a s} -> (Nat, LPort s)
fromSt' st idx = 
  let (_, pi)    = stToPort' st idx --"\{nm}_i" 
      (idx', po) = stToPort' st idx -- "\{nm}_o" 
  in (idx', MkLP prf (MkBang pi) (MkBang po))

public export
seqLP: (1 _: LPort s) -> (1 _: LPort s)
    -> (LC (LPort s) PortAssign)
seqLP (MkLP prf2 (MkBang lpIn2) (MkBang lpOut2)) 
      (MkLP prf1 lpIn1 (MkBang lpOut1)) 
  = let teq = sameShapeTrans prf2 prf1
        pa = fromTPA' $ TPA lpIn2 $ rewrite teq in lpOut1
        o2 = MkBang $ rewrite sym $ teq in lpOut2
    in MkLP prf1 lpIn1 o2 # pa

public export
parLP: (1 _: LPort s1) -> (1 _: LPort s2)
    -> (LPort (LPair s1 s2))
parLP (MkLP prf1 (MkBang lpIn1) (MkBang lpOut1)) 
      (MkLP prf2 (MkBang lpIn2) (MkBang lpOut2)) 
  = MkLP (P prf1 prf2) 
         (MkBang (CP lpIn1 lpIn2)) 
         (MkBang (CP lpOut1 lpOut2))

-- stLemma LU LU = Refl
-- stLemma (LP st11 st12) (LP st21 st22) = 
--   let p1 = stLemma st11 st21 
--       p2 = stLemma st12 st22
--   in rewrite p2 in (rewrite p1 in ?stLemma_rhs_4)
-- stLemma LV LV = Refl
