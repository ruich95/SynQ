module Impl.HDL.Port

import Data.Signal
import Data.BitVec
import Data.Value
import Data.Name

public export
data Port: Type where
  SP: Name -> (len: Nat) -> Value len -> Port
  CP: Port -> Port -> Port
  UP: Name -> Port
  
%name Port p1, p2

public export
record PortAssign where
  constructor PA
  lhs: Port
  rhs: Port

namespace TPort
  public export
  data TPort: Type -> Type where
    SP: Name -> (len: Nat) -> Value len -> TPort (BitVec len)
    CP: TPort a -> TPort b -> TPort (a, b)
    UP: Name -> TPort ()
  
  export
  Eq (TPort a) where
    (==) (SP nm1 len val1) (SP nm2 len val2) = (nm1 == nm2) && (val1 == val2)
    (==) (CP p11 p12) (CP p21 p22) 
      = (p11 == p21) && (p12 == p22)
    (==) (UP nm1) (UP nm2) 
      = nm1 == nm2
    (==) _ _ = False
  
  export
  fromSig: Sig a -> (nm: String) -> TPort a
  fromSig U nm = UP UN
  fromSig (P x y) nm = CP (fromSig x ("\{nm}_0")) 
                          (fromSig y ("\{nm}_1"))
  fromSig (BV {n})  nm = SP (NM nm) n UV
  
  export
  genUnKnown: Sig a -> TPort a
  genUnKnown U = UP UN
  genUnKnown (P x y) = 
    CP (genUnKnown x)
       (genUnKnown y)
  genUnKnown (BV {n}) = SP UN n UV
  
  
  export
  fromSig': Sig a -> (id: Nat) -> (Nat, TPort a)
  fromSig' U id = (id, UP UN)
  fromSig' (P x y) id = 
    let (id', p1)  = (fromSig' x id)
        (id'', p2) = (fromSig' y id')
    in  (id'', CP p1 p2)
  fromSig' (BV {n}) id = (S id, SP (NM (show id)) n UV)
  
  export
  portLike: TPort a -> (nm: String) -> TPort a
  portLike (SP nm1 len val) nm = SP (NM nm) len val
  portLike (CP p1 p2) nm = CP (portLike p1 ("\{nm}_0")) 
                              (portLike p2 ("\{nm}_1"))
  portLike (UP nm1) nm = UP (NM nm)
  
  export
  portLike': TPort a -> (id: Nat) -> (Nat, TPort a)
  portLike' (SP nm1 len val) id = (S id, SP (NM $ show id) len val)
  portLike' (CP p1 p2) id = 
    let (id', p1')  = (portLike' p1 id)
        (id'', p2') = (portLike' p2 id')
    in  (id'', CP p1 p2)
  portLike' (UP nm1) id = (S id, UP (NM $ show id))
  
  public export
  record TPortAssign a where
    constructor TPA
    lhs: TPort a
    rhs: TPort a
  
  %name TPort p1, p2
    
export
fromTP: TPort a -> Port
fromTP (SP nm len val) = SP nm len val
fromTP (CP p1 p2)      = CP (fromTP p1) (fromTP p2)
fromTP (UP nm)         = UP nm

export
fromTP': TPort a -> Port
fromTP' (SP UN len UV) = UP UN
fromTP' (SP UN len (V x)) = SP UN len (V x)
fromTP' (SP (NM str) len val) = SP (NM str) len val
fromTP' (CP p1 p2)      = CP (fromTP' p1) (fromTP' p2)
fromTP' (UP nm)         = UP nm

export
fromSig: Sig a -> (nm: String) -> Port
fromSig x nm = fromTP $ fromSig x nm

export
fromSig': Sig a -> (id: Nat) -> (Nat, Port)
fromSig' x id = let (id', p) = TPort.fromSig' x id 
                in (id', fromTP $ p)

export
fromTPA: TPortAssign a -> PortAssign
fromTPA (TPA lhs rhs) = PA (fromTP lhs) (fromTP rhs)

export
fromTPA': TPortAssign a -> PortAssign
fromTPA' (TPA lhs rhs) = PA (fromTP' lhs) (fromTP' rhs)

assign: (lhs: TPort a) -> (rhs: TPort a) -> PortAssign
assign lhs rhs = PA (fromTP lhs) (fromTP rhs)

lemma: (m: Nat) -> (n: Nat) -> equalNat m n = True -> m = n
lemma 0 0 prf = Refl
lemma 0 (S k) prf impossible
lemma (S k) 0 prf impossible
lemma (S k) (S j) prf = cong S (lemma k j prf)

export
Eq Port where
  (==) (SP nm1 len1 val1) (SP nm2 len2 val2) with (len1 == len2) proof p
    (==) (SP nm1 len1 val1) (SP nm2 len2 val2) | False = False
    (==) (SP nm1 len1 val1) (SP nm2 len2 val2) | True = 
      let prf = lemma len1 len2 p 
          val2' = rewrite prf in val2
      in (nm1 == nm2) && (val1 == val2')
  (==) (CP p11 p12) (CP p21 p22) 
    = (p11 == p21) && (p12 == p22)
  (==) (UP nm1) (UP nm2) 
    = nm1 == nm2
  (==) _ _ = False
  
  
public export
data SimplePort: Port -> Type where
  IsSP: SimplePort (SP _ _ _)

-- replace all occurance of p in pp with q
export
replacePortWith: (p: Port) -> (prfp: SimplePort p)
  -> (q: Port) -> (prfq: SimplePort q) 
  -> (pp: Port) -> Port
replacePortWith p@(SP _ _ _) IsSP q@(SP _ _ _) IsSP pp@(SP nm len val) = 
  if pp == p then q else pp 
replacePortWith p@(SP _ _ _) IsSP q@(SP _ _ _) IsSP (CP p1 p2) 
  = CP (replacePortWith p IsSP q IsSP p1)
       (replacePortWith p IsSP q IsSP p2)
replacePortWith p@(SP _ _ _) IsSP q@(SP _ _ _) IsSP pp@(UP nm) = pp

export
replacePortAssignWith: (p: Port) -> (prfp: SimplePort p)
  -> (q: Port) -> (prfq: SimplePort q) 
  -> (pa: PortAssign) -> PortAssign
replacePortAssignWith p@(SP _ _ _) IsSP q@(SP _ _ _) IsSP (PA lhs rhs) = 
  PA (replacePortWith p IsSP q IsSP lhs)
     (replacePortWith p IsSP q IsSP rhs)

public export
data SameShape: Port -> Port -> Type where
  SSP: SameShape (SP _ len _) (SP _ len _)
  SCP: SameShape p1 q1 -> SameShape p2 q2 -> SameShape (CP p1 p2) (CP q1 q2)
  SUP: SameShape (UP _) (UP _)

export
flat: (p: Port) -> (q: Port) -> (same: SameShape p q) 
  -> List (p':Port ** (q':Port ** (SimplePort p', SimplePort q')))
flat p@(SP _ len _) q@(SP _ len _) SSP = [(p ** (q ** (IsSP, IsSP)))]
flat (CP p1 p2) (CP q1 q2) (SCP x y) = flat p1 q1 x ++ flat p2 q2 y
flat (UP _) (UP _) SUP = []

export
sameTypeSameShape: (p: TPort a) -> (q: TPort a) -> SameShape (fromTP p) (fromTP q)
sameTypeSameShape p@(SP nm len val) (SP nm1 len val1) = SSP
sameTypeSameShape p@(CP p1 p2) (CP q1 q2) = SCP (sameTypeSameShape p1 q1) (sameTypeSameShape p2 q2)
sameTypeSameShape p@(UP nm) (UP nm1) = SUP
-- sameTypeSameShape _ _  = absurd (the Void (believe_me ()))

export 
flatT: (p: TPort a) -> (q: TPort a) 
  -> List (p':Port ** (q':Port ** (SimplePort p', SimplePort q')))
flatT p q = flat (fromTP p) (fromTP q) (sameTypeSameShape p q)





