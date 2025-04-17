import Data.SQData
  
data Repr: Type -> Type -> Type where
  Lam: {auto aSig: Sig a} -> {auto bSig: Sig b} 
    -> (Repr () a -> Repr () b) -> Repr a b
  App: {auto aSig: Sig a} -> {auto bSig: Sig b} 
    -> Repr a b -> Repr () a -> Repr () b
  Prod: {auto aSig: Sig a} -> {auto bSig: Sig b} 
    -> Repr () a -> Repr () b -> Repr () (a, b)
  Unit': Repr () ()
  Val: {n: _} -> (BitVec n) -> Repr () (BitVec n)
  Add: {n: _} -> Repr () (BitVec n) -> Repr () (BitVec n)
    -> Repr () (BitVec $ S n)
    
typeA: (a : Type) -> (tm: Repr a b) -> Sig a
typeA a (Lam {aSig} f) = aSig
typeA () _ = U

typeB: (b : Type) -> (tm: Repr a b) -> Sig b
typeB b (Lam {bSig} f) = bSig
typeB b (App {bSig} x y) = bSig
typeB () Unit' = U
typeB (a, b) (Prod x y) = ?rhs
typeB (BitVec n) (Val x) = BV
typeB (BitVec (S n)) (Add x y) = BV

badFn: {n:_} -> Repr (BitVec n) (BitVec n)
badFn = 
  Lam $ \x => case x of 
                Val k => Val $ BV 0
                (Add y z) => Val $ BV 1
                _ => x

one: {n:_} -> Repr () (BitVec $ S n)
one = Val $ BV 1

one': {n:_} -> Repr () (BitVec $ S n)
one' = Add (Val $ BV 1) (Val $ BV 0)

t1: {n:_} -> Repr () (BitVec $ S n)
t1 = App badFn one

t2: {n:_} -> Repr () (BitVec $ S n)
t2 = App badFn one'

abst: {_ :Sig a} -> Repr () a -> a

lift: {auto aSig :Sig a} -> a -> Repr () a
lift {aSig = U} x = Unit'
lift {aSig = (P y z)} x = Prod (lift $ fst x) (lift $ snd x)
lift {aSig = BV} x = Val x

interp: Repr a b -> a -> b
interp (Lam {aSig} f) x = interp (f $ lift x) $ ()
interp (App (Lam f) z) _ = interp (f z) ()
interp (App y z) _ = (interp y) $ (interp z) ()
interp (Prod x y) _ = ?rhs3
interp Unit' _ = ()
interp (Val y) _ = y
interp (Add y z) _ = 
  let (BV y') = interp y () 
      (BV z') = interp z () 
  in BV (y' + z')

prf: forall n . (Main.interp Main.one $ ()) = (Main.interp Main.one' $ ())
prf = Refl
