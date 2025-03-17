import Data.SQData
  
data Repr: Type -> Type -> Type where
  Lam: {auto aSig: Sig a} -> {auto bSig: Sig b} -> (Repr () a -> Repr () b) -> Repr a b
  App: {auto aSig: Sig a} -> {auto bSig: Sig b} -> Repr a b -> Repr () a -> Repr () b
  Val: {auto aSig: Sig a} -> {auto bSig: Sig b} -> a -> Repr () a
  Prod : {auto aSig: Sig a} -> {auto bSig: Sig b} -> Repr () a -> Repr () b -> Repr () (a, b)
  Proj1: {auto aSig: Sig a} -> {auto bSig: Sig b} -> Repr () (a, b) -> Repr () a
  Proj2: {auto aSig: Sig a} -> {auto bSig: Sig b} -> Repr () (a, b) -> Repr () b
  Unit': {auto aSig: Sig a} -> {auto bSig: Sig b} -> Repr () ()
  

-- badFn: Const Int -> Repr () Int
-- badFn (Add x y) = Val $ V 0
-- badFn (V i) = Val $ V 1


-- One: Const Int
-- One = V 1

-- One': Const Int
-- One' = Add (V 1) (V 0)

-- p': Const a -> a
-- p' (Add x y) = (p' x) + (p' y)
-- p' (V i) = i

-- interp: Repr a b -> a -> b
-- interp (Lam {aTy = (Add _ _)} f) y = (interp $ f (V y)) ()
-- interp (Lam {aTy = (V _)} f) y     = (interp $ f (V y)) ()
-- interp (App f z) y                 = let f' = interp f 
--                                          z' = interp z
--                                      in (f' . z') ()
-- interp (Val (Add x z)) y = p' (Add x z)
-- interp (Val (V i)) y = i
-- interp (Prod x z) y = ((interp x $ ()), (interp z $ ()))
-- interp (Proj1 x) y = fst (interp x $ ())
-- interp (Proj2 x) y = snd (interp x $ ())
-- interp Unit' y = y
