import Data.SQData

%default total

record Comb (repr: Type -> Type -> Type) where
  constructor CombComponents
  lam: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto notUnit: NotUnit a} 
    -> {auto bIsSig: Sig b} 
    -> (repr () a -> repr () b) -> repr a b
  app: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
    -> repr a b -> repr () a -> repr () b
  prod: {a:_} -> {b:_} 
     -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
     -> repr () a -> repr () b -> repr () (a, b)
  fst: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
    -> repr () (a, b) -> repr () a
  snd: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
    -> repr () (a, b) -> repr () b
  unit: repr () ()
  
  add: {n: _} -> repr () (BitVec n) -> repr () (BitVec n) -> repr () (BitVec $ S n)
  value: {n: _} -> BitVec n -> repr () (BitVec n) 
  
record CombL (repr: Type -> Type -> Type) where
  constructor CombLComponents
  lam: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto notUnit: NotUnit a} 
    -> {auto bIsSig: Sig b} 
    -> (repr () a -> repr () b) -> repr a b
  prod: {a:_} -> {b:_} 
     -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
     -> repr () a -> repr () b -> repr () (a, b)
  fst: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
    -> repr () (a, b) -> repr () a
  snd: {a:_} -> {b:_} 
    -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
    -> repr () (a, b) -> repr () b
  unit: repr () ()
  
  add: {n: _} -> repr () (BitVec n) -> repr () (BitVec n) -> repr () (BitVec $ S n)
  value: {n: _} -> BitVec n -> repr () (BitVec n) 

record V (repr: Type -> Type -> Type) (a: Type) where
  constructor Val
  val: repr () a

-- data V: (Type -> Type -> Type) -> Type -> Type where
--   Val: repr () a -> V repr a

data E: (Type -> Type -> Type) -> Type -> Type -> Type where
  F: {notUnit: NotUnit a} -> (V repr a -> V repr b) -> E repr a b
  C: V repr a -> E repr () a

lam: {repr: _} -> {a:_} -> {b:_} 
  -> {auto aIsSig: Sig a} -> {auto notUnit: NotUnit a} 
  -> {auto bIsSig: Sig b} 
  -> (cl: CombL repr) 
  -> (E repr () a -> E repr () b) -> E repr a b
lam cl f = F {notUnit = notUnit} $ 
  \x => let y = f (C x) 
        in case y of
                (F {notUnit = (NUnit prf)} g) 
                    => case prf Refl of _ impossible
                (C z) => z

app: {repr: _} -> (cl: CombL repr) 
  -> E repr a b -> E repr () a -> E repr () b
app cl (F f) (F {notUnit = (NUnit prf)} g) 
  = case prf Refl of _ impossible
app cl (F f) (C x) = C (f x)
app cl (C x) y = C x

prod: {repr: _} -> {a: _} -> {b: _}
   -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> (cl: CombL repr) 
   -> E repr () a -> E repr () b -> E repr () (a, b)
prod cl (F {notUnit = (NUnit prf)} f) y 
  = case prf Refl of _ impossible
prod cl (C x) (F {notUnit = (NUnit prf)} f) 
  = case prf Refl of _ impossible
prod cl (C $ Val x) (C $ Val y) = C $ Val $ cl.prod x y

fst: {repr: _} -> {a: _} -> {b: _}
  -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
  -> (cl: CombL repr) 
  -> E repr () (a, b) -> E repr () a
fst cl (F {notUnit = (NUnit prf)} f) 
  = case prf Refl of _ impossible
fst cl (C $ Val x) = C $ Val $ cl.fst x

snd: {repr: _} -> {a: _} -> {b: _}
  -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
  -> (cl: CombL repr) 
  -> E repr () (a, b) -> E repr () b
snd cl (F {notUnit = (NUnit prf)} f) 
  = case prf Refl of _ impossible
snd cl (C $ Val x) = C $ Val $ cl.snd x

unit: {repr: _} -> (cl: CombL repr) 
   -> E repr () ()
unit cl = C $ Val $ cl.unit

add: {repr: _} -> {n:_}
  -> (cl: CombL repr) 
  -> E repr () (BitVec n) -> E repr () (BitVec n) 
  -> E repr () (BitVec $ S n)
add cl (F {notUnit = (NUnit prf)} f) y 
  = case prf Refl of _ impossible
add cl (C x) (F {notUnit = (NUnit prf)} f) 
  = case prf Refl of _ impossible
add cl (C $ Val x) (C $ Val y) = C $ Val $ cl.add x y

value: {repr:_} -> {n: _}
    -> (cl: CombL repr)
    -> BitVec n -> E repr () (BitVec n)
value cl x = C $ Val $ cl.value x

-- implement Comb with CombL
impl: {repr: _} -> (cl: CombL repr) -> (Comb $ E repr)
impl cl =
  CombComponents 
    (lam cl) (app cl) (prod cl) (fst cl)
    (snd cl) (unit cl) (add cl)  (value cl)

abst: {repr: _} -> {a: _} -> {b: _}
   -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
   -> (cl: CombL repr) -> (t: E repr a b) -> repr a b
abst cl (F {notUnit} f) 
  = cl.lam $ \x => val $ f (Val x)
abst cl (C x) = val x

addPrf: {repr: _} -> {n:_} -> (cl: CombL repr) 
  -> (x: repr () $ BitVec n) -> (y: repr () $ BitVec n)
  -> (cl.add x y) = abst cl ((impl cl).add (C $ Val x) (C $ Val y))
addPrf cl x y = ?addPrf_rhs

norm: {a: _} -> {b: _}
 -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
 -> ({repr':_} -> Comb repr' -> repr' a b) 
 -> ({repr:_} ->  CombL repr -> repr a b)
norm f cl = abst cl $ f (impl cl)

record Eval a b where
  constructor MkEval
  eval: a -> b

eValue: {n:_} -> BitVec n -> Eval () (BitVec n)
-- eValue x = MkEval (\y => x)

eAdd: {n:_} -> Eval () (BitVec n) -> Eval () (BitVec n) -> Eval () $ BitVec (S n)

eUnit : Eval () ()
-- eUnit = MkEval (\x => x)

eSnd : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} -> Eval () (a, b) -> Eval () b

eFst : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} -> Eval () (a, b) -> Eval () a

eProd : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} -> Eval () a -> Eval () b -> Eval () (a, b)

eLam : {auto aIsSig: Sig a} -> {auto notUnit: NotUnit a} -> {auto bIsSig: Sig b} -> (Eval () a -> Eval () b) -> Eval a b

eApp : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} -> Eval a b -> Eval () a -> Eval () b
eApp (MkEval f) (MkEval x) = MkEval (\() => f (x ()))


evalImpl: Comb Eval
evalImpl = 
  CombComponents eLam eApp eProd eFst eSnd eUnit eAdd eValue

evalImpl': CombL Eval
evalImpl' = 
  CombLComponents eLam eProd eFst eSnd eUnit eAdd eValue 

prf: {a: _} -> {b: _}
 -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
 -> (t: {repr:_} -> (Comb repr) -> repr a b)
 -> (x: a)
 -> (eval $ t Main.evalImpl) x = (eval $ norm t Main.evalImpl') x
prf t x = ?prf_rhs
