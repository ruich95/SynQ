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

%hint
prodNotUnit: NotUnit (a, b)

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
  
lift1: {repr: _} -> {a: _} -> {b: _}
   -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> (fn: repr () a -> repr () b)
   -> (E repr () a -> E repr () b)
lift1 fn (F {notUnit = (NUnit prf)} f) = case prf Refl of _ impossible
lift1 fn (C x) = C $ (Val . fn . val) x

lift2: {repr: _} -> {a: _} -> {b: _}
   -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
   -> {auto cIsSig: Sig c}
   -> (fn: repr () a -> repr () b -> repr () c)
   -> (E repr () a -> E repr () b -> E repr () c)
lift2 fn (F {notUnit = (NUnit prf)} f) y 
  = case prf Refl of _ impossible
lift2 fn (C x) (F {notUnit = (NUnit prf)} f) 
  = case prf Refl of _ impossible
lift2 fn (C x) (C y) = C $ Val $ fn (val x) (val y)


lam: {repr: _} -> {a:_} -> {b:_} 
  -> {auto aIsSig: Sig a} -> {auto notUnit: NotUnit a} 
  -> {auto bIsSig: Sig b} 
  -> (E repr () a -> E repr () b) -> E repr a b
lam f = F {notUnit = notUnit} $ 
  \x => let y = f (C x) 
        in case y of
                (F {notUnit = (NUnit prf)} g) 
                    => case prf Refl of _ impossible
                (C z) => z


app: {repr: _}
  -> E repr a b -> E repr () a -> E repr () b
app (F f) (F {notUnit = (NUnit prf)} g) 
  = case prf Refl of _ impossible
app (F f) (C x) = C (f x)
app (C x) y = C x

-- implement Comb with CombL
impl: {repr: _} -> (cl: CombL repr) -> (Comb $ E repr)
impl cl =
  CombComponents 
    lam app (lift2 cl.prod) (lift1 cl.fst)
    (lift1 cl.snd) (C $ Val cl.unit) (lift2 cl.add)  (C . Val . cl.value)

abst: {repr: _} -> {a: _} -> {b: _}
   -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
   -> (lam: {auto notUnit: NotUnit a} 
   -> (repr () a -> repr () b) -> repr a b) -> (t: E repr a b) -> repr a b
abst lam (F {notUnit} f) 
  = lam $ val . f . Val
abst lam (C x) = val x

addPrf: {repr: _} -> {n:_} -> (cl: CombL repr) -> (c: Comb repr)
  -> (x: repr () $ BitVec n) -> (y: repr () $ BitVec n)
  -> ((lift2 c.add) (C $ Val x) (C $ Val y)) = ((impl cl).add (C $ Val x) (C $ Val y))
addPrf cl c x y = ?rhs'

norm: {a: _} -> {b: _}
 -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
 -> ({repr':_} -> Comb repr' -> repr' a b) 
 -> ({repr:_} ->  CombL repr -> repr a b)
norm f cl = abst cl.lam $ f (impl cl)

record Eval a b where
  constructor MkEval
  eval: a -> b

eValue: {n:_} -> BitVec n -> Eval () (BitVec n)
-- eValue x = MkEval (\y => x)

eAdd: {n:_} -> Eval () (BitVec n) -> Eval () (BitVec n) -> Eval () $ BitVec (S n)

eUnit : Eval () ()
-- eUnit = MkEval (\x => x)

eSnd : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
  -> Eval () (a, b) -> Eval () b
eSnd x = MkEval $ Prelude.const $ snd (eval x $ ())

eFst : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
  -> Eval () (a, b) -> Eval () a
eFst x = MkEval $ Prelude.const $ fst (eval x $ ())

eProd : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
  -> Eval () a -> Eval () b -> Eval () (a, b)
eProd x y = MkEval $ Prelude.const ((eval x $ ()), (eval y $ ()))

eLam : {auto aIsSig: Sig a} -> {auto notUnit: NotUnit a} -> {auto bIsSig: Sig b} 
  -> (Eval () a -> Eval () b) -> Eval a b
eLam f = MkEval $ \x => (eval $ f $ MkEval $ Prelude.const x) ()

eApp : {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} -> Eval a b -> Eval () a -> Eval () b
eApp f x = MkEval (Prelude.const $ (eval f) (eval x $ ()))

evalImpl: Comb Eval
evalImpl = 
  CombComponents eLam eApp eProd eFst eSnd eUnit eAdd eValue

evalImpl': CombL Eval
evalImpl' = 
  CombLComponents eLam eProd eFst eSnd eUnit eAdd eValue 

contract: {a: _} -> {b: _}
 -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
 -> (t: {repr:_} -> (Comb repr) -> repr a b)
 -> Type
contract t = (eval $ t Main.evalImpl) = (eval $ norm t Main.evalImpl')

adder: {n:_} -> {repr: _} -> (Comb repr) -> repr (BitVec n) (BitVec $ S n)
adder comp = comp.lam $ \x => comp.add x x

%hint
p: {n:_} -> NotUnit (BitVec n, BitVec n)

adder': {n:_} -> {repr: _} -> (Comb repr) -> repr (BitVec n) (BitVec $ S n)
adder' {n} comp = 
  comp.lam $ \y 
    => comp.app (comp.lam $ \x => comp.add {n=n} (comp.fst x) (comp.snd x)) 
                (comp.prod y y)

adder_eq: {n:_} -> contract (Main.adder' {n=n})
adder_eq = Refl

swap: {a: _} -> {b: _} 
   -> {auto aIsSig: Sig a} 
   -> {auto bIsSig: Sig b} 
   -> {comb: _} -> (Comb comb) -> comb (a, b) (b, a)
swap glue = glue.lam $ \x => glue.prod (glue.snd x) (glue.fst x)

swap_eq: {a:_} -> {b:_} -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
  -> contract {a = (a, b)} {b = (b, a)} Main.swap
swap_eq = Refl

f: {a:_} -> {b:_} -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
  -> {auto prf: contract {a = (a, b)} {b = (b, a)} Main.swap} 
  -> Nat
f = 0

g: {a:_} -> {b:_} -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b} 
  -> Nat
g = f {a} {b}

eSwap: {a: _} -> {b: _}
   -> {auto aIsSig: Sig a} 
   -> {auto bIsSig: Sig b}
   -> (a, b) -> (b, a)
eSwap = eval (swap evalImpl)

eSwapPrf: {a: _} -> {b: _} -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
   -> (x: a) -> (y: b) -> eSwap (eSwap (x, y)) = (x, y)
eSwapPrf x y = Refl

prf: {a: _} -> {b: _}
 -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
 -> (t: {repr:_} -> (Comb repr) -> repr a b)
 -> (eval $ t Main.evalImpl) = (eval $ norm t Main.evalImpl')
prf t = ?prf_rhs
-- prf t with (t $ impl Main.evalImpl')
--   prf t | (F f) = ?prf_rhs_rhs_0
--   prf t | (C y) = ?prf_rhs_rhs_1_rhs_0


