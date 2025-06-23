module Impl.Compile.Compile

import Language.Reflection
import Data.LState
import Data.Linear

import Data.BitVec
import Data.Signal

public export
record Combinational a b where
  constructor MkComb
  genComb: Elab (a -> b)

public export
data Sequential: Type -> Type -> Type -> Type where
  MkSeq: Elab (a -> LState s b) -> Sequential s a b
  
public export
genSeq: Sequential s a b -> Elab (a -> LState s b)
genSeq (MkSeq x) = x

-- public export
-- Consumable (Sequential s a b) where
--   consume (MkSeq x) = ()
  
-- public export
-- interface Const a where
--   constructor MkConst
--   constant: a

-- -- [defaultBV] Const (Combinational () $ BitVec n) where
-- --   constant = MkComb $ pure $ \_ => BV 0

-- -- [defaultUnit] Const (Combinational () ()) where
-- --   constant = MkComb $ pure $ \_ => ()
  
-- -- [defaultProd] (Const (Combinational () a), Const (Combinational () b)) 
-- --   => Const (Combinational () (a, b)) where
-- --   constant = let t1: Elab (() -> a) = genComb constant 
-- --                  t2: Elab (() -> b) = genComb constant 
-- --              in MkComb $ do t1 <- t1 
-- --                             t2 <- t2
-- --                             pure $ \_ => (t1 (), t2 ())

-- %hint 
public export
sigConstant: {aIsSig: Sig a} -> (Combinational () a)
sigConstant {aIsSig = U} = MkComb $ pure $ \_ => ()
sigConstant {aIsSig = (P x y)} = 
  let c1 = sigConstant {aIsSig=x}
      c1 = genComb c1
      c2 = sigConstant {aIsSig=y}
      c2 = genComb c2
  in MkComb $ do c1 <- c1
                 c2 <- c2
                 pure $ \_ => (c1 (), c2 ())
sigConstant {aIsSig = BV {n=n}} = MkComb $ pure $ \_ => BV {n=n} 0

-- public export
-- (Const a, Consumable b) => Consumable (a -> b) where
--   consume f = consume $ f constant

public export
free: {aIsSig: Sig a} -> (1 _: Combinational () a -> Sequential s () b)
  -> !* (Elab $ Combinational () a -> Sequential s () b)
free f = let c = sigConstant {aIsSig=aIsSig}
             MkSeq f' = f c
         in MkBang $ do f <- quote f 
                        check f
--                      lambda _ $ \x => let g = genSeq $ f (MkComb $ pure $ \_: () => x) 
--                                       in g <*> pure ()
-- free {aIsSig = U} f = 
--   let MkSeq f' = f (MkComb $ pure $ \_ => ()) 
--   in MkBang f'
-- free {aIsSig = (P x y)} f = 
--   let c = sigConstant {aIsSig= (P x y)}
--       MkSeq f' = f c
--   in MkBang $ lambda _ $ \x => f' <*> pure ()
-- free {aIsSig = BV {n=n}} f = 
--   let MkSeq f' = f (MkComb $ pure $ \_ => (BV {n=n} 0)) 
--   in MkBang $ lambda _ $ \x => f' <*> pure ()
