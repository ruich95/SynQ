module Impl.Compile.Compile

import Language.Reflection
import Data.LState
import Data.Linear

public export
record Combinational a b where
  constructor MkComb
  genComb: Elab (a -> b)

public export
free: (1 _: a) -> Elab (!* a)
free = believe_me (\x: a => the (Elab (!* a)) $ Prelude.pure (MkBang x))

public export
data Sequential: Type -> Type -> Type -> Type where
  MkSeq: Elab (a -> LState s b) -> Sequential s a b
  
public export
genSeq: Sequential s a b -> Elab (a -> LState s b)
genSeq (MkSeq x) = x
