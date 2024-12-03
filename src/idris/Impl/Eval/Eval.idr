module Impl.Eval.Eval

import Data.LState

public export
record Combinational a b where
  constructor MkComb
  runComb: a -> b

public export
data Sequential: Type -> Type -> Type -> Type where
  MkSeq: (1 _: a -> LState s b) -> Sequential s a b
  
public export
runSeq: (1 _: Sequential s a b) -> a -> LState s b
runSeq (MkSeq f) = f

public export
runMealy: (Sequential s a b) 
  -> List a -> LState s (List b)
runMealy f [] = LST $ \1 st => st # []
runMealy f (x :: xs) = 
  LST $ \1 st'' => 
    let (st' # y)  = runState (runSeq f $ x) st''
        (st  # ys) = runState (runMealy f xs) st'
    in (st # y :: ys)
     

  
