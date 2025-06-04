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

-- public export
-- runMealy: (Sequential s a b) 
--   -> List a -> LState s (List b)
-- runMealy f [] = LST $ \1 st => st # []
-- runMealy f (x :: xs) = 
--   LST $ \1 st'' => 
--     let (st' # y)  = runState (runSeq f $ x) st''
--         (st  # ys) = runState (runMealy f xs) st'
--     in (st # y :: ys)

public export
runMealy: (Sequential s a b) 
  -> s -> List a -> (s, List b)
runMealy sys st [] = (st, [])
runMealy (MkSeq f) st (x :: xs) = 
  let LST sf    = f x 
      (st' # y) = sf st
      final_st  = fst (runMealy (MkSeq f) st' xs)
      ys        = snd (runMealy (MkSeq f) st' xs)
  in (final_st , y::ys)

export
runMealyLemma: (sys: Eval.Sequential s a b) 
  -> (st: s) -> (xs1: List a) -> (xs2: List a)
  -> (st':s ** 
       (snd $ runMealy sys st (xs1 ++ xs2)) 
          = (snd $ runMealy sys st xs1) 
            ++ (snd $ runMealy sys st' xs2))
runMealyLemma sys st [] xs2 = (st ** Refl)
runMealyLemma (MkSeq f) st (x :: xs) xs2 with (f x)
  runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) with (sf st)
    runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) | (st0 # y) 
      with (snd $ runMealy (MkSeq f) st0 xs) proof p
      runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) | (st0 # y) | ys 
        with (runMealyLemma (MkSeq f) st0 xs xs2)
        runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) | (st0 # y) | ys | (st' ** prf) 
          = (st' ** rewrite sym p in rewrite prf in Refl)
