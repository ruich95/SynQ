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
runSeq': (Sequential s a b) -> a -> (1 _: s) -> LC s b
runSeq' (MkSeq f) x = let LST f' = f x in f'

public export
runMealyR: (Sequential s a b) 
  -> s -> List a -> (s, List b)
runMealyR sys st [] = (st, [])
runMealyR (MkSeq f) st (x :: xs) = 
  let LST sf    = f x 
      (st' # y) = sf st
      final_st  = fst (runMealyR (MkSeq f) st' xs)
      ys        = snd (runMealyR (MkSeq f) st' xs)
  in (final_st , y::ys)

public export
runMealy': (Sequential s a b) 
  -> (s, List b) -> List a -> (s, List b)
runMealy' sys (st, prev) [] = (st, prev)
runMealy' sys@(MkSeq f) (st, prev) (x :: xs) = 
  let LST sf    = f x 
      (st' # y) = sf st
  in runMealy' sys (st', prev++[y]) xs

-- foldl-style runMealy
public export
runMealy: (Sequential s a b) 
  -> s -> List a -> (s, List b)
runMealy sys st xs = runMealy' sys (st, []) xs

public export
runMealyIO: (Sequential s a b) 
  -> s -> List a -> List b
runMealyIO sys st [] = []
runMealyIO (MkSeq f) st (x :: xs) = 
  let LST sf    = f x 
      (st' # y) = sf st
      ys        = (runMealyIO (MkSeq f) st' xs)
  in y :: ys

export
runReact: (Show a, Show b, Show s) 
  => (input: IO a) 
  -> (sys: Sequential s a b) -> (st: s) 
  -> IO()
runReact input (MkSeq f) st = reactMealy input f st

export
runReactIO: (Show a, Show b) 
  => (input: IO a) 
  -> (sys: Sequential s a b) -> (st: s) 
  -> IO()
runReactIO input (MkSeq f) st = reactMealyIO input f st

-- public export
-- runMealyLemma: (sys: Eval.Sequential s a b) 
--   -> (st: s) -> (xs1: List a) -> (xs2: List a)
--   -> (st':s ** 
--        (snd $ runMealy sys st (xs1 ++ xs2)) 
--           = (snd $ runMealy sys st xs1) 
--             ++ (snd $ runMealy sys st' xs2))
-- runMealyLemma sys st [] xs2 = (st ** Refl)
-- runMealyLemma (MkSeq f) st (x :: xs) xs2 with (f x)
--   runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) with (sf st)
--     runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) | (st0 # y) 
--       with (snd $ runMealy (MkSeq f) st0 xs) proof p
--       runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) | (st0 # y) | ys 
--         with (runMealyLemma (MkSeq f) st0 xs xs2)
--         runMealyLemma (MkSeq f) st (x :: xs) xs2 | (LST sf) | (st0 # y) | ys | (st' ** prf) 
--           = (st' ** rewrite sym p in rewrite prf in Refl)
