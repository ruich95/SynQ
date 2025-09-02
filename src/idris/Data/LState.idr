module Data.LState

import Data.Linear
import public Data.LC

import System.File

public export infixr 9 <<<

public export
data LState: Type -> Type -> Type where
  LST: (1 sf: (1 _: s) -> LC s a) -> LState s a

{- sf shall be bind with multicity 1

data LState: Type -> Type -> Type where
  LST: (sf: (1 _: s) -> LC s a) -> LState s a
      
test: (1 _: LState s a) -> s -> a
test (LST sf) st = let (st # x) = sf st in x -}

public export
const: (1 x: a) -> () -> a
const x _ = x

public export
runState: (1 _: LState s a) -> (1 st: s) -> LC s a
runState (LST sf) st = sf st

public export
toMealy: (1 _: a -> LState s b) -> (1 _: LC s a) -> LC s b
toMealy f (st # x) = runState (f x) st

public export
fromMealy: (1 _: (1 _: LC s a) -> LC s b) -> a -> LState s b
fromMealy f x = LST $ \st => f (st # x)

public export
eval: (a, a -> b) -> b
eval (x, f) = f x

public export
pure: a -> LState s a
pure x = LST (\1 y => y # x)

public export
(=<<): (1 g: b -> LState s c) -> (1 f: a -> LState s b) 
    -> a -> LState s c
(=<<) g f x = LST $ \s => 
  let (s' # y) = runState (f x) s 
      (s'' # z) = runState (g y) s' 
  in (s'' # z) -- fromMealy $ (toMealy g) . (toMealy f)

public export
(>>=): (1 x: LState s a) -> (1 f: a -> LState s b) 
    -> LState s b
(>>=) x f = f =<< (const x) $ ()

public export
map: (f: a -> b) -> (1 sf: LState s a) -> LState s b
map f sf = (pure . f) =<< (const sf) $ ()

public export
(<*>): (1 f: LState s (a -> b)) 
    -> (1 x: LState s a) -> LState s b
(<*>) f x = (pure . eval) 
        =<< (\y => f >>= (pure . (MkPair y))) 
        =<< (const x) 
          $ ()

public export
(<<<): (1 g: b -> LState s2 c) -> (1 f: a -> LState s1 b)
    -> a -> LState (LPair s1 s2) c
(<<<) g f x = 
  LST $ \(st1 # st2) =>
    let (st1' # y) = runState (f x) st1
        (st2' # z) = runState (g y) st2
    in (st1' # st2') # z

bypassFst: (1 f: a -> LState s1 b) -> (c, a)
        -> LState s1 (c, b)
bypassFst f = \x => (pure . (\z => (fst x, z))) 
                =<< (const $ f =<< (pure . snd) $ x)
                  $ ()

bypassSnd: (1 f: a -> LState s1 b) -> (a, c)
        -> LState s1 (b, c)
bypassSnd f = \x => (pure . (\z => (z, snd x))) 
                =<< (const $ f =<< (pure . fst) $ x) 
                  $ ()

(<|>): (1 f: a -> LState s1 b) -> (1 g: c -> LState s2 d) 
    -> (a, c) -> LState (LPair s1 s2) (b, d)
(<|>) f g = (bypassFst g) <<< (bypassSnd f)


react: (Show a, Show b, Show s) 
  => (parse: IO a) 
  -> (a -> LState s b) -> (st: s)
  -> IO s
react parse f st = 
  do putStrLn "{\"current_state\" : \"\{show st}\"}"
     fflush stdout
     inData <- parse 
     (st' # out) <- pure (runState (f inData) st)
     putStrLn "{\"output\" : \"\{show out}\"}"
     fflush stdout
     pure st'

reactIO: (Show a, Show b) 
  => (parse: IO a) 
  -> (a -> LState s b) -> (st: s)
  -> IO s
reactIO parse f st = 
  do inData <- parse 
     (st' # out) <- pure (runState (f inData) st)
     putStrLn "{\"output\" : \"\{show out}\"}"
     fflush stdout
     pure st'
               
export
reactMealy: (Show a, Show b, Show s) 
  => (parse: IO a) 
  -> (a -> LState s b) -> (st: s)
  -> IO ()
reactMealy parse f st = 
  do st' <- react parse f st
     reactMealy parse f st'

export
reactMealyIO: (Show a, Show b) 
  => (parse: IO a) 
  -> (a -> LState s b) -> (st: s)
  -> IO ()
reactMealyIO parse f st = 
  do st' <- reactIO parse f st
     reactMealyIO parse f st'

{-To be used in types/proofs (w/ multiplicity 0) only-}

public export
getState: LState s a -> s -> s
getState (LST sf) s with (sf s)
  getState (LST sf) s | (l # v) = l

public export
getValue: LState s a -> s -> a
getValue (LST sf) s with (sf s)
  getValue (LST sf) s | (l # v) = v
