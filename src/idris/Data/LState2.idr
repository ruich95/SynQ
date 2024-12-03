module Data.LState2

import Data.LC
import Data.Linear

import Control.Monad.State

public export
data LState2: Type -> Type -> Type where
  LST2: (1 _: s -> LC a s) -> LState2 s a
 
public export 
fromST: State s a -> LState2 s (!* a)
fromST (ST runStateT') 
  = LST2 $ \st => let Id (st', x) = runStateT' st
                  in MkBang x # st

public export
pure: (a) -@ LState2 s a
pure f = LST2 (\x => f # x)

public export
(>>=): LState2 s a -@ ( a -@ LState2 s b)
    -@ LState2 s b
(>>=) (LST2 x) f = 
  LST2 $ \st => 
    let (x' # st') = x st
        (LST2 f')  = f x'
        (f'' # st'') = f' st'
    in (f'' # st'')
    
public export
map: (a -@ b) -> LState2 s a -@ LState2 s b
map f (LST2 x) = 
  LST2 $ \st 
    => let (x' # st') = x st
       in f x' # st'

public export
(<*>): LState2 s (a -@ b) -@ LState2 s a 
    -@ LState2 s b
(<*>) (LST2 f) (LST2 x) = 
  LST2 $ \st 
    => let (f' # st') = f st 
           (x' # st'') = x st'
       in f' x' # st''
