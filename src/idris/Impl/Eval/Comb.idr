module Impl.Eval.Comb

import Sym.Comb.Comb
import Impl.Eval.Eval

import Data.Signal

public export
Comb Combinational where
  lam f = MkComb 
    $ \x => (runComb 
              $ (f . MkComb . const) x) ()
  
  app f x = 
    let f' = runComb f 
        x' = runComb x
    in MkComb (f' . x')
    
  prod x y = MkComb 
    $ bimap (runComb x) (runComb y) 
    . (\() => ((), ()))
  
  proj1 x = MkComb 
    $ (fst . runComb x)
  
  proj2 x = MkComb 
    $ (snd . runComb x)
    
  unit = MkComb $ const ()
