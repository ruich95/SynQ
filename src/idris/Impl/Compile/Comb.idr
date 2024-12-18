module Impl.Compile.Comb

import Sym.Comb
import Impl.Compile.Compile
import Language.Reflection
import Data.Signal

public export
Comb Combinational where
  lam f = 
    MkComb 
      $ lambda a $ \y => let MkComb e = f (MkComb $ pure (const y))
                         in e <*> (pure ())
  
  app (MkComb f) (MkComb e) = 
    MkComb $ do f' <- f
                e' <- e <*> (pure ())
                res <- pure $ f' e'
                pure $ const res
  
  prod (MkComb e1) (MkComb e2) = 
    MkComb $ do e1' <- e1
                e2' <- e2
                pure $ \u =>(e1' u, e2' u)
  
  proj1 (MkComb e) 
    = let e' = [| fst $ e <*> (pure ()) |]
      in MkComb [| const e' |]
      
  proj2 (MkComb e) 
    = MkComb $ do e' <- e <*> (pure ())
                  pure $ const $ snd e'
      
  unit = MkComb $ pure id
