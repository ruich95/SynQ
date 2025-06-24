module Impl.Compile.Seq

import Impl.Compile.Compile
import Impl.Compile.Comb

import Language.Reflection

import Sym.Seq
import Sym.Comb

import Data.LState
import Data.LC
import Data.Linear
import Data.Signal
import Data.State

%ambiguity_depth 5

public export
Seq Combinational Sequential where
  abst f = 
    let MkSeq f_ = f $ sigConstant {aIsSig=aIsSig}
    in MkSeq $ do f <- quote f
                  f <- check f
                  lambda a $ \x => 
                         let (MkSeq y): Sequential s () b 
                               = f $ MkComb $ pure $ \_:() => x
                         in y <*> pure ()
    
    
    -- MkSeq $ lambda _ $ \x 
       --   => do -- f <- f 
       --         x' <- pure $ MkComb $ pure $ \_ => x
       --         MkSeq y <- f <*> pure x'
       --         y <*> pure ()
       --         --pure $ f x
       --         --x' <- pure $ MkComb $ pure $ \_ => x
       --         --MkSeq y <- pure $ f x'
       --         --y <*> pure ()
  
  (=<<) (MkSeq g) (MkSeq f) = 
    MkSeq $ do f' <- f
               g' <- g
               lambda _ $ \x => 
                 let LST sf = f' x 
                 in pure $ LST $ \st => 
                      let (st' # y) = sf st 
                          LST sg    = g' y
                      in sg st'
               -- pure (g' =<< f')
  
  pure (MkComb f) = 
    MkSeq $ do f' <- f
               lambda _ $ \x => 
                 pure $ LST $ \st => st # f' x
               -- pure $ fromMealy 
               --     $ \1 (st # x) => (st # f' x)
  
  (<<<) (MkSeq g) (MkSeq f) = 
    MkSeq $ do f' <- f
               g' <- g
               pure (g' <<< f')
