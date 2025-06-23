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

public export
Seq Combinational Sequential where
  abst f = 
    let MkBang f = free {aIsSig=aIsSig} f 
    in MkSeq $ lambda _ $ \x 
         => do f <- f 
               pure $ f x
               --x' <- pure $ MkComb $ pure $ \_ => x
               --MkSeq y <- pure $ f x'
               --y <*> pure ()
  
  (=<<) (MkSeq g) (MkSeq f) = 
    MkSeq $ do f' <- f
               g' <- g
               pure (g' =<< f')
  
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
