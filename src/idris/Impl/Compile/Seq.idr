module Impl.Compile.Seq

import Impl.Compile.Compile
import Impl.Compile.Comb

import Language.Reflection

import Sym.Seq

import Data.LState
import Data.LC
import Data.Linear

public export
Seq Combinational Sequential where
  abst f = ?rhs
  
  (=<<) (MkSeq g) (MkSeq f) = 
    MkSeq $ do f' <- f
               g' <- g
               pure (g' =<< f')
  
  pure (MkComb f) = 
    MkSeq $ do f' <- f
               pure $ fromMealy 
                    $ \1 (st # x) => (st # f' x)
  
  (<<<) (MkSeq g) (MkSeq f) = 
    MkSeq $ do f' <- f
               g' <- g
               pure (g' <<< f')
