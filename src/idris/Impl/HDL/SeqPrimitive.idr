module Impl.HDL.SeqPrimitive

import Sym.Comb.Comb
import Sym.Seq.Seq
import Sym.Seq.SeqPrimitive

import Data.Name
import Data.BitVec
import Data.Signal
import Data.State

import Impl.HDL.Port
import Impl.HDL.LPort
import Impl.HDL.Module
import Impl.HDL.NetList
import Impl.HDL.Comb
import Impl.HDL.Seq

import Control.Monad.State

import Data.LState2

import Data.Linear
import Data.List
import Data.LC 

public export
Reg Combinational Sequential where
  set (MkComb x) = MkSeq $ 
    do (MkBang comb) <- fromST x
       pure $ let p = comb.oPort 
              in fromComb ({oPort := (UP UN)} comb)
                          (MkLP similar 
                                (MkBang $ UP UN) 
                                (MkBang p))
  get = MkSeq $ 
    do (MkBang p) <- LST2 
          -- $ \c => (MkBang (stToPort sIsState 
          --                           (show c) 
          --                           {prf = similar}) 
          --                  # S c)
          $ \c => let (c', p') = stToPort' sIsState c {prf = similar}
                  in (MkBang p' # c')
       pure $ fromComb ({oPort := p} emptyCNL) 
                       (MkLP similar (MkBang p) 
                                     (MkBang p))

public export                                   
reg: Reg Combinational Sequential
reg = MkReg get set
where
  get: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> Sequential s () a
  get = MkSeq $ 
    do (MkBang p) <- LST2 
          -- $ \c => (MkBang (stToPort sIsState 
          --                           (show c) 
          --                           {prf = similar}) 
          --                  # S c)
             $ \c => let (c', p') = stToPort' sIsState c {prf = similar}
                     in (MkBang p' # c')
       pure $ fromComb ({oPort := p} emptyCNL) 
                       (MkLP similar (MkBang p) 
                                     (MkBang p))
                                     
  set: {auto aIsSig: Sig a} -> {auto sIsState: St s}
    -> {auto similar: SameShape a s}
    -> Combinational () a -> Sequential s () ()
  set (MkComb x) = MkSeq $ 
    do (MkBang comb) <- fromST x
       pure $ let p = comb.oPort 
              in fromComb ({oPort := (UP UN)} comb) -- emptyCNL 
                          (MkLP similar 
                                (MkBang $ UP UN) 
                                (MkBang p))
  
