module Impl.HDL.Seq

import Sym.Comb.Comb
import Sym.Seq.Seq

import Data.Name

import Impl.HDL.Port
import Impl.HDL.LPort
import Impl.HDL.Module
import Impl.HDL.NetList
import Impl.HDL.Comb

import Control.Monad.State

import Data.LState2
import Data.Signal
import Data.State

import Data.Linear
import Data.List
import Data.LC 

public export
Seq Combinational Sequential where
  abst f = MkSeq 
    $ do --(MkBang iP) <- LST2 $ \c => MkBang (TPort.fromSig aIsSig (show c)) # S c
         (MkBang iP) <- LST2 $ \c => let (c', p) = TPort.fromSig' aIsSig c 
                                     in MkBang p # c'
         (MkBang comb') <- pure $ MkBang $ the (CombNL () a) $ {oPort := iP} emptyCNL
         seq' <- (genSeq' $ f (MkComb $ pure comb'))
         pure $ let (lp # comb) = unpackSeqNL seq'
                in fromComb ({iPort := iP} comb) lp
  
  pure (MkComb (ST f)) = MkSeq 
    $ LST2 $ \c => 
           let Id (c', comb) = f c
               (ty ** prf) = getType sIsState
               -- lport = fromSt sIsState (show c') {prf}
               (c'', lport) = fromSt' sIsState c' {prf}
           in fromComb comb lport # (S c'')
       
  (=<<) (MkSeq g) (MkSeq f) = MkSeq 
    $ do (lp1 # comb1) <- (pure unpackSeqNL) <*> f
         (lp2 # comb2) <- (pure unpackSeqNL) <*> g
         pure $ let comb = comb2 . comb1 
                    (lp # pa) = lp2 `seqLP` lp1
                in fromComb ({assignedPorts $= \xs => snoc xs pa} comb) 
                            lp
  
  (<<<) (MkSeq g) (MkSeq f) = MkSeq 
    $ do (lp1 # comb1) <- (pure unpackSeqNL) <*> f
         (lp2 # comb2) <- (pure unpackSeqNL) <*> g
         pure $ let comb = comb2 . comb1 
                    lp = lp1 `parLP` lp2
                in fromComb comb lp
