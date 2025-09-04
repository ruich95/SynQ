module Impl.TAC.Seq

import Sym.Comb.Comb
import Sym.Seq.Seq

import Control.Monad.State

import Data.LState
import Data.Signal
import Data.State

import Data.Linear
import Data.List
import Data.LC 

import Impl.TAC.TAC

import Impl.TAC.Types
import Impl.TAC.Comb

splitSt: (1 _: TACSt) -> LC (LPair TACSt TACSt) (List TACAtom1, Name)
splitSt (MkSt name ty@(ProdTy a b)) = 
  let nms: (Name, Name) = 
        case name of
          Anon     => (Anon, Anon)
          (NM str) => (NM "\{str}_0", NM "\{str}_1")
      (nm1, nm2) = nms
      ops = 
        [Gl $ PROJ1 (Var name ty) (Var nm1 a),
         Gl $ PROJ2 (Var name ty) (Var nm2 b)]
      st1 = (MkSt nm1 a)
      st2 = (MkSt nm2 b)
  in (st1 # st2) # (ops, name)
splitSt (MkSt _ _ ) with (the Void $ believe_me ())
  splitSt (MkSt _ _ ) | _ impossible

mergeSt: Name -> (1 _: LPair TACSt TACSt) -> LC TACSt (List TACAtom1)
mergeSt nm ((MkSt nm1 a) # (MkSt nm2 b)) = 
  let ty = ProdTy a b
      ops = [Gl $ PROD (Var nm1 a) (Var nm2 b) (Var nm ty)]
  in MkSt nm ty # ops

public export
Seq TACComb TACSeq where
  abst f = 
    MkTACS $ LST $ \((MkBang c) # st) => 
      let (c', varIn) = 
            runState c $ genVar $ fromSig aIsSig
          input = MkTACC $ ST 
            $ \d => Id $ (d, MkTAC1 U varIn [])
          (MkTACS $ LST f) = f input
          (st' # f') = f (MkBang c' # st)
      in (st' # {input := varIn} f')
  
  pure (MkTACC f) = 
    MkTACS $ LST $ \(MkBang c # st) => 
      let (c', f) = runState c f 
      in (MkBang c' # st) # f
       
  (=<<) (MkTACS g) (MkTACS f) = 
    MkTACS $ 
      do (MkTAC1 inF outF opsF) <- f
         g'@(MkTAC1 inG _ _)    <- g
         let (MkTAC1 _ outG' opsG') 
                = substInput1 g' outF
         pure $ MkTAC1 inF outG' 
                       (opsF ++ opsG')
  
  (<<<) (MkTACS g) (MkTACS f) = 
    MkTACS $ LST $ \(c # st) => 
      let (st1 # st2) # (splitOps, name) = splitSt st 
          (c1 # st1') # (MkTAC1 inF outF opsF) = 
            LState.runState f (c # st1)
          (c2 # st2') # g'@(MkTAC1 inG _ _) = 
            LState.runState g (c1 # st2)
          (st' # mergeOps) = 
            mergeSt name (st1' # st2')
          (MkTAC1 _ outG' opsG') = 
            substInput1 g' outF
      in (c2 # st') 
       # MkTAC1 inF outG' 
                (splitOps 
                  ++ opsF 
                  ++ opsG' 
                  ++ mergeOps)
                
  swap (MkTACS f) = 
    MkTACS $ LST $ \(c # st) => 
      let (st1 # st2) # (splitOps1, name) = splitSt st 
          name' = case name of 
                    Anon => Anon
                    NM str => NM "\{str}'"
          st' # mergeOps1 = mergeSt name' (st2 # st1)
          (c' # st'') # f@(MkTAC1 inF outF opsF) = 
            LState.runState f (c # st')
          (st2 # st1) # (splitOps2, _) = splitSt st''
          st''' # mergeOps2 = mergeSt name (st1 # st2)
      in (c' # st''') 
       # MkTAC1 inF outF 
                (splitOps1 
                  ++ mergeOps1 
                  ++ opsF 
                  ++ splitOps2 
                  ++ mergeOps2)
