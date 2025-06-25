module Impl.HDL.Comb

import Sym.Comb.Comb

import Data.Name
import Data.Signal

import Impl.HDL.Port
import Impl.HDL.Module
import Impl.HDL.NetList
import Impl.HDL.Flatten



import Control.Monad.State

genPort: (Sig a) -> State Nat (TPort a)
genPort isSig = ST $ \c => Id (S c, fromSig isSig (show c))

genPort': (Sig a) -> State Nat (TPort a)
genPort' isSig = ST $ \c => Id (fromSig' isSig c)

public export
Comb Combinational where
  lam f = MkComb
    $ do iP <- genPort' aIsSig
         comb <- genComb $ f (MkComb $ pure $ MkCNL (UP UN) iP [] [])
         True <- pure $ (fromTP comb.oPort) == (fromTP iP)
           | False =>  pure $ {iPort := iP} comb
         oP <- genPort' bIsSig
         pure $ {iPort := iP, oPort := oP,
                 assignedPorts $= \xs => xs ++ [fromTPA $ TPA oP comb.oPort]} comb
  
  -- lam f = MkComb
  --   $ do iP <- genPort' aIsSig
  --        comb <- genComb $ f (MkComb $ pure $ MkCNL (UP UN) iP [] [])
  --        oP   <- genPort' bIsSig
  --        pure $ {iPort := iP, oPort := oP,
  --                assignedPorts $= \xs => xs ++ [fromTPA $ TPA oP comb.oPort]} comb
  
  app f x  = MkComb 
    $ do x' <- genComb x
         f' <- genComb f
         -- pure $ f' . x'
         pure $ f' <<= x'
                
  prod x y = MkComb 
    $ do x' <- genComb x
         y' <- genComb y
         pure $ MkCNL (UP UN) (CP x'.oPort y'.oPort)
                  (x'.assignedPorts ++ y'.assignedPorts)
                  (x'.instModules ++ y'.instModules)
                
  proj1 x = MkComb 
    $ do x' <- genComb x
         pure $ let p = case x'.oPort of 
                          (CP p1 p2) => p1
                          -- (UP nm) => (UP nm)
                in {oPort := p} x'
                
  proj2 x = MkComb 
    $ do x' <- genComb x
         pure $ let p = case x'.oPort of 
                          (CP p1 p2) => p2
                          -- (UP nm) => (UP nm)
                in {oPort := p} x'
  
  unit = MkComb $ pure emptyCNL
