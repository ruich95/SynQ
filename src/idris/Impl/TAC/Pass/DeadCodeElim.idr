module Impl.TAC.Pass.DeadCodeElim

import Impl.TAC.Common
import Impl.TAC.TAC

import Impl.TAC.Pass.Common
import Data.List
import Data.LC

isElement: (Eq a) => a -> List a -> Bool
isElement x [] = False
isElement x (y :: xs) = 
  if x == y then True 
  else isElement x xs

isDead: TACData 
  -> (List TACAtom1, TACData) -> Bool
isDead x ([], out) = not (x == out)
isDead x (y :: xs, out) = 
  let used = getUsed y
  in if isElement x used
     then False else isDead x (xs, out)
     
deadElimStep: (Zipper TACAtom1, TACData) -> (Zipper TACAtom1, TACData)
deadElimStep (z@(MkZipper prev Nothing rest), out) = (next z, out)
deadElimStep (z@(MkZipper prev (Just cur) rest), out) = 
  case cur of 
    (Op (_ ::= _)) => (next z, out)
    _ => if isDead (getDst cur) (prev, out)
         then (next $ drop z, out) 
         else (next z, out)

deadElim: (Zipper TACAtom1, TACData) -> (Zipper TACAtom1, TACData)
deadElim (z, out) = 
  if isEnd z then deadElimStep (z, out)
  else deadElim $ deadElimStep (z, out)

deadCodeElim': TAC1 -> TAC1
deadCodeElim' tac@(MkTAC1 input output ops) = 
  let ops'      = fromList $ reverse ops 
      (ops', _) = deadElim (ops', output)
      ops'      = reverse $ Common.toList ops'
  in {ops := ops'} tac

export
deadCodeElim: (1 _: LC a TAC1) -> LC a TAC1
deadCodeElim (l # v) = (l # deadCodeElim' v)
