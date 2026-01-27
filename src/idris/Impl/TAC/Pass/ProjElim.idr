module Impl.TAC.Pass.ProjElim

import Impl.TAC.Common
import Impl.TAC.TAC

import Impl.TAC.Pass.Common
import Data.List
import Data.LC

data TACData' = P1 TACData | P2 TACData

findVal: TACData' -> List TACAtom1 -> Maybe TACData
findVal x [] = Nothing
findVal x ((Gl $ PROD y z dst) :: xs) = 
  case x of
       (P1 w) => 
         if w == dst then Just y 
                     else findVal x xs
       (P2 w) => 
         if w == dst then Just z 
                     else findVal x xs
findVal x (_ :: xs) = findVal x xs

projElimStep: (Zipper TACAtom1, TACData) 
            -> (Zipper TACAtom1, TACData)
projElimStep (z@(MkZipper prev cur rest), out) = 
  case cur of
    Nothing  => (next z, out)
    (Just x) => 
      case x of
        (Gl $ PROJ1 y dst) => 
          case findVal (P1 y) prev of
            Nothing  => (next z, out)
            (Just w) => 
              let rest' = substBy1 dst w rest
                  z'    = next $ MkZipper prev Nothing rest'
                  out'  = if out == dst then w else out
              in (z', out')
        (Gl $ PROJ2 y dst) => 
          case findVal (P2 y) prev of
            Nothing  => (next z, out)
            (Just w) => 
              let rest' = substBy1 dst w rest
                  z'    = next $ MkZipper prev Nothing rest'
                  out'  = if out == dst then w else out
              in (z', out')
        _ => (next z, out)

projElim': (Zipper TACAtom1, TACData) 
        -> (Zipper TACAtom1, TACData)
projElim' (z, y) = 
  if isEnd z then projElimStep (z, y) -- ?projElim'_rhs_0
  else (projElim' . projElimStep) (z, y)
  
  
export
projElim: (1 _: LC a TAC1) -> LC a TAC1
projElim (st # tac@(MkTAC1 input output ops)) = 
  let (ops', out') = projElim' (fromList ops, output) 
      ops' = Common.toList ops'
  in (st # {output := out', ops := ops'} tac)
