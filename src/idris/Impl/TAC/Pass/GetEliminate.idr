module Impl.TAC.Pass.GetEliminate

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common


SetCtx: Type
SetCtx = List (FlatSt, FTACData)

hasBeenSet: FlatSt -> SetCtx 
  -> Maybe FTACData
hasBeenSet x [] = Nothing
hasBeenSet x ((y, z) :: xs) = 
  if x == y then Just z 
  else hasBeenSet x xs 

findEarly: FlatSt -> List FlatOp 
  -> Maybe FTACData
findEarly x [] = Nothing
findEarly x (y :: xs) = 
  case isGet y of
       Nothing => findEarly x xs
       (Just (dst, st)) => 
         if x == st 
         then Just dst 
         else findEarly x xs

getElimStep: SetCtx -> (Zipper FlatOp, List FTACData)
  -> (SetCtx, Zipper FlatOp, List FTACData)
getElimStep ctx (z@(MkZipper prev (Just op) rest), outs) = 
  case isSet op of
    (Just y) => (y :: ctx, next z, outs)
    Nothing => 
      case isGet op of
        (Just (dst, st)) => 
          case hasBeenSet st ctx of
            (Just x) => 
              let rest' = map (substOp dst x) rest
                  outs' = map (subst dst x) outs 
              in (ctx, next $ drop $ {rest := rest'} z, outs')
            Nothing => 
              case findEarly st prev of
                (Just x) => 
                  let rest' = map (substOp dst x) rest
                      outs' = map (subst dst x) outs 
                  in (ctx, next $ drop $ {rest := rest'} z, outs')
                Nothing => (ctx, next z, outs)
        Nothing => (ctx, next z, outs)
getElimStep ctx (z, outs) = (ctx, next z, outs)


getElim': SetCtx -> (Zipper FlatOp, List FTACData)
  -> (SetCtx, Zipper FlatOp, List FTACData)
getElim' ctx x@(z, o) = 
  if isEnd z then getElimStep ctx x
  else let (ctx', x') = getElimStep ctx x
       in getElim' ctx' x'

export
elimGet: FTAC -> FTAC
elimGet tac@(MkFTAC input output state ops) = 
  let ops' = fromList ops
      (_, ops', o') = 
        getElim' [] (ops', output)
      ops' = Common.toList ops'
  in {output := o', ops := ops'} tac
