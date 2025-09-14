module Impl.TAC.Pass.InlineGet

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common

inlineStep: Zipper FlatOp -> Zipper FlatOp
inlineStep z@(MkZipper prev (Just x) rest) = 
  case isGet x of 
    Just (dst, MkSt src) => 
      let rest' = map (substOp dst src) rest
      in next $ drop $ {rest := rest'} z
    _ => next z
inlineStep z@(MkZipper _ _ _) = next z

inline: Zipper FlatOp -> Zipper FlatOp
inline z1 = 
  if isEnd z1 
  then inlineStep z1
  else inline $ inlineStep z1

export
substSt: FTAC -> FTAC
substSt tac = 
  let ops' = Common.toList 
           $ inline 
           $ fromList tac.ops 
  in {ops := ops'} tac
