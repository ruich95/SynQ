module Impl.TAC.Pass.ExpSharing

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Common
import Impl.TAC.Pass.Common

import Data.List
import Data.LC

sameDef: FlatOp -> FlatOp -> Bool
sameDef (st ::= src)             (st' ::= src')              = src == src' && (st == st')
sameDef (_ <<= st)               (_ <<= st')                 = st' == st
sameDef (ADD src1 src2 _)        (ADD src1' src2' _)         = (src1 == src1') && (src2 == src2')
sameDef (CONCAT src1 src2 _)     (CONCAT src1' src2' _)      = (src1 == src1') && (src2 == src2')
sameDef (AND src1 src2 _)        (AND src1' src2' _)         = (src1 == src1') && (src2 == src2')
sameDef (OR src1 src2 _)         (OR src1' src2' _)          = (src1 == src1') && (src2 == src2')
sameDef (XOR src1 src2 _)        (XOR src1' src2' _)         = (src1 == src1') && (src2 == src2')
sameDef (EQ src1 src2 _)         (EQ src1' src2' _)          = (src1 == src1') && (src2 == src2')
sameDef (LTU src1 src2 _)        (LTU src1' src2' _)         = (src1 == src1') && (src2 == src2')
sameDef (LT src1 src2 _)         (LT src1' src2' _)          = (src1 == src1') && (src2 == src2')
sameDef (MUX21 src1 src2 src3 _) (MUX21 src1' src2' src3' _) = (src1 == src1') && (src2 == src2') && (src3 == src3')
sameDef (SLL k src _)            (SLL k' src' _)             = (src == src') && (k == k')
sameDef (SRL k src _)            (SRL k' src' _)             = (src == src') && (k == k')
sameDef (SRA k src _)            (SRA k' src' _)             = (src == src') && (k == k')
sameDef (NOT src _)              (NOT src' _)                = src == src'
sameDef (SLICE k j src _)        (SLICE k' j' src' _)        = (src == src') && (k == k') && (j == j')
sameDef (MULT src1 src2 _)       (MULT src1' src2' _)        = (src1 == src1') && (src2 == src2')
sameDef _ _ = False

hasDefined: FlatOp -> List (FlatOp) -> Maybe FTACData
hasDefined x [] = Nothing
hasDefined x (y :: xs) = 
  case sameDef x y of
       False => hasDefined x xs
       True =>  Just $ getDst y

shareExpStep: (Zipper FlatOp, List FTACData) -> (Zipper FlatOp, List FTACData)
shareExpStep (z@(MkZipper prev Nothing rest), outputs) = (next z, outputs)
shareExpStep (z@(MkZipper prev (Just x) rest), outputs) = 
  case hasDefined x prev of
       Nothing => (next z, outputs)
       (Just y) => 
         let rest' = map (substOp (getDst x) y) rest
             outputs' = map (subst (getDst x) y) outputs
         in (next $ MkZipper prev Nothing rest', outputs')

shareExp': (Zipper FlatOp, List FTACData) -> (Zipper FlatOp, List FTACData) 
shareExp' z = if isEnd (fst z) then z else shareExp' (shareExpStep z)

export
shareExp: FTAC -> FTAC
shareExp tac@(MkFTAC input output state ops) = 
  let ops' = fromList ops
      (ops', output') = shareExp' (ops', output)
      ops' = Common.toList ops'
  in {ops := ops', output := output'} tac
