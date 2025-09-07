module Impl.TAC.Pass.Proj2Idx

import Impl.TAC.Common
import Impl.TAC.TAC

import Impl.TAC.Pass.Common
import Data.List
import Data.LC

data Dir = P1 | P2

trace: TACAtom1 -> (TACData, List TACAtom1) 
    -> (TACData, List Dir)
trace (Gl (PROJ1 src dst)) (input, ops) = 
  if src == input then (input, [P1])
  else let def = findDef src ops 
       in case def of
            Nothing => (src, [P1])
            (Just def) => 
              let (root, tr) = trace def (input, ops) 
              in (root, snoc tr P1)
trace (Gl (PROJ2 src dst)) (input, ops) = 
  if src == input then (input, [P2])
  else let def = findDef src ops 
       in case def of
            Nothing => (src, [P2])
            (Just def) => 
              let (root, tr) = trace def (input, ops) 
              in (root, snoc tr P2)
trace atom y = (getDst atom, [])

numLeaf: TACTy -> Nat
numLeaf (ProdTy a b) = numLeaf a + numLeaf b
numLeaf _ = 1

getIdx: Nat -> TACTy -> List Dir -> Nat
getIdx k ty1 [] = k
getIdx k (ProdTy a b) (P1 :: xs) = getIdx k a xs
getIdx k (ProdTy a b) (P2 :: xs) = getIdx (k + numLeaf a) b xs
getIdx k _ (x :: xs) = k

ofSimpleTy:TACData -> Bool
ofSimpleTy (Var nm $ ProdTy a b) = False
ofSimpleTy _ = True

proj2Idx': (TACData, Zipper TACAtom1) 
  -> List TACAtom2
proj2Idx' (input, z@(MkZipper prev cur rest)) = 
  case cur of 
    Nothing => 
      case rest of 
        [] => []
        _  => proj2Idx' (input, next z)
    (Just (Gl (PROD x y dst))) => 
      case rest of 
        [] => []
        _  => proj2Idx' (input, next $ drop z)
    (Just (Op x)) => 
      case rest of 
        [] => [Op2 x]
        _  => (Op2 x) :: proj2Idx' (input, next z)
    (Just proj) => 
      let (root, tr) = trace proj (input, prev) 
          dst = getDst proj
      in if not (ofSimpleTy dst) 
         then case rest of
                [] => []
                _  => proj2Idx' (input, next z)
         else case root of
                (Var nm ty1) => 
                  let idx = getIdx 0 ty1 tr 
                  in case rest of 
                       [] => [Gl2 $ IDX root idx $ getDst proj] 
                       _ =>  (Gl2 $ IDX root idx $ getDst proj) :: proj2Idx' (input, next z)
                _ => believe_me "impossible"
           
           
export
proj2Idx: (1 _: LC st TAC1) -> LC st TAC2
proj2Idx (l # (MkTAC1 input output ops)) = 
  let ops' = fromList ops 
      ops'' = proj2Idx' (input, ops')
  in (l # MkTAC2 input output ops'')

test: TACTy
test = ProdTy (ProdTy (BvTy 1) (ProdTy (BvTy 4) (BvTy 5))) (ProdTy (BvTy 2) (BvTy 3))

