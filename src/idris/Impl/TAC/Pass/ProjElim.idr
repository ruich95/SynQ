module Impl.TAC.Pass.ProjElim

import Impl.TAC.Types
import Impl.TAC.TAC
import Data.List
import Data.LC

getGls: List TACAtom1 -> List TACGl1
getGls [] = []
getGls ((Gl x) :: xs) = x :: getGls xs
getGls ((Op x) :: xs) = getGls xs

data TACData' = P1 TACData | P2 TACData

getProjDstSrc: List TACGl1 -> List (TACData, TACData')
getProjDstSrc [] = []
getProjDstSrc ((PROD  x y dst) :: xs) = 
  getProjDstSrc xs
getProjDstSrc ((PROJ1 x dst)   :: xs) = 
  (dst, P1 x) :: getProjDstSrc xs
getProjDstSrc ((PROJ2 x dst)   :: xs) = 
  (dst, P2 x) :: getProjDstSrc xs

getSrcVal: TACData' -> List TACGl1 -> Maybe TACData
getSrcVal x [] = Nothing
getSrcVal (P1 x) (p@(PROD y z dst) :: xs) = 
  if x == dst then Just y else getSrcVal (P1 x) xs
getSrcVal (P2 x) (p@(PROD y z dst) :: xs) = 
  if x == dst then Just z else getSrcVal (P2 x) xs
getSrcVal x (_ :: xs) = getSrcVal x xs

getProjPair: List TACGl1 -> List (TACData, TACData)
getProjPair xs = 
  let dstSrcs = getProjDstSrc xs
      dstMapsRaw = 
        map (\(dst, src) => (dst, getSrcVal src xs)) 
            dstSrcs
  in foldl (\xs, (dst, src) => 
         case src of
           Nothing => xs
           Just src => snoc xs (dst, src)) 
      [] dstMapsRaw
      
dropDstMatch': (dst: TACData) 
  -> List TACAtom1 -> List TACAtom1
dropDstMatch' dst [] = []
dropDstMatch' dst ((Gl x) :: xs) = 
  case x of
       p@(PROD  y z w) => 
         (Gl p) :: dropDstMatch' dst xs
       p@(PROJ1 y z)   => 
         if dst == z then xs 
         else (Gl p) :: dropDstMatch' dst xs
       p@(PROJ2 y z)   => 
         if dst == z then xs 
         else (Gl p) :: dropDstMatch' dst xs
dropDstMatch' dst ((Op x) :: xs) = 
  (Op x) :: dropDstMatch' dst xs

dropDstMatch: (dsts: List TACData) 
  -> List TACAtom1 -> List TACAtom1
dropDstMatch [] xs = xs
dropDstMatch (x :: ys) xs = 
  let rest = dropDstMatch' x xs
  in dropDstMatch ys rest

substAll: List (TACData, TACData) 
  -> List TACAtom1
  -> List TACAtom1
substAll [] ys = ys
substAll ((old, new) :: xs) ys = 
  let ys' = substBy1 old new ys
  in substAll xs ys'

substOut: List (TACData, TACData) 
  -> TACData -> TACData
substOut [] x = x
substOut ((old, new) :: xs) x = 
  if x == old then substOut xs new 
  else substOut xs x

public export
projElim: (1 _: LC TACSt TAC1) -> LC TACSt TAC1
projElim (l # (MkTAC1 input output ops)) = 
  let gls       = getGls ops
      projPairs = getProjPair gls
      ops'      = dropDstMatch (map fst projPairs) ops
      ops''     = substAll projPairs ops'
      output'   = substOut (reverse projPairs) output
  in l # (MkTAC1 input output' ops'')
