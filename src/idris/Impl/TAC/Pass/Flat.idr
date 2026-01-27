module Impl.TAC.Pass.Flat

import Impl.TAC.TAC
import Impl.TAC.Data

import Data.List

flatData: TACData -> List FTACData
flatData (Const x) = [Const x]
flatData U         = [U]
flatData (SVar label ty1) = [SVar label ty1]
flatData (CVar d1 d2 ty1) = flatData d1 ++ flatData d2

flatState: TACSt TACData -> List (TACSt FTACData)
flatState (MkSt x) = map (\x => MkSt x) (flatData x)

flatOp: TACOp TACData -> List (TACOp FTACData)
flatOp (st ::= src) = 
  zipWith (\x, y => x ::= y) 
          (flatState st) 
          (flatData src)
flatOp (dst <<= st) = 
  zipWith (\x, y => x <<= y) 
          (flatData dst) 
          (flatState st)
flatOp (ADD src1 src2 dst) = 
  zipWith3 (\x, y, z => ADD x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (CONCAT src1 src2 dst) = 
  zipWith3 (\x, y, z => CONCAT x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (AND src1 src2 dst) = 
  zipWith3 (\x, y, z => AND x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (OR src1 src2 dst) = 
  zipWith3 (\x, y, z => OR x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (XOR src1 src2 dst) = 
  zipWith3 (\x, y, z => XOR x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (EQ src1 src2 dst) = 
  zipWith3 (\x, y, z => EQ x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (LTU src1 src2 dst) = 
  zipWith3 (\x, y, z => LTU x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (LT src1 src2 dst) = 
  zipWith3 (\x, y, z => LT x y z) 
           (flatData src1) 
           (flatData src2) 
           (flatData dst)
flatOp (MUX21 src1 src2 src3 dst) = 
  zipWith3 (\x, (y1, y2), z => MUX21 x y1 y2 z) 
           (flatData src1) 
           (zip (flatData src2) 
                (flatData src3))
           (flatData dst)
flatOp (SLL k src dst) = 
  zipWith (\x, y => SLL k x y) 
          (flatData src) 
          (flatData dst)
flatOp (SRL k src dst) = 
  zipWith (\x, y => SRL k x y) 
          (flatData src) 
          (flatData dst)
flatOp (SRA k src dst) = 
  zipWith (\x, y => SRA k x y) 
          (flatData src) 
          (flatData dst)
flatOp (NOT src dst) = 
  zipWith (\x, y => NOT x y) 
          (flatData src) 
          (flatData dst)
flatOp (SLICE k j src dst) = 
  zipWith (\x, y => SLICE k j x y) 
          (flatData src) 
          (flatData dst)
flatOp (MULT src1 src2 dst) = 
  zipWith3 (\x, y, z => MULT x y z) 
           (flatData src1) 
           (flatData src2)
           (flatData dst)

flatOps: List (TACOp TACData) -> List (TACOp FTACData)
flatOps xs = xs >>= flatOp

public export
flatTAC: TAC -> FTAC
flatTAC x = 
  MkFTAC (flatData  x.input) 
         (flatData  x.output)
         (flatState x.state)
         (flatOps x.ops)
