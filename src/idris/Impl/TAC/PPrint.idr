module Impl.TAC.PPrint

import Impl.TAC.TAC
import Data.BitVec 
import Data.LC

import System.File

ppTy: TACTy -> String
ppTy (BvTy width) = 
  "BV \{show width}"
ppTy (ProdTy a b) = 
  "(\{ppTy a}, \{ppTy b})"
ppTy UnitTy = "()"

ppName: Name -> String
ppName Anon = "_"
ppName (NM str) = str

ppData: TACData -> String
ppData (Const {n} x) = 
  "\{show x}: BV \{show n}"
ppData U = "() : ()"
ppData (Var nm ty1) = 
  "\{ppName nm}: \{ppTy ty1}"

ppSt: TACSt -> String
ppSt (MkSt name ty) = 
  "\{ppName name}: \{ppTy ty}"
  
ppGl1: TACGl1 -> String
ppGl1 (PROD x y dst) = 
  "\{ppData dst} = (\{ppData x}, \{ppData y})"
ppGl1 (PROJ1 x dst) = 
  "\{ppData dst} = proj1 \{ppData x}"
ppGl1 (PROJ2 x dst) = 
  "\{ppData dst} = proj2 \{ppData x}"

ppOp: TACOp1 -> String
ppOp (x ::= y) = 
  "\{ppData x} ::= \{ppData y}"
ppOp (x <<= y) = 
  "\{ppData x} <<= \{ppData y}"
ppOp (ADD x y dst) = 
  "\{ppData dst} = \{ppData x} + \{ppData y}"
ppOp (CONCAT x y dst) = 
  "\{ppData dst} = \{ppData x} :: \{ppData y}"
ppOp (AND x y dst) = 
  "\{ppData dst} = \{ppData x} & \{ppData y}"
ppOp (OR x y dst) = 
  "\{ppData dst} = \{ppData x} | \{ppData y}"
ppOp (XOR x y dst) = 
  "\{ppData dst} = \{ppData x} ^ \{ppData y}"
ppOp (EQ x y dst) = 
  "\{ppData dst} = \{ppData x} == \{ppData y}"
ppOp (LTU x y dst) = 
  "\{ppData dst} = \{ppData x} <U \{ppData y}"
ppOp (LT x y dst) = 
  "\{ppData dst} = \{ppData x} <S \{ppData y}"
ppOp (MUX21 x y z dst) = 
  "\{ppData dst} = if \{ppData x} then \{ppData y} else \{ppData z}"
ppOp (SLL k x dst) = 
  "\{ppData dst} = \{ppData x} << \{show k}"
ppOp (SRL k x dst) = 
  "\{ppData dst} = \{ppData x} >> \{show k}"
ppOp (SRA k x dst) = 
  "\{ppData dst} = \{ppData x} >>A \{show k}"
ppOp (NOT x dst) = 
  "\{ppData dst} = not \{ppData x}"
ppOp (SLICE k j x dst) = 
  "\{ppData dst} = (\{ppData x})<\{show k}:\{show j}>"
  
ppAtom1: TACAtom1 -> String
ppAtom1 (Gl x) = ppGl1 x
ppAtom1 (Op x) = ppOp x

export
ppTAC1: (1 _: LC TACSt TAC1) -> List String
ppTAC1 ((MkSt name ty) # (MkTAC1 input output ops)) = 
  "input: \{ppData input}" 
  :: "output: \{ppData output}" 
  :: "state: \{ppSt (MkSt name ty)}" 
  :: map ppAtom1 ops

ppGl2: TACGl2 -> String
ppGl2 (IDX x idx dst) = 
  "\{ppData dst} = \{ppData x}[\{show idx}]"

ppAtom2: TACAtom2 -> String
ppAtom2 (Gl2 x) = ppGl2 x
ppAtom2 (Op2 x) = ppOp x

export
ppTAC2: (1 _: LC TACSt TAC2) -> List String
ppTAC2 ((MkSt name ty) # (MkTAC2 input output ops)) = 
  "input: \{ppData input}" 
  :: "output: \{ppData output}" 
  :: "state: \{ppSt (MkSt name ty)}" 
  :: map ppAtom2 ops

writeLns: File -> List String -> IO ()
writeLns f [] = pure ()
writeLns f (x :: xs) = do Right () <- fPutStrLn f x
                            | Left err => printLn err
                          writeLns f xs

export
ppDump: String -> List String -> IO ()
ppDump name lns = 
  do (Right f) <- openFile "\{name}.txt" WriteTruncate
       | (Left err) => printLn err
     writeLns f lns
     closeFile f
