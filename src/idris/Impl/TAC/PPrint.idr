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

-- ppName: Name -> String
-- ppName Anon = "_"
-- ppName (NM str) = str

ppData': (p: String) -> TACData -> String
ppData' _ (Const x) = "\{show x}"
ppData' _ U = "()"
ppData' p (SVar label ty1) = 
  "\{p}_\{show label}"
ppData' p (CVar d1 d2 ty1) = 
  "(\{ppData' p d1}, \{ppData' p d2})"

export
ppData: TACData -> String
ppData x = 
  let ty = getTy x 
  in "\{ppData' "x" x}: \{ppTy ty}"


ppSt: TACSt -> String
ppSt (MkSt x) = 
  let ty = getTy x 
  in "\{ppData' "st" x}: \{ppTy ty}"

export  
ppOp1: TACOp1 -> String
ppOp1 (x ::= y) = 
  "\{ppSt x} ::= \{ppData y}"
ppOp1 (x <<= y) = 
  "\{ppData x} <<= \{ppSt y}"
ppOp1 (ADD x y dst) = 
  "\{ppData dst} = \{ppData x} + \{ppData y}"
ppOp1 (CONCAT x y dst) = 
  "\{ppData dst} = \{ppData x} :: \{ppData y}"
ppOp1 (AND x y dst) = 
  "\{ppData dst} = \{ppData x} & \{ppData y}"
ppOp1 (OR x y dst) = 
  "\{ppData dst} = \{ppData x} | \{ppData y}"
ppOp1 (XOR x y dst) = 
  "\{ppData dst} = \{ppData x} ^ \{ppData y}"
ppOp1 (EQ x y dst) = 
  "\{ppData dst} = \{ppData x} == \{ppData y}"
ppOp1 (LTU x y dst) = 
  "\{ppData dst} = \{ppData x} <U \{ppData y}"
ppOp1 (LT x y dst) = 
  "\{ppData dst} = \{ppData x} <S \{ppData y}"
ppOp1 (MUX21 x y z dst) = 
  "\{ppData dst} = if \{ppData x} then \{ppData y} else \{ppData z}"
ppOp1 (SLL k x dst) = 
  "\{ppData dst} = \{ppData x} << \{show k}"
ppOp1 (SRL k x dst) = 
  "\{ppData dst} = \{ppData x} >> \{show k}"
ppOp1 (SRA k x dst) = 
  "\{ppData dst} = \{ppData x} >>A \{show k}"
ppOp1 (NOT x dst) = 
  "\{ppData dst} = not \{ppData x}"
ppOp1 (SLICE k j x dst) = 
  "\{ppData dst} = (\{ppData x})<\{show k}:\{show j}>"

export
ppTAC1: (TACSt, TAC1) -> List String
ppTAC1 (st, MkTAC1 input output ops) = 
  "input: \{ppData input}" 
  :: "output: \{ppData output}" 
  :: "state: \{ppSt st}" 
  :: map ppOp1 ops

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
