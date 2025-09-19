module Impl.TAC.Json

import Impl.TAC.TAC
import Impl.TAC.Data
import Data.BitVec 
import Data.LC

import System.File
import Language.JSON
import Data.Bits

jsonTACTy: TACTy -> JSON
jsonTACTy (BvTy width) = 
  JObject [("bit-vector", JObject [("width", JString $ show width)])]
jsonTACTy (ProdTy a b) = 
  let j1 = jsonTACTy a 
      j2 = jsonTACTy b
  in JObject [("product", JObject [("fst", j1), ("snd", j2)])]
jsonTACTy UnitTy = 
  JString "unit"

jsonFTACData: FTACData -> JSON
jsonFTACData (Const {n} (BV val)) = 
  JObject [("data", 
            JObject [("constant",  
                       JObject [("width", JString $ show n), 
                                ("val", JString $ show val)])])]
jsonFTACData U = JObject [("data", JNull)]
jsonFTACData (SVar label ty1) = 
  JObject [("data", 
            JObject [("variable",  
                       JObject [("label", JString $ show label), 
                                ("type" , jsonTACTy ty1)])])]

jsonFlatSt: TACSt FTACData -> JSON
jsonFlatSt (MkSt (Const {n} (BV val))) = 
  JObject [("state", 
            JObject [("constant",  
                       JObject [("width", JString $ show n), 
                                ("val", JString $ show val)])])]
jsonFlatSt (MkSt U) = JObject [("state", JNull)]
jsonFlatSt (MkSt (SVar label ty1)) = 
  JObject [("state", 
            JObject [("variable",  
                       JObject [("label", JString $ show label), 
                                ("type" , jsonTACTy ty1)])])]

mkJsonOp: (op: String) -> (srcs: List FTACData) -> (dst: FTACData) -> JSON
mkJsonOp op srcs dst = 
  let jDst = jsonFTACData dst
      jSrcs = map jsonFTACData srcs
  in JObject[("op", JArray [JString op, JArray jSrcs, jDst])]

mkJsonOpwParams: (op: String) -> (params: List Nat) 
  -> (srcs: List FTACData) -> (dst: FTACData) -> JSON
mkJsonOpwParams op params srcs dst = 
  let jDst = jsonFTACData dst
      jSrcs = map jsonFTACData srcs
      jParams = map (\x => JString $ show x) params
  in JObject[("op", JArray [JString op, JArray jParams, JArray jSrcs, jDst])]

jsonFlatOp: TACOp FTACData -> JSON
jsonFlatOp (st ::= src) = 
  let jst = jsonFlatSt st
      jsrc = jsonFTACData src
  in JObject[("op", JArray [JString "set", jsrc, jst])]
jsonFlatOp (dst <<= st) = 
  let jst = jsonFlatSt st
      jdst = jsonFTACData dst
  in JObject[("op", JArray [JString "get", jst, jdst])]
jsonFlatOp (ADD src1 src2 dst) = 
  mkJsonOp "add" [src1, src2] dst
jsonFlatOp (CONCAT src1 src2 dst) = 
  mkJsonOp "concat" [src1, src2] dst
jsonFlatOp (AND src1 src2 dst) = 
  mkJsonOp "and" [src1, src2] dst
jsonFlatOp (OR src1 src2 dst) = 
  mkJsonOp "or" [src1, src2] dst
jsonFlatOp (XOR src1 src2 dst) = 
  mkJsonOp "xor" [src1, src2] dst
jsonFlatOp (EQ src1 src2 dst) = 
  mkJsonOp "eq" [src1, src2] dst
jsonFlatOp (LTU src1 src2 dst) =
  mkJsonOp "ltu" [src1, src2] dst
jsonFlatOp (LT src1 src2 dst) = 
  mkJsonOp "lt" [src1, src2] dst
jsonFlatOp (MUX21 src1 src2 src3 dst) = 
  mkJsonOp "mux21" [src1, src2, src3] dst
jsonFlatOp (SLL k src dst) = 
  mkJsonOpwParams "sll" [k] [src] dst
jsonFlatOp (SRL k src dst) = 
  mkJsonOpwParams "srl" [k] [src] dst
jsonFlatOp (SRA k src dst) = 
  mkJsonOpwParams "sra" [k] [src] dst
jsonFlatOp (NOT src dst) = 
  mkJsonOp "not" [src] dst
jsonFlatOp (SLICE k j src dst) = 
  mkJsonOpwParams "sll" [k, j] [src] dst
jsonFlatOp (MULT src1 src2 dst) = 
  mkJsonOp "mult" [src1, src2] dst


jsonFTAC: FTAC -> JSON
jsonFTAC (MkFTAC input output state ops) = 
  let jInput  = JArray $ map jsonFTACData input
      jOutput = JArray $ map jsonFTACData output
      jState  = JArray $ map jsonFlatSt state
      jOps    = JArray $ map jsonFlatOp ops
  in JObject [("input",  jInput),
              ("output", jOutput),
              ("state",  jState),
              ("ops",  jOps)]
              
export
jsonDump: String -> FTAC -> IO ()
jsonDump name tac = 
    do (Right f) <- openFile "\{name}.json" WriteTruncate
       | (Left err) => printLn err
       let str = format 4 $ jsonFTAC tac
       Right () <- fPutStrLn f str
       | Left err => printLn err
       closeFile f
