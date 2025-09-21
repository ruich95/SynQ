module Impl.TAC.Json

import Impl.TAC.TAC
import Impl.TAC.Data
import Data.BitVec 
import Data.LC

import System.File
import Language.JSON
import Data.String

jsonTACTy: TACTy -> JSON
jsonTACTy (BvTy width) = 
  JObject [("bit-vector", JObject [("width", JString $ show width)])]
jsonTACTy (ProdTy a b) = 
  let j1 = jsonTACTy a 
      j2 = jsonTACTy b
  in JObject [("product", JObject [("fst", j1), ("snd", j2)])]
jsonTACTy UnitTy = 
  JString "unit"

json2TACTy: JSON -> Maybe TACTy
json2TACTy (JString "unit") = Just UnitTy
json2TACTy (JObject [("bit-vector", 
              JObject [("width", JString wstr)])]) = 
  do width <- parsePositive {a=Nat} wstr
     pure $ BvTy width
json2TACTy (JObject [("product", JObject [("fst", j1), ("snd", j2)])]) = 
  do ty1 <- json2TACTy j1
     ty2 <- json2TACTy j2
     pure $ ProdTy ty1 ty2
json2TACTy _ = Nothing

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

json2FTACData: JSON -> Maybe FTACData
json2FTACData 
  (JObject [("data", 
    JObject [("constant",  
      JObject [("width", JString wstr), 
               ("val", JString vstr)])])]) =
  do width <- parsePositive {a=Nat} wstr
     val   <- parsePositive {a=Bits64} vstr
     pure $ Const {n=width} $ BV val
json2FTACData 
  (JObject [("data", 
    JObject [("variable",  
      JObject [("label", JString labelstr), 
               ("type" , jty)])])]) = 
  do label <- parsePositive labelstr 
     ty    <- json2TACTy jty
     pure $ SVar label ty
json2FTACData (JObject [("data", JNull)]) = Just U
json2FTACData _ = Nothing

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

json2FlatSt: JSON -> Maybe (TACSt FTACData)
json2FlatSt
  (JObject [("state", 
    JObject [("constant",  
      JObject [("width", JString wstr), 
               ("val", JString vstr)])])]) =
  do width <- parsePositive {a=Nat} wstr
     val   <- parsePositive {a=Bits64} vstr
     pure $ MkSt $ Const {n=width} $ BV val
json2FlatSt
  (JObject [("state", 
    JObject [("variable",  
      JObject [("label", JString labelstr), 
               ("type" , jty)])])]) = 
  do label <- parsePositive labelstr 
     ty    <- json2TACTy jty
     pure $ MkSt $ SVar label ty
json2FlatSt (JObject [("state", JNull)]) = Just $ MkSt U
json2FlatSt _ = Nothing

mkJsonOp1: (op: String) 
  -> (src1: FTACData) 
  -> (dst : FTACData) 
  -> JSON
mkJsonOp1 op src1 dst = 
  let jSrc1 = jsonFTACData src1
      jDst  = jsonFTACData dst
  in JObject[("op", 
       JObject [(op, 
         JObject [("src1", jSrc1), 
                  ("dst",  jDst)])])]

mkOp1: String -> JSON -> Maybe (TACOp FTACData)
mkOp1 "not" 
      (JObject [("src1", jSrc1), 
                ("dst",  jDst)]) = 
      do src1 <-json2FTACData jSrc1 
         dst <- json2FTACData jDst
         pure $ NOT src1 dst
mkOp1 str json = Nothing

mkJsonP1Op1: (op: String) 
  -> (param: (String, Nat))
  -> (src1 : FTACData) 
  -> (dst  : FTACData) 
  -> JSON
mkJsonP1Op1 op (pkey, param) src dst = 
  let jSrc  = jsonFTACData src
      jDst   = jsonFTACData dst
  in JObject[("op", 
       JObject [(op, 
         JObject [(pkey, JString $ show param),
                  ("src", jSrc), 
                  ("dst",  jDst)])])]

mkP1Op1: String -> JSON -> Maybe (TACOp FTACData)
mkP1Op1 strOp 
        (JObject [(pkey, JString strParam),
                  ("src", jSrc), 
                  ("dst",  jDst)]) = 
        do shtmt <- parsePositive {a=Nat} strParam
           src   <- json2FTACData jSrc
           dst   <- json2FTACData jDst
           case strOp of
             "sll" => pure $ SLL shtmt src dst
             "srl" => pure $ SRL shtmt src dst
             "sra" => pure $ SRA shtmt src dst
             _ => Nothing
mkP1Op1 str json = Nothing

mkJsonP2Op1: (op: String) 
  -> (param1: (String, Nat))
  -> (param2: (String, Nat))
  -> (src1 : FTACData) 
  -> (dst  : FTACData) 
  -> JSON
mkJsonP2Op1 op (pkey1, param1) (pkey2, param2) src1 dst = 
  let jSrc1  = jsonFTACData src1
      jDst   = jsonFTACData dst
  in JObject[("op", 
       JObject [(op, 
         JObject [(pkey1, JString $ show param1),
                  (pkey2, JString $ show param2),
                  ("src1", jSrc1), 
                  ("dst",  jDst)])])]

mkP2Op1: String -> JSON -> Maybe (TACOp FTACData)
mkP2Op1 "slice" 
        (JObject [("lower", JString strLower),
                  ("upper", JString strUpper),
                  ("src", jSrc), 
                  ("dst",  jDst)]) = 
        do lower <- parsePositive strLower
           upper <- parsePositive strUpper
           src   <- json2FTACData jSrc
           dst   <- json2FTACData jDst
           pure $ SLICE lower upper src dst
mkP2Op1 str json = Nothing

mkJsonOp2: (op: String) 
  -> (src1: FTACData) 
  -> (src2: FTACData) 
  -> (dst : FTACData) 
  -> JSON
mkJsonOp2 op src1 src2 dst = 
  let jSrc1 = jsonFTACData src1
      jSrc2 = jsonFTACData src2
      jDst  = jsonFTACData dst
  in JObject[("op", 
       JObject [(op, 
         JObject [("src1", jSrc1), 
                  ("src2", jSrc2), 
                  ("dst",  jDst)])])]

mkOp2: String -> JSON -> Maybe (TACOp FTACData)
mkOp2 op 
  (JObject [("src1", jSrc1), 
            ("src2", jSrc2), 
            ("dst",  jDst)]) = 
    do src1 <- json2FTACData jSrc1
       src2 <- json2FTACData jSrc2
       dst  <- json2FTACData jDst
       case op of
         "add"    => pure $ ADD src1 src2 dst
         "concat" => pure $ CONCAT src1 src2 dst
         "and"    => pure $ AND src1 src2 dst
         "or"     => pure $ OR src1 src2 dst
         "xor"    => pure $ XOR src1 src2 dst
         "eq"     => pure $ EQ src1 src2 dst
         "ltu"    => pure $ LTU src1 src2 dst
         "lt"     => pure $ LT src1 src2 dst
         "mult"   => pure $ MULT src1 src2 dst
         _ => Nothing
mkOp2 _ _ = Nothing

mkJsonOp3: (op: String) 
  -> (src1: FTACData) 
  -> (src2: FTACData) 
  -> (src3: FTACData) 
  -> (dst : FTACData) 
  -> JSON
mkJsonOp3 op src1 src2 src3 dst = 
  let jSrc1 = jsonFTACData src1
      jSrc2 = jsonFTACData src2
      jSrc3 = jsonFTACData src3
      jDst  = jsonFTACData dst
  in JObject[("op", 
       JObject [(op, 
         JObject [("src1", jSrc1), 
                  ("src2", jSrc2), 
                  ("src3", jSrc3), 
                  ("dst",  jDst)])])]

mkOp3: String -> JSON -> Maybe (TACOp FTACData)
mkOp3 "mux21" 
      (JObject [("src1", jSrc1), 
                ("src2", jSrc2), 
                ("src3", jSrc3), 
                ("dst",  jDst)]) = 
      do src1 <- json2FTACData jSrc1
         src2 <- json2FTACData jSrc2
         src3 <- json2FTACData jSrc3
         dst  <- json2FTACData jDst
         pure $ MUX21 src1 src2 src3 dst
mkOp3 str json = Nothing

jsonFlatOp: TACOp FTACData -> JSON
jsonFlatOp (st ::= src) = 
  let jst = jsonFlatSt st
      jsrc = jsonFTACData src
  in JObject[("op", 
       JObject [("set", 
         JObject [("st", jst), 
                  ("src", jsrc)])])]
jsonFlatOp (dst <<= st) = 
  let jst = jsonFlatSt st
      jdst = jsonFTACData dst
  in JObject[("op", 
       JObject [("get", 
         JObject [("dst", jdst), 
                  ("st", jst)])])]
jsonFlatOp (ADD src1 src2 dst) = 
  mkJsonOp2 "add" src1 src2 dst
jsonFlatOp (CONCAT src1 src2 dst) = 
  mkJsonOp2 "concat" src1 src2 dst
jsonFlatOp (AND src1 src2 dst) = 
  mkJsonOp2 "and" src1 src2 dst
jsonFlatOp (OR src1 src2 dst) = 
  mkJsonOp2 "or" src1 src2 dst
jsonFlatOp (XOR src1 src2 dst) = 
  mkJsonOp2 "xor" src1 src2 dst
jsonFlatOp (EQ src1 src2 dst) = 
  mkJsonOp2 "eq" src1 src2 dst
jsonFlatOp (LTU src1 src2 dst) =
  mkJsonOp2 "ltu" src1 src2 dst
jsonFlatOp (LT src1 src2 dst) = 
  mkJsonOp2 "lt" src1 src2 dst
jsonFlatOp (MUX21 src1 src2 src3 dst) = 
  mkJsonOp3 "mux21" src1 src2 src3 dst
jsonFlatOp (SLL k src dst) = 
  mkJsonP1Op1 "sll" ("sht", k) src dst
jsonFlatOp (SRL k src dst) = 
  mkJsonP1Op1 "srl" ("sht", k) src dst
jsonFlatOp (SRA k src dst) = 
  mkJsonP1Op1 "sra" ("sht", k) src dst
jsonFlatOp (NOT src dst) = 
  mkJsonOp1 "not" src dst
jsonFlatOp (SLICE k j src dst) = 
  mkJsonP2Op1 "slice" ("lower", k) ("upper", j) src dst
jsonFlatOp (MULT src1 src2 dst) = 
  mkJsonOp2 "mult" src1 src2 dst

op2: List String
op2 = ["add", "concat", "and", "or", "xor", "eq", "ltu", "lt", "mult"]

op1: List String
op1 = ["not"]

op3: List String
op3 = ["mux21"]

p1Op1: List String 
p1Op1 = ["sll", "srl", "sra"]

p2Op1: List String 
p2Op1 = ["slice"]

isElement: Eq a => a -> List a -> Maybe a
isElement x [] = Nothing
isElement x (y :: xs) = 
  if x /= y 
  then isElement x xs 
  else Just x

json2FlatOp: JSON -> Maybe (TACOp FTACData)
json2FlatOp 
  (JObject [("op", 
     JObject [("get", body)])]) = 
       case body of 
         JObject [("dst", jdst), 
                  ("st", jst)] => 
           do dst <- json2FTACData jdst 
              st  <- json2FlatSt jst
              pure $ dst <<= st
         _ => Nothing
json2FlatOp 
  (JObject [("op", 
     JObject [("set", body)])]) = 
       case body of 
         JObject [("st", jst), 
                  ("src", jsrc)] => 
           do st <- json2FlatSt jst 
              src <- json2FTACData jsrc
              pure $ st ::= src
         _ => Nothing
json2FlatOp 
  (JObject [("op", 
     JObject [(op, body)])]) = 
       case isElement op op2 of
         Nothing => 
           case isElement op op1 of
             Nothing => 
               case isElement op p1Op1 of
                 Nothing => 
                   case isElement op p2Op1 of
                     Nothing => 
                       case isElement op op3 of
                         Nothing => Nothing
                         Just op => mkOp3 op body
                     Just op => mkP2Op1 op body
                 Just op => mkP1Op1 op body
             Just op => mkOp1 op body
         Just op => mkOp2 op body
json2FlatOp _ = Nothing

jsonFTAC: FTAC -> JSON
jsonFTAC (MkFTAC input output state ops) = 
  let jInput  = JArray $ map jsonFTACData input
      jOutput = JArray $ map jsonFTACData output
      jState  = JArray $ map jsonFlatSt state
      jOps    = JArray $ map jsonFlatOp ops
  in JObject [("input" ,  jInput),
              ("output", jOutput),
              ("state" ,  jState),
              ("ops"   ,  jOps)]

export
jsonDump: String -> FTAC -> IO ()
jsonDump name tac = 
  do (Right f) <- openFile "\{name}.json" WriteTruncate
     | (Left err) => printLn err
     let str = format 4 $ jsonFTAC tac
     Right () <- fPutStrLn f str
     | Left err => printLn err
     closeFile f

swap: List (Maybe a) -> Maybe (List a)
swap [] = Just []
swap (x :: xs) = [| x :: swap xs|]

json2FTAC: JSON -> Maybe FTAC
json2FTAC (JObject [("input" , JArray jInput),
                    ("output", JArray jOutput),
                    ("state" , JArray jState),
                    ("ops"   , JArray jOps)]) = 
          do input  <- swap $ map json2FTACData jInput
             output <- swap $ map json2FTACData jOutput
             state  <- swap $ map json2FlatSt   jState
             ops    <- swap $ map json2FlatOp   jOps
             pure $ MkFTAC input output state ops
json2FTAC _ = Nothing

export
jsonLoad: String -> IO FTAC
jsonLoad name = 
  do (Right f) <- openFile "\{name}.json" Read
       | Left err => 
           do printLn err
              pure $ MkFTAC [] [] [] []
     Right jString <- fRead f
       | Left err => 
           do printLn err
              pure $ MkFTAC [] [] [] []
     Just json <- pure $ parse jString
       | Nothing => 
           do printLn "invalid JSON file."
              pure $ MkFTAC [] [] [] []
     Just tac <- pure $ json2FTAC json
       | Nothing => 
           do printLn "illformed JSON fill."
              pure $ MkFTAC [] [] [] []
     closeFile f;
     pure tac

export
jStrLoad: String -> Maybe FTAC
jStrLoad str = 
  do json <- parse str
     json2FTAC json

var: Nat -> FTACData
var x = SVar x $ BvTy 8

cst: Bits64 -> FTACData
cst m = Const $ BV {n=8} m

st: Nat -> TACSt FTACData
st x = MkSt $ var x

export
wsum: FTAC
wsum = 
  MkFTAC 
    [var 0] 
    [var 1] 
    [st 2, st 3, st 4] 
    [(var 5) <<= (st 2),
     (var 6) <<= (st 3),
     (var 7) <<= (st 4),
     MULT (var 0)  (cst 1)  (var 8),
     MULT (var 5)  (cst 1)  (var 9),
     MULT (var 6)  (cst 1)  (var 10),
     MULT (var 7)  (cst 1)  (var 11),
     ADD  (var 8)  (var 9)  (var 12),
     ADD  (var 10) (var 11) (var 13),
     ADD  (var 12) (var 13) (var 1),
     (st 2) ::= (var 0),
     (st 3) ::= (var 5),
     (st 4) ::= (var 6)]

export     
test: FTAC -> Maybe Bool
test tac = 
  do tac' <- json2FTAC $ jsonFTAC tac
     pure $ tac == tac'

export
dumpLoadTest: String -> FTAC -> {default True remove: Bool} -> IO ()
dumpLoadTest str tac {remove} = 
  do jsonDump str tac;
     tac' <- jsonLoad str
     printLn $ 
       (if (tac' == tac) 
        then "SUCCESS: loaded and dumped are the same."
        else "FAIL: loaded and dumped are not the same.")
     True <- pure remove 
       | _ => pure ()
     Right _ <- removeFile "\{str}.json"
       | Left err => printLn err
     pure ()

export
testJString: String
testJString = format 0 $ jsonFTAC wsum
