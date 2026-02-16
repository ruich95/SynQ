module Impl.TAC.Verilog

import Impl.TAC.TAC
import Impl.TAC.Data
import Data.BitVec 

import Data.String

import System.File

data2Wire: FTACData -> String
data2Wire (SVar label ty1) = "x\{show label}"
data2Wire (Const x) = show x
data2Wire U = believe_me "impossible"

st2Reg: TACSt FTACData -> String
st2Reg (MkSt (SVar label ty1)) = "st\{show label}"
st2Reg (MkSt (Const x)) = show x
st2Reg (MkSt U) = believe_me "impossible"

getWidth: FTACData -> Nat
getWidth (SVar _ (BvTy width)) = width
getWidth (Const $ BV {n=n} _) = n
getWidth _ = believe_me "impossible"

declWire': FTACData -> String
declWire' wire = 
  let width = getWidth  wire
      name  = data2Wire wire
  in case width of
       0 => ""
       1 => "wire \{name}"
       (S (S k)) => "wire [\{show (S k)}:0] \{name}"

declWire: FTACData -> String
declWire wire = 
  let width = getWidth wire
  in case width of
       0 => ""
       _ => declWire' wire ++ ";"

declReg': (TACSt FTACData) -> String
declReg' (reg@(MkSt U)) = ""
declReg' (reg@(MkSt x)) = 
  let width = getWidth  x
      name  = st2Reg reg
  in case width of
       0 => ""
       1 => "reg \{name}"
       (S (S k)) => "reg [\{show (S k)}:0] \{name}"

declReg: TACSt FTACData -> String
declReg (reg@(MkSt x)) = 
  let width = getWidth x
  in case width of
       0 => ""
       _ => declReg' reg ++ ";"

notInOutputs: List FTACData -> FTACData -> Maybe FTACData
notInOutputs [] x = Just x
notInOutputs (y :: xs) x = 
  if y == x 
  then Nothing
  else notInOutputs xs x

getWireToDecl: List FTACData -> TACOp FTACData -> Maybe FTACData
getWireToDecl outputs (st ::= src)      = Nothing
getWireToDecl outputs (dst <<= st)      = notInOutputs outputs dst
getWireToDecl outputs (ADD _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (CONCAT _ _ dst)  = notInOutputs outputs dst
getWireToDecl outputs (AND _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (OR _ _ dst)      = notInOutputs outputs dst
getWireToDecl outputs (XOR _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (EQ _ _ dst)      = notInOutputs outputs dst
getWireToDecl outputs (LTU _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (LT _ _ dst)      = notInOutputs outputs dst
getWireToDecl outputs (MUX21 _ _ _ dst) = notInOutputs outputs dst
getWireToDecl outputs (SLL _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (SRL _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (SRA _ _ dst)     = notInOutputs outputs dst
getWireToDecl outputs (NOT _ dst)       = notInOutputs outputs dst
getWireToDecl outputs (SLICE _ _ _ dst) = notInOutputs outputs dst
getWireToDecl outputs (MULT _ _ dst)    = notInOutputs outputs dst

getRegAssign: (TACOp FTACData) -> Maybe String
getRegAssign (st ::= src) = Just "\{st2Reg st} <= \{data2Wire src};"
getRegAssign x = Nothing

op2ModuleInst: (TACOp FTACData) -> (List String)
op2ModuleInst (st ::= src) = []
op2ModuleInst (dst <<= st) = ["assign \{data2Wire dst} = \{st2Reg st};"]
op2ModuleInst (ADD src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["add #(.LEN(\{show width}))",
      "  add_\{dstStr} (",
      "      .add_in_1(\{src1Str}),",
      "      .add_in_2(\{src2Str}),",
      "      .add_out(\{dstStr}));"]
op2ModuleInst (CONCAT src1 src2 dst) = 
  let width1  = getWidth src1
      width2  = getWidth src2
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["concat #(.LEN1(\{show width1}), .LEN2(\{show width2}))",
      "  concat_\{dstStr} (",
      "      .concat_in_1(\{src1Str}),",
      "      .concat_in_2(\{src2Str}),",
      "      .concat_out(\{dstStr}));"]
op2ModuleInst (AND src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["and_comp #(.LEN(\{show width}))",
      "  and_comp_\{dstStr} (",
      "      .and_comp_in_1(\{src1Str}),",
      "      .and_comp_in_2(\{src2Str}),",
      "      .and_comp_out(\{dstStr}));"]
op2ModuleInst (OR src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["or_comp #(.LEN(\{show width}))",
      "  or_comp_\{dstStr} (",
      "      .or_comp_in_1(\{src1Str}),",
      "      .or_comp_in_2(\{src2Str}),",
      "      .or_comp_out(\{dstStr}));"]
op2ModuleInst (XOR src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["xor_comp #(.LEN(\{show width}))",
      "  xor_comp_\{dstStr} (",
      "      .xor_comp_in_1(\{src1Str}),",
      "      .xor_comp_in_2(\{src2Str}),",
      "      .xor_comp_out(\{dstStr}));"]
op2ModuleInst (EQ src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["eq #(.LEN(\{show width}))",
      "  eq_\{dstStr} (",
      "      .eq_in_1(\{src1Str}),",
      "      .eq_in_2(\{src2Str}),",
      "      .eq_out(\{dstStr}));"]
op2ModuleInst (LTU src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["ltu #(.LEN(\{show width}))",
      "  ltu_\{dstStr} (",
      "      .ltu_in_1(\{src1Str}),",
      "      .ltu_in_2(\{src2Str}),",
      "      .ltu_out(\{dstStr}));"]
op2ModuleInst (LT src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in ["lt #(.LEN(\{show width}))",
      "  lt_\{dstStr} (",
      "      .lt_in_1(\{src1Str}),",
      "      .lt_in_2(\{src2Str}),",
      "      .lt_out(\{dstStr}));"]
op2ModuleInst (MUX21 src1 src2 src3 dst) = 
  let width   = getWidth src2
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      src3Str = data2Wire src3
      dstStr  = data2Wire dst
  in ["mux21_comp #(.LEN(\{show width}))",
      "  mux21_comp_\{dstStr} (",
      "      .mux21_comp_sel(\{src1Str}),",
      "      .mux21_comp_in_1(\{src2Str}),",
      "      .mux21_comp_in_2(\{src3Str}),",
      "      .mux21_comp_out(\{dstStr}));"]
op2ModuleInst (SLL k src dst) = 
  let width   = getWidth src
      src1Str = data2Wire src
      dstStr  = data2Wire dst
  in ["sll #(.LEN(\{show width}), .SHAMT(\{show k}))",
      "  sll_\{dstStr} (",
      "      .sll_in_1(\{src1Str}),",
      "      .sll_out(\{dstStr}));"]
op2ModuleInst (SRL k src dst) = 
  let width   = getWidth src
      src1Str = data2Wire src
      dstStr  = data2Wire dst
  in ["srl #(.LEN(\{show width}), .SHAMT(\{show k}))",
      "  srl_\{dstStr} (",
      "      .srl_in_1(\{src1Str}),",
      "      .srl_out(\{dstStr}));"]
op2ModuleInst (SRA k src dst) = 
  let width   = getWidth src
      src1Str = data2Wire src
      dstStr  = data2Wire dst
  in ["sra #(.LEN(\{show width}), .SHAMT(\{show k}))",
      "  sra_\{dstStr} (",
      "      .sra_in_1(\{src1Str}),",
      "      .sra_out(\{dstStr}));"]
op2ModuleInst (NOT src dst) = 
  let width   = getWidth src
      src1Str = data2Wire src
      dstStr  = data2Wire dst
  in ["not_comp #(.LEN(\{show width}))",
      "  not_comp_\{dstStr} (",
      "      .not_comp_in_1(\{src1Str}),",
      "      .not_comp_out(\{dstStr}));"]
op2ModuleInst (SLICE k j src dst) = 
  let width   = getWidth src
      src1Str = data2Wire src
      dstStr  = data2Wire dst
  in ["slice #(.LEN(\{show width}), .LOWER(\{show k}), .UPPER(\{show j}))",
      "  slice_\{dstStr} (",
      "      .slice_in_1(\{src1Str}),",
      "      .slice_out(\{dstStr}));"]
op2ModuleInst (MULT src1 src2 dst) = 
  let width   = getWidth src1
      src1Str = data2Wire src1
      src2Str = data2Wire src2
      dstStr  = data2Wire dst
  in if width /= 18 
     then ["unsupported multiplyer"]
     else ["mult18 mult18_\{dstStr} (",
           "    .mult18_in_1(\{src1Str}),",
           "    .mult18_in_2(\{src2Str}),",
           "    .mult18_out(\{dstStr}));"]

ops2WireDecls: List FTACData -> List (TACOp FTACData) -> List String
ops2WireDecls outputs [] = []
ops2WireDecls outputs (x :: xs) = 
  case getWireToDecl outputs x of 
    Nothing => ops2WireDecls outputs xs
    Just wire => declWire wire :: ops2WireDecls outputs xs

ops2ModuleInst: List (TACOp FTACData) -> List String
ops2ModuleInst [] = []
ops2ModuleInst (op :: ops) = 
  let moduleInsts = op2ModuleInst op
      rest        = ops2ModuleInst ops
  in moduleInsts ++ [""] ++ rest

ops2RegAssigns: List (TACOp FTACData) -> List String
ops2RegAssigns [] = []
ops2RegAssigns (x :: xs) = 
  case getRegAssign x of
       Nothing => ops2RegAssigns xs
       (Just s) => s :: ops2RegAssigns xs

inputParams: List FTACData -> List String
inputParams [] = []
inputParams (i :: is) = 
  "input \{declWire' i}," :: inputParams is

outputParams: List FTACData -> List String
outputParams [] = []
outputParams (o :: []) = ["output \{declWire' o}"]
outputParams (o :: os@(_ :: _)) = 
    "output \{declWire' o}," :: outputParams os 

declRegs: List (TACSt FTACData) -> List String
declRegs = map declReg

toLns: (name: String) -> FTAC -> List String
toLns name (MkFTAC input output state ops) = 
  let inputParamList  = map (indent 4) $ inputParams input
      outputParamList = map (indent 4) $ outputParams output
      wireDecls       = map (indent 4) $ ops2WireDecls output ops
      regDecls        = map (indent 4) $ declRegs state
      moduleInsts     = map (indent 4) $ ops2ModuleInst ops
      regAssigns      = map (indent 8) $ ops2RegAssigns ops
  in ["module \{name} (",
      indent 4 "input wire clk,"]
  ++ inputParamList 
  ++ outputParamList 
  ++ [");"]
  ++ wireDecls
  ++ [""]
  ++ regDecls
  ++ [""]
  ++ moduleInsts
  ++ [""]
  ++ [indent 4 "always @ (posedge clk) begin"]
  ++ regAssigns
  ++ [indent 4 "end",
      "endmodule"]
      
writeLns: File -> List String -> IO ()
writeLns f [] = pure ()
writeLns f (x :: xs) = do Right () <- fPutStrLn f x
                            | Left err => printLn err
                          writeLns f xs
      
export  
dumpVerilog: (name: String) -> FTAC -> IO ()
dumpVerilog name tac = 
  let lns = toLns name tac
  in do (Right f) <- openFile "\{name}.v" WriteTruncate
          | (Left err) => printLn err
        writeLns f lns
        closeFile f
