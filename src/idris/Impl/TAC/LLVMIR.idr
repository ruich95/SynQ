module Impl.TAC.LLVMIR

import Impl.TAC.TAC
import Impl.TAC.Data
import Data.BitVec 

import Data.String

import Control.Monad.State

import System.File

data2Reg: FTACData -> String
data2Reg (SVar label ty1) = "%x\{show label}"
data2Reg (Const $ BV x) = show x
data2Reg U = believe_me "impossible"

st2Reg: TACSt FTACData -> String
st2Reg (MkSt (SVar label ty1)) = "@st\{show label}"
st2Reg (MkSt (Const $ BV x)) = show x
st2Reg (MkSt U) = believe_me "impossible"

data2iTy: FTACData -> String
data2iTy (SVar _ (BvTy width)) = "i\{show width}"
data2iTy (Const $ BV {n=n} _) = "i\{show n}"
data2iTy _ = believe_me "impossible"

getWidth: FTACData -> Nat
getWidth (SVar _ (BvTy width)) = width
getWidth (Const $ BV {n=n} _) = n
getWidth _ = believe_me "impossible"

opToInst: (TACOp FTACData) -> State Nat (List String)
opToInst (st ::= src) = 
  pure ["store \{data2iTy src} \{data2Reg src}, ptr \{st2Reg st}"]
opToInst (dst <<= st) = 
  pure ["\{data2Reg dst} = load \{data2iTy dst}, ptr \{st2Reg st}"]
opToInst (AND src1 src2 dst) = 
  pure ["\{data2Reg dst} = and \{data2iTy dst} \{data2Reg src1}, \{data2Reg src2}"]
opToInst (OR src1 src2 dst) = 
  pure ["\{data2Reg dst} = or \{data2iTy dst} \{data2Reg src1}, \{data2Reg src2}"]
opToInst (XOR src1 src2 dst) = 
  pure ["\{data2Reg dst} = xor \{data2iTy dst} \{data2Reg src1}, \{data2Reg src2}"]
opToInst (NOT src dst) = 
  pure ["\{data2Reg dst} = xor \{data2iTy dst} \{data2Reg src}, -1"]
opToInst (EQ src1 src2 dst) = 
  pure ["\{data2Reg dst} = icmp eq \{data2iTy src1} \{data2Reg src1}, \{data2Reg src2}"]
opToInst (LTU src1 src2 dst) = 
  pure ["\{data2Reg dst} = icmp ult \{data2iTy src1} \{data2Reg src1}, \{data2Reg src2}"]
opToInst (LT src1 src2 dst) = 
  pure ["\{data2Reg dst} = icmp slt \{data2iTy src1} \{data2Reg src1}, \{data2Reg src2}"]
opToInst (MUX21 src1 src2 src3 dst) = 
  pure ["\{data2Reg dst} = select i1  \{data2Reg src1}, \{data2iTy dst} \{data2Reg src2}, \{data2iTy dst} \{data2Reg src3}"]
opToInst (SLL k src dst) = 
  pure ["\{data2Reg dst} = shl \{data2iTy dst} \{data2Reg src}, \{show k}"]
opToInst (SRL k src dst) = 
  pure ["\{data2Reg dst} = lshr \{data2iTy dst} \{data2Reg src}, \{show k}"]
opToInst (SRA k src dst) = 
  pure ["\{data2Reg dst} = ashr \{data2iTy dst} \{data2Reg src}, \{show k}"]
opToInst (ADD src1 src2 dst) = 
  let tySrc = data2iTy src1
      tyDst = data2iTy dst
      src1Reg = data2Reg src1
      src2Reg = data2Reg src2
      dstReg  = data2Reg dst
  in ST $ \c => Id
       ((S $ S c), 
        let src1Imm = "\{dstReg}.\{show c}"
            src2Imm = "\{dstReg}.\{show $ S c}"
        in ["\{src1Imm} = zext \{tySrc} \{src1Reg} to \{tyDst}",
            "\{src2Imm} = zext \{tySrc} \{src2Reg} to \{tyDst}",
            "\{dstReg} = add \{tyDst} \{src1Imm}, \{src2Imm}"])
opToInst (MULT src1 src2 dst) = 
  let tySrc = data2iTy src1
      tyDst = data2iTy dst
      src1Reg = data2Reg src1
      src2Reg = data2Reg src2
      dstReg  = data2Reg dst
  in ST $ \c => Id
       ((S $ S c), 
        let src1Imm = "\{dstReg}.\{show c}"
            src2Imm = "\{dstReg}.\{show $ S c}"
        in ["\{src1Imm} = sext \{tySrc} \{src1Reg} to \{tyDst}",
            "\{src2Imm} = sext \{tySrc} \{src2Reg} to \{tyDst}",
            "\{dstReg} = mul \{tyDst} \{src1Imm}, \{src2Imm}"])
opToInst (SLICE k j src dst) = 
  let dstTy = "i\{show $ minus j k}"
      srcTy = data2iTy src
      srcReg = data2Reg src
      dstReg = data2Reg dst
  in ST $ \c => Id
       ((S c),
        ["\{dstReg}.\{show c} = lshr \{srcTy} \{srcReg}, \{show k}",
         "\{dstReg} = trunc \{srcTy} \{dstReg}.\{show c} to \{dstTy}"])
opToInst (CONCAT src1 src2 dst) = 
  let tySrc1 = data2iTy src1
      tySrc2 = data2iTy src2
      tyDst = data2iTy dst
      src1Reg = data2Reg src1
      src2Reg = data2Reg src2
      dstReg  = data2Reg dst
      shtmt = getWidth src2
  in ST $ \c => Id
       ((S $ S $ S c), 
        let src1Imm1 = "\{dstReg}.\{show c}"
            src1Imm2 = "\{dstReg}.\{show $ S c}"
            src2Imm = "\{dstReg}.\{show $ S $ S c}"
        in ["\{src1Imm1} = zext \{tySrc1} \{src1Reg} to \{tyDst}",
            "\{src1Imm2} = shl \{tyDst} \{src1Imm1}, \{show shtmt}",
            "\{src2Imm} = zext \{tySrc2} \{src2Reg} to \{tyDst}",
            "\{dstReg} = or \{tyDst} \{src1Imm2}, \{src2Imm}"])

opsToInst: List (TACOp FTACData) -> State Nat (List String)
opsToInst [] = pure []
opsToInst (op :: ops) = 
  do insts <- opToInst op
     rest  <- opsToInst ops
     pure $ insts ++ rest

stToGlobal': TACSt FTACData -> String
stToGlobal' st@(MkSt x) = 
  "\{st2Reg st} = private global \{data2iTy x} 0"

stToGlobal: List (TACSt FTACData) -> List String
stToGlobal = map stToGlobal'

inputToParams: List FTACData -> String
inputToParams [] = ""
inputToParams (i :: []) = "i64 \{data2Reg i}.i"
inputToParams (i :: is@(_ :: _)) = 
  let iStr = "i64 \{data2Reg i}.i"
      isStr = inputToParams is
  in "\{iStr}, \{isStr}"
  
inputTrunc': FTACData -> String
inputTrunc' x = 
  "\{data2Reg x} = trunc i64 \{data2Reg x}.i to \{data2iTy x}"

inputTrunc: List FTACData -> List String
inputTrunc = map inputTrunc'

outputBufToGlobal: List FTACData -> String
outputBufToGlobal xs = 
  let nEle = length xs
  in "@outputs = private global [\{show nEle} x i64] zeroinitializer"
  
outputAssign': (nEle: Nat) -> Nat -> FTACData -> List String
outputAssign' nEle k x = 
  let xReg = data2Reg x
      xTy = data2iTy x
  in ["\{xReg}.oe = sext \{xTy} \{xReg} to i64",
      "\{xReg}.optr = getelementptr [\{show nEle} x i64], ptr @outputs, i64 0, i64 \{show k}",
      "store i64 \{xReg}.oe, ptr \{xReg}.optr"]

outputAssign: List FTACData -> List String
outputAssign xs = 
  let nEle = length xs
  in assignOutput'' nEle 0 xs
  where
    assignOutput'': (nEle:Nat) -> Nat -> List FTACData -> List String
    assignOutput'' nEle n [] = []
    assignOutput'' nEle n (x :: xs) = 
      let cur = outputAssign' nEle n x
      in cur ++ assignOutput'' nEle (S n) xs
      
toLns: (name: String) -> FTAC -> List String
toLns name (MkFTAC input output state ops) = 
  let inputParamList = inputToParams input
      inputVarTrunc = inputTrunc input
      outputBuffer = outputBufToGlobal output
      outputAssigns = outputAssign output
      stList = stToGlobal state
      instList = snd $ runState 0 (opsToInst ops)
  in [outputBuffer, ""] 
  ++ stList
  ++ ["",
      "define ptr @\{name}(\{inputParamList}){",
      "entry:"]
  ++ map (indent 4) inputVarTrunc
  ++ [""]
  ++ map (indent 4) instList
  ++ [""]
  ++ map (indent 4) outputAssigns
  ++ [indent 4 "ret ptr @outputs", "}"]

writeLns: File -> List String -> IO ()
writeLns f [] = pure ()
writeLns f (x :: xs) = do Right () <- fPutStrLn f x
                            | Left err => printLn err
                          writeLns f xs
      
export  
dumpLLVMIR: (name: String) -> FTAC -> IO ()
dumpLLVMIR name tac = 
  let lns = toLns name tac
  in do (Right f) <- openFile "\{name}.ll" WriteTruncate
          | (Left err) => printLn err
        writeLns f lns
        closeFile f
