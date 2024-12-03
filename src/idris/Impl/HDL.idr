module Impl.HDL

import public Impl.HDL.NetList
import public Impl.HDL.Comb
import public Impl.HDL.CombPrimitive
import public Impl.HDL.Seq
import public Impl.HDL.SeqPrimitive
import Impl.HDL.Flatten
import Impl.HDL.Verilog

import Control.Monad.State
import Data.LState2
import Data.LC
import Data.Linear

import System.File

genCNetList: Combinational a b -> FlattenCombNL
genCNetList x = flatCombNL $ snd $ runState 0 $ genComb x

genNetList: (1 _: Sequential s a b) -> !* FlattenNetList
genNetList seq = 
  let (LST2 runSt) = genSeq' seq 
      (nl # _) = runSt 0
  in flatNetList nl

               
writeCombVerilog': (name: String) -> FlattenCombNL -> IO ()
writeCombVerilog' name m = 
  let lns = combNetListStr name m
  in do (Right f) <- openFile "\{name}.v" WriteTruncate
          | (Left err) => printLn err
        writeLns f lns
        closeFile f


writeVerilog': (name: String) -> (1 _: !* FlattenNetList) -> IO ()
writeVerilog' name (MkBang m) = 
  let lns = netListStr name m
  in do (Right f) <- openFile "\{name}.v" WriteTruncate
          | (Left err) => printLn err
        writeLns f lns
        closeFile f
        
export
writeCombVerilog: (name: String) -> (Combinational a b) -> IO ()
writeCombVerilog name comb = writeCombVerilog' name (genCNetList comb)

export
writeVerilog: forall s, a, b. (name: String) -> (1 _: Sequential s a b) -> IO ()
writeVerilog name seq = writeVerilog' name (genNetList seq)
