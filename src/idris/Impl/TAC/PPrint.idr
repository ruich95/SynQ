module Impl.TAC.PPrint

import Impl.TAC.TAC
import Impl.TAC.Data
import Data.BitVec 
import Data.LC

import System.File


ppTAC: TAC -> List String
ppTAC (MkTAC input output st ops) = 
  "input: \{show input}" 
  :: "output: \{show output}" 
  :: "state: \{show st}" 
  :: map show ops
  

ppFTAC: FTAC -> List String
ppFTAC (MkFTAC inputs outputs sts ops) = 
  ["inputs:"]
  ++ (map ((\s => "  \{s}") . show) inputs)
  ++ ["outputs:"]
  ++ (map ((\s => "  \{s}") . show) outputs)
  ++ ["states:"]
  ++ (map ((\s => "  \{s}") . show) sts)
  ++ ["ops:"]
  ++ (map ((\s => "  \{s}") . show) ops)

ppFTAC2: FTAC2 -> List String
ppFTAC2 = ppFTAC . toFTAC

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

public export
interface PPrint a where
  pprint: a -> List String
  
export
PPrint TAC where
  pprint = ppTAC

export
PPrint FTAC where
  pprint = ppFTAC
  
export
PPrint FTAC2 where
  pprint = ppFTAC2
