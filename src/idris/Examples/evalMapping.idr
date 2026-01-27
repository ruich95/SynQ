
import Impl.TAC
import Impl.TAC.Analysis.Eval
import System.File
import Language.JSON

readAll': String -> IO String
readAll' prev = 
  do False <- fEOF stdin
       | True => pure prev
     ln <- getLine
     readAll' "\{prev}\{ln}\n"
     
readAll: IO String
readAll = readAll' ""

evalMapping: IO ()
evalMapping = 
  do -- printLn "system:"
     -- fflush stdout
     jStr <- getLine --readAll
     Just tac <- pure $ jStrLoad jStr
      | Nothing => do printLn "Invalid tac:";
                      fflush stdout
                      printLn jStr
                      fflush stdout
     jStr <- getLine
     Just mapping <- pure $ jStr2Mapping jStr
       | Nothing => do printLn "Invalid mapping:";
                       fflush stdout
                       printLn jStr
                       fflush stdout
     True <- pure $ matchedMapping tac mapping
       | _ => do printLn "unmatched mapping!"
                 fflush stdout
     let res = eval $ mapFTAC tac mapping
         res = JObject [("steps", JNumber (cast res.steps)), 
                        ("communications", JNumber (cast res.comms))]
     printLn $ format 0 res
     -- printLn (tac == wsum)
     fflush stdout

