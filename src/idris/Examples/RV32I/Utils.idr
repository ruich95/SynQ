module Examples.RV32I.Utils

import Data.BitVec

import System.File

-- %hide Prelude.fromInteger

export
readIn: IO (BitVec 1, BitVec 32, BitVec 32)
readIn = do putStr "EN: \n"
            fflush stdout
            en <- (pure $ BitVec.fromInteger . cast) <*> getLine
            putStr "Inst: \n"
            fflush stdout
            inst <- (pure $ BitVec.fromInteger . cast) <*> getLine
            putStr "PC: \n"
            fflush stdout
            pc <- (pure $ BitVec.fromInteger . cast) <*> getLine
            pure (en, inst, pc)
