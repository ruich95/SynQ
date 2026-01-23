module Examples.FMDemod.BarrelShifter

import SynQ
import Data.Vect
import Language.Reflection
import System.File

%language ElabReflection
%hide Data.Linear.Interface.seq

export
barrelShifterRA32: (Comb comb, Primitive comb) 
  => comb () (BitVec 5) -> comb ()  (BitVec 32) -> comb ()  (BitVec 32)
barrelShifterRA32 = %runElab barrelShifter RA

test: (Seq comb seq, Primitive comb) 
  => seq () (BitVec 5) (BitVec 32)
test = pure $ lam $ \shtmt => barrelShifterRA32 shtmt (const $ BV 0xBAD0BEEF)

testProg': (BitVec 5) -> LState () (BitVec 32)
testProg' = runSeq (test {comb=Eval.Combinational})

read: IO (BitVec 5)
read = do putStr "shtmt: \n"
          fflush stdout
          shtmtStr <- getLine
          let shtmt = (BitVec.fromInteger {n=5} . cast) shtmtStr
          pure shtmt
          
testProg: IO ()
testProg = reactMealy read testProg' () 
