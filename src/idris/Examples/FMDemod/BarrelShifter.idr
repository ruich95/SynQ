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

shifterRAStg1: (Comb comb, Primitive comb) 
  => Vect 3 (comb () (BitVec 1)) 
  -> comb ()  (BitVec 32) 
  -> comb ()  (BitVec 32)
shifterRAStg1 [b2, b1, b0] x = 
  mux21 b2 
    (mux21 b1 
      (mux21 b0 
        (shiftRA 7 x)
        (shiftRA 6 x))
      (mux21 b0 
        (shiftRA 5 x)
        (shiftRA 4 x)))
    (mux21 b1 
      (mux21 b0 
        (shiftRA 3 x)
        (shiftRA 2 x))
      (mux21 b0 
        (shiftRA 1 x)
        (shiftRA 0 x)))

shifterRAStg2: (Comb comb, Primitive comb) 
  => Vect 2 (comb () (BitVec 1)) 
  -> comb ()  (BitVec 32) 
  -> comb ()  (BitVec 32)
shifterRAStg2 [b4, b3] x = 
  mux21 b4
    (mux21 b3 
      (shiftRA 24 x)
      (shiftRA 16 x))
    (mux21 b3 
      (shiftRA 8 x)
      (shiftRA 0 x))
      
shifterRA': (Comb comb, Primitive comb) 
  => Vect 5 (comb () (BitVec 1)) 
  -> comb ()  (BitVec 32) 
  -> comb ()  (BitVec 32)
shifterRA' [b4, b3, b2, b1, b0] x = 
  shifterRAStg2 [b4, b3] $ shifterRAStg1 [b2, b1, b0] x
  
export
shifterRA: (Comb comb, Primitive comb) 
  => comb () (BitVec 5)
  -> comb ()  (BitVec 32) 
  -> comb ()  (BitVec 32)  
shifterRA idx x = shifterRA' ((%runElab Unpack.unpack <*> pure idx)) x

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
