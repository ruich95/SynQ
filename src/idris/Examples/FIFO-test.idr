import SynQ
import Examples.FIFO
import System.Random
import Data.List

%hide SeqLib.(>>=)

fifoMealy: List ((BitVec 1, SigTy 32), BitVec 1) 
  -> List ((BitVec 1, SigTy 32), BitVec 1)
fifoMealy = (runMealyIO $ fifo4' {comb = Eval.Combinational} reg) iniSt

rndEvent: IO ((BitVec 1, SigTy 32), BitVec 1) 
rndEvent = 
  do valid <- randomIO {a=Int32} 
     dat   <- randomIO {a=Int32} 
     last  <- randomIO {a=Int32}
     rdy   <- randomIO {a=Int32}
     let valid = BV {n=1}  $ cast  $ valid `mod` 2
         dat   = BV {n=32} $ cast  $ dat
         last  = BV {n=1}  $ cast  $ last `mod` 2
         rdy   = BV {n=1}  $ cast  $ rdy `mod` 2
     pure $ ((valid, (dat, last)), rdy)

rndSeq: Nat -> IO $ List ((BitVec 1, SigTy 32), BitVec 1) 
rndSeq 0 = pure []
rndSeq (S k) = 
  do hd <- rndEvent
     tl <- rndSeq k
     pure $ hd :: tl
     
squeeze: List ((BitVec 1, SigTy 32), BitVec 1) -> List ((BitVec 1, SigTy 32), BitVec 1) 
squeeze = filter $ \x => ((fst $ fst x) == BV 1) && (snd x == BV 1) 

private infix 9 <:
      
(<:): Eq a => List a -> List a -> Bool
(<:) [] _ = True
(<:) (x :: xs) [] = False
(<:) (x :: xs) (y :: ys) = 
  if x == y then xs <: ys
  else False



fifoProp: List ((BitVec 1, SigTy 32), BitVec 1) -> Bool
fifoProp input = 
  let (dataIn , ackIn)  = unzip input
      (dataOut, ackOut) = unzip $ fifoMealy input
  in (squeeze $ dataOut `zip` ackIn) <: (squeeze $ dataIn `zip` ackOut)
  
test1: Nat -> IO $ Either () $ List ((BitVec 1, SigTy 32), BitVec 1)
test1 k = 
  do sample <- rndSeq k 
     if fifoProp sample then pure $ Left () else pure $ Right sample
     
test: Nat -> IO ()
test 0 = printLn "Success"
test (S k) = 
  do len <- randomRIO {a=Int32} (20, 100) 
     let len: Nat = cast len 
     Left _ <- test1 len 
     | Right sample => printLn "fail on sample: \{show sample}"
     test k

