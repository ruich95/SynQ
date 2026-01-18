module Examples.FMDemod.FIRInBuffer

import SynQ
import Examples.FMDemod.RAM
import Examples.FMDemod.AddrGen

import System.File

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)

%ambiguity_depth 8

FIRBufferSt: Nat -> Type
FIRBufferSt width = (LPair AddrGenSt (RAMSt 32 width))

firInBuffer: (Seq comb seq, Primitive comb)
  => {width: Nat} 
  -> (1 regRAM: Reg (RAMSt' 32 width) comb seq)
  -> (1 regAddrGen: Reg AddrGenSt' comb seq)
  -> (en: comb () $ BitVec 1)
  -> (dat: comb () $ BitVec width)
  -> seq (FIRBufferSt width)
         ()  (BitVec width)
firInBuffer regRAM regAddrGen en dat = 
  let (ramR # ramW) = ram regRAM
      addrGen = addrGen regAddrGen
      _ = RAMStIsSt {m=32} {n=width}
  in do addr <- (pure $ lam id) <<< addrGen en
        let waddr = proj1 addr
            raddr = proj2 addr
        _ <- ramW en waddr dat <<< pure unit
        (ramR raddr) <<< pure unit

firInBuffer': (BitVec 1, BitVec 18)
  -> LState (FIRBufferSt 18) (BitVec 18)
firInBuffer' = let _ = LP AddrGenStIsSt $ RAMStIsSt {m=32} {n=18}
               in runSeq $ abst $ \xin => firInBuffer reg reg (proj1 xin) (proj2 xin)

initBufferSt: (width: Nat) -> FIRBufferSt width
initBufferSt width = initAddrGenSt # (initRAMSt 32 width (BV 0))

%unhide Prelude.(>>=)
read: IO (BitVec 1, BitVec 18)
read = do putStr "en: \n"
          fflush stdout
          en <- (pure $ BitVec.fromInteger . cast) <*> getLine
          putStr "data: \n"
          fflush stdout
          dat <- (pure $ BitVec.fromInteger . cast) <*> getLine
          pure (en, dat)

Show (FIRBufferSt 18) where
  show (x # y) = "\{show x} ||| \{show' 32 18 y}"

firInBufferProg: IO ()
firInBufferProg = reactMealy read firInBuffer' $ initBufferSt 18
