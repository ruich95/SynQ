module Examples.FMDemod.FIRInBuffer

import SynQ
import public Examples.FMDemod.RAM
import public Examples.FMDemod.AddrGen

import System.File

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)

%ambiguity_depth 8

export
FIRBufferSt: Nat -> Type
FIRBufferSt width = (LPair AddrGenSt (RAMSt 32 width))

export
%hint
FIRBufferStIsSt: (w: Nat) -> (St $ FIRBufferSt w)
FIRBufferStIsSt w = LP AddrGenStIsSt (RAMStIsSt {m=32})

public export
InBufRegs: (comb: Type -> Type -> Type) 
        -> (seq: Type -> Type -> Type -> Type) 
        -> Type
InBufRegs comb seq = LPair (Reg (RAMSt' 32 18) comb seq)
                       $ (Reg AddrGenSt' comb seq)

export
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

export
show': (width: Nat) -> FIRBufferSt width -> String
show' width (x # y) = "\{show x} || \{show' 32 width y}"

firInBuffer': (BitVec 1, BitVec 18)
  -> LState (FIRBufferSt 18) (BitVec 18)
firInBuffer' = let _ = LP AddrGenStIsSt $ RAMStIsSt {m=32} {n=18}
               in runSeq $ abst $ \xin => firInBuffer reg reg (proj1 xin) (proj2 xin)

export
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

namespace InBuffer64
  export
  FIRBufferSt64: Nat -> Type
  FIRBufferSt64 width = (LPair AddrGenSt64 (RAMSt 64 width))
  
  export
  %hint
  FIRBufferSt64IsSt: (w: Nat) -> (St $ FIRBufferSt64 w)
  FIRBufferSt64IsSt w = LP AddrGenSt64IsSt (RAMStIsSt {m=64})
  
  public export
  InBuf64Regs: (comb: Type -> Type -> Type) 
          -> (seq: Type -> Type -> Type -> Type) 
          -> Type
  InBuf64Regs comb seq = LPair (Reg (RAMSt' 64 18) comb seq)
                             $ (Reg AddrGenSt64' comb seq)
  
  export
  firInBuffer64: (Seq comb seq, Primitive comb)
    => {width: Nat} 
    -> (1 regRAM: Reg (RAMSt' 64 width) comb seq)
    -> (1 regAddrGen: Reg AddrGenSt64' comb seq)
    -> (en: comb () $ BitVec 1)
    -> (dat: comb () $ BitVec width)
    -> seq (FIRBufferSt64 width)
           ()  (BitVec width)
  firInBuffer64 regRAM regAddrGen en dat = 
    let (ramR # ramW) = ram regRAM
        addrGen = addrGen64 regAddrGen
        _ = RAMStIsSt {m=64} {n=width}
        _ = FIRBufferSt64IsSt width
    in do addr <- (pure $ lam id) <<< addrGen en
          let waddr = proj1 addr
              raddr = proj2 addr
          _ <- ramW en waddr dat <<< pure unit
          (ramR raddr) <<< pure unit
