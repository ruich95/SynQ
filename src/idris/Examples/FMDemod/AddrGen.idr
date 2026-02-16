module Examples.FMDemod.AddrGen

import SynQ
import System.File

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.(<<<)
%ambiguity_depth 8

export
AddrGenSt': Type
AddrGenSt' = (BitVec 5, BitVec 5)

export
AddrGenSt: Type
AddrGenSt = LPair (!* BitVec 5) (!* BitVec 5)

export
%hint
AddrGenStIsSt: St AddrGenSt
AddrGenStIsSt = LP LV LV

export
addrGen: (Seq comb seq, Primitive comb)
  => (1 reg: Reg AddrGenSt' comb seq)
  -> (en: comb () $ BitVec 1)
  -> seq AddrGenSt () (BitVec 5, BitVec 5)
addrGen (MkReg get set) en = 
  do st <- get
     let curTail = proj1 st
         curIdx  = mux21 en 
                     (adder' curTail (const $ BV 1)) -- curTail + 1
                     (proj2 st)
         nextTail = mux21 en 
                      (adder' curTail (const $ BV 1))
                      curTail
         nextIdx  = (adder' curIdx (const $ BV 1))
     _ <- set $ prod nextTail nextIdx
     pure $ prod curTail curIdx

export
initAddrGenSt: AddrGenSt
initAddrGenSt = (MkBang 0) # (MkBang 0)

export
show': AddrGenSt -> String
show' = show

addrGen': (BitVec 1)
  -> LState AddrGenSt (BitVec 5, BitVec 5)     
addrGen' = runSeq $ abst $ addrGen reg

%unhide Prelude.(>>=)
read: IO (BitVec 1)
read = do putStr "en: \n"
          fflush stdout
          en <- (pure $ BitVec.fromInteger . cast) <*> getLine
          pure en
          
addrProg: IO ()
addrProg = reactMealy read addrGen' $ (MkBang 0) # (MkBang 0)

export 
Show AddrGenSt where
  show = show'

export
AddrGenSt64': Type
AddrGenSt64' = (BitVec 6, BitVec 6)

export
AddrGenSt64: Type
AddrGenSt64 = LPair (!* BitVec 6) (!* BitVec 6)

export
%hint
AddrGenSt64IsSt: St AddrGenSt64
AddrGenSt64IsSt = LP LV LV

export
addrGen64: (Seq comb seq, Primitive comb)
  => (1 reg: Reg AddrGenSt64' comb seq)
  -> (en: comb () $ BitVec 1)
  -> seq AddrGenSt64 () (BitVec 6, BitVec 6)
addrGen64 (MkReg get set) en = 
  do st <- get
     let curTail = proj1 st
         curIdx  = mux21 en 
                     (adder' curTail (const $ BV 1)) -- curTail + 1
                     (proj2 st)
         nextTail = mux21 en 
                      (adder' curTail (const $ BV 1))
                      curTail
         nextIdx  = (adder' curIdx (const $ BV 1))
     _ <- set $ prod nextTail nextIdx
     pure $ prod curTail curIdx
