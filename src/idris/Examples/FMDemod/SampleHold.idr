module Examples.FMDemod.SampleHold

import SynQ

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.infixr.(<<<)

private infixl 9 <<<

%ambiguity_depth 8

export
sampleHold: (Seq comb seq, Primitive comb)
  => {stWidth: Nat}
  -> {auto aIsSig: Sig a}
  -> {auto stIsSt: St st}
  -> {auto similar: SameShape a st}
  -> (1 reg: Reg (BitVec stWidth, BitVec 1, a) comb seq)
  -> (sampleAt: comb () (BitVec stWidth))
  -> (en: comb () (BitVec 1))
  -> (dat: comb () a)
  -> seq (LPair (!* BitVec stWidth) $ LPair (!* BitVec 1) st) () (BitVec 1, a)
sampleHold (MkReg get set) sampleAt en dat = 
  do st <- get
     let curSt  = proj1 st
         oValid = proj1 $ proj2 st
         oData  = proj2 $ proj2 st
         nxtSt  = mux21 en (adder' curSt (const $ BV 1)) curSt
         nxtValid = en `and` (curSt `eq` sampleAt)
         nxtData  = if_ nxtValid dat oData
     _ <- set (prod nxtSt $ prod nxtValid nxtData)
     pure $ prod oValid oData
     

