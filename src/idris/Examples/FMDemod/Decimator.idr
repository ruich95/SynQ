module Examples.FMDemod.Decimator

import SynQ
import System.File
import Examples.FMDemod.SampleHold
import Impl.TAC

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.infixr.(<<<)


private infixl 9 <<<

%ambiguity_depth 8
     
decimator2': (Seq comb seq, Primitive comb)
  => {dWidth: Nat}
  -> (1 reg: Reg (BitVec 1, BitVec 1, BitVec dWidth) comb seq)
  -> seq (LPair (!* BitVec 1) $ LPair (!* BitVec 1) (!* BitVec dWidth)) 
         (BitVec 1, BitVec dWidth) (BitVec 1, BitVec dWidth)
decimator2' reg = 
  abst $ \ins => sampleHold reg (const $ BV 0) (proj1 ins) (proj2 ins)

export
decimator2: (Seq comb seq, Primitive comb)
  => {dWidth: Nat}
  -> (1 reg: Reg (BitVec 1, BitVec 1, BitVec dWidth) comb seq)
  -> (en: comb () (BitVec 1))
  -> (dat: comb () (BitVec dWidth))
  -> seq (LPair (!* BitVec 1) $ LPair (!* BitVec 1) (!* BitVec dWidth)) 
         () (BitVec 1, BitVec dWidth)
decimator2 reg en dat = (decimator2' reg) =<< (pure $ prod en dat)


export
Decimator128St': Nat -> Type
Decimator128St' w = (BitVec 7, BitVec 1, BitVec w)

export
Decimator128St: Nat -> Type
Decimator128St w = 
  (LPair (!* BitVec 7) $ LPair (!* BitVec 1) (!* BitVec w))
  
export
decimator128Init: (w: Nat) -> Decimator128St w
decimator128Init w = (MkBang $ BV 0) # (MkBang $ BV 0) # (MkBang $ BV 0)

export
decimator128StIsSt: (w: Nat) -> St (Decimator128St w)
decimator128StIsSt w = LP LV (LP LV LV)

decimator128': (Seq comb seq, Primitive comb)
  => {dWidth: Nat}
  -> (1 reg: Reg (Decimator128St' dWidth) comb seq)
  -> seq (Decimator128St dWidth)
         (BitVec 1, BitVec dWidth) 
         (BitVec 1, BitVec dWidth)
decimator128' reg = 
  abst $ \ins => sampleHold reg (const $ BV 0) (proj1 ins) (proj2 ins)

export
decimator128: (Seq comb seq, Primitive comb)
  => {dWidth: Nat}
  -> (1 reg: Reg (Decimator128St' dWidth) comb seq)
  -> (en: comb () (BitVec 1))
  -> (dat: comb () (BitVec dWidth))
  -> seq (Decimator128St dWidth)
         () (BitVec 1, BitVec dWidth)
decimator128 reg en dat = (decimator128' reg) =<< (pure $ prod en dat)

%unhide Prelude.(>>=)
read: IO (BitVec 1, BitVec 48)
read = do putStr "en: \n"
          fflush stdout
          rstStr <- getLine
          let en = (BitVec.fromInteger {n=1} . cast) rstStr
          putStr "data: \n"
          fflush stdout
          x1Str <- getLine
          let dat = (BitVec.fromInteger {n=48} . cast) x1Str
          pure (en, dat)
          
decimator2Prog: IO ()
decimator2Prog = reactMealy read (runSeq $ decimator2' reg) 
                   ((MkBang $ BV 0) # (MkBang $ BV 0) # (MkBang $ BV 0))

emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "decimator2" $ shareExp $ elimDead $ flatTAC $ genTAC (decimator2' {dWidth=48} reg)
