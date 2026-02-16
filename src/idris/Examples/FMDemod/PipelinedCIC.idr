module Examples.FMDemod.PipelinedCIC

import SynQ
import System.File
import Data.Vect
import public Examples.FMDemod.Decimator
import Impl.TAC

%hide Prelude.(>>=)
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.infixr.(<<<)


private infixl 9 <<<

%ambiguity_depth 8

public export
CICIntRegs: {nStgs: Nat} 
  -> (dWidth: Vect nStgs Nat) 
  -> (comb: Type -> Type -> Type)
  -> (seq: Type -> Type -> Type -> Type)
  -> Type      
CICIntRegs [] comb seq = ()
CICIntRegs (w :: []) comb seq = (Reg (BitVec w) comb seq)
CICIntRegs (w :: ws@(_ :: _)) comb seq = 
  LPair (Reg (BitVec w) comb seq) (CICIntRegs ws comb seq)

public export
CICCombRegs: {nStgs: Nat} 
  -> (dWidth: Vect nStgs Nat) 
  -> (comb: Type -> Type -> Type)
  -> (seq: Type -> Type -> Type -> Type)
  -> Type      
CICCombRegs [] comb seq = ()
CICCombRegs (w :: []) comb seq = (Reg (BitVec w, BitVec 1, BitVec w) comb seq)
CICCombRegs (w :: ws@(_ :: _)) comb seq = 
  LPair (Reg (BitVec w, BitVec 1, BitVec w) comb seq) (CICCombRegs ws comb seq)

CICIntSt: {nStgs: Nat} 
  -> (dWidth: Vect nStgs Nat) 
  -> Type
CICIntSt [] = ()
CICIntSt (w :: []) = (!* BitVec w)
CICIntSt (w :: ws@(_ :: _)) = 
  LPair (!* BitVec w) (CICIntSt ws)

CICCombSt: {nStgs: Nat} 
  -> (dWidth: Vect nStgs Nat) 
  -> Type
CICCombSt [] = ()
CICCombSt (w :: []) = (LPair (!* BitVec w) (LPair (!* BitVec 1) (!* BitVec w)))
CICCombSt (w :: ws@(_ :: _)) = 
  LPair (LPair (!* BitVec w) (LPair (!* BitVec 1) (!* BitVec w))) (CICCombSt ws)

intStg: (Seq comb seq, Primitive comb)
  => {width: Nat}
  -> (1 reg: Reg (BitVec width) comb seq)
  -> seq (!* BitVec width) (BitVec width) (BitVec width)
intStg (MkReg get set) = 
  abst $ \xin => do acc <- get 
                    let nxt = adder' acc xin
                    _ <- set nxt
                    pure acc

combStg: (Seq comb seq, Primitive comb)
  => {width: Nat}
  -> (1 reg: Reg (BitVec width, BitVec 1, BitVec width) comb seq)
  -> seq (LPair (!* BitVec width) $ LPair (!* BitVec 1) (!* BitVec width))
         (BitVec 1, BitVec width) 
         (BitVec 1, BitVec width)
combStg (MkReg get set) = 
  abst $ \ins => 
    let en  = proj1 ins
        xin = proj2 ins 
    in do st <- get 
          let prev    = proj1 st
              out     = proj2 st
              nxtOut  = adder' xin (adder' (not prev) (const $ BV 1))
              nxtPrev = mux21 en xin prev
          _ <- set $ prod nxtPrev $ prod en nxtOut
          pure $ out

lteSelf: (x:Nat) -> LTE x x
lteSelf 0 = LTEZero
lteSelf (S k) = LTESucc (lteSelf k)

lsbTrunc: (Primitive comb)
  => (width: Nat)
  -> (nDrop: Nat)
  -> {auto prf: LTE nDrop width}
  -> comb () (BitVec width)
  -> comb () (BitVec $ width `minus` nDrop)
lsbTrunc width nDrop x = 
  slice {prf_upper = lteSelf width} nDrop width x

%hide Prelude.pure
cicInt4: (Seq comb seq, Primitive comb)
  => (1 regs: CICIntRegs [44, 37, 31, 26] comb seq)
  -> seq (CICIntSt [44, 37, 31, 26]) (BitVec 44) (BitVec 23)
cicInt4 (r1 # r2 # r3 # r4) = ((pure $ lam $ lsbTrunc 26 3) =<< intStg r4) 
                          <<< ((pure $ lam $ lsbTrunc 31 5) =<< intStg r3) 
                          <<< ((pure $ lam $ lsbTrunc 37 6) =<< intStg r2) 
                          <<< ((pure $ lam $ lsbTrunc 44 7) =<< intStg r1)
                    
cicComb4: (Seq comb seq, Primitive comb)
  => (1 regs: CICCombRegs [23, 22, 21, 20] comb seq)
  -> seq (CICCombSt [23, 22, 21, 20]) 
         (BitVec 1, BitVec 23) 
         (BitVec 1, BitVec 18)
cicComb4 (r1 # r2 # r3 # r4) = 
      ((pure $ lam $ \x => prod (proj1 x) (lsbTrunc 20 2 $ proj2 x)) =<< combStg r4) 
  <<< ((pure $ lam $ \x => prod (proj1 x) (lsbTrunc 21 1 $ proj2 x)) =<< combStg r3) 
  <<< ((pure $ lam $ \x => prod (proj1 x) (lsbTrunc 22 1 $ proj2 x)) =<< combStg r2) 
  <<< ((pure $ lam $ \x => prod (proj1 x) (lsbTrunc 23 1 $ proj2 x)) =<< combStg r1)

export
CIC4d128St: Type
CIC4d128St = 
  LPair (CICIntSt [44, 37, 31, 26]) 
    $ LPair (Decimator128St 23)
            (CICCombSt [23, 22, 21, 20])
      
%hint
export
cic4d128StIsSt: St CIC4d128St
cic4d128StIsSt = LP (LP LV (LP LV (LP LV LV))) 
                    (LP (decimator128StIsSt 23) 
                      $ LP (LP LV (LP LV LV)) 
                           (LP (LP LV (LP LV LV)) 
                               (LP (LP LV (LP LV LV)) 
                                   (LP LV (LP LV LV)))))
%hide Prelude.concat                                   
signExt1644: (Primitive comb)
  => comb () (BitVec 16)
  -> comb () (BitVec 44)
signExt1644 x = 
  let sign = slice 15 16 x
  in mux21 sign 
       (concat (not $ const $ BV {n=28} 0) x)
       (concat (const $ BV {n=28} 0) x)

export
cic4d128': (Seq comb seq, Primitive comb)
  => (1 intRegs : CICIntRegs [44, 37, 31, 26] comb seq)
  -> (1 decReg  : Reg (Decimator128St' 23) comb seq)
  -> (1 combRegs: CICCombRegs [23, 22, 21, 20] comb seq)
  -> seq CIC4d128St (BitVec 16) (BitVec 1, BitVec 18)
cic4d128' intRegs decReg combRegs = 
  let _ = decimator128StIsSt 23
  in (cicComb4 combRegs) 
        <<< (abst $ decimator128 decReg (const $ BV 1)) 
        <<< (cicInt4 intRegs =<< pure (lam signExt1644))

emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "pipe_cic4_d128" $ shareExp $ elimDead $ flatTAC $ genTAC (cic4d128' (reg # reg # reg # reg) reg (reg # reg # reg # reg))

emitVerilog: IO ()
emitVerilog = dumpVerilog "pipe_cic4_d128" $ shareExp $ elimDead $ flatTAC $ genTAC (cic4d128' (reg # reg # reg # reg) reg (reg # reg # reg # reg))
