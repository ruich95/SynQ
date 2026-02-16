module Examples.FMDemod.CIC

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
CICRegs: {nStgs: Nat} 
  -> (dWidth: Vect nStgs Nat) 
  -> (comb: Type -> Type -> Type)
  -> (seq: Type -> Type -> Type -> Type)
  -> Type      
CICRegs [] comb seq = ()
CICRegs (w :: []) comb seq = (Reg (BitVec w) comb seq)
CICRegs (w :: ws@(_ :: _)) comb seq = 
  LPair (Reg (BitVec w) comb seq) (CICRegs ws comb seq)

CICSt: {nStgs: Nat} 
  -> (dWidth: Vect nStgs Nat) 
  -> Type
CICSt [] = ()
CICSt (w :: []) = (!* BitVec w)
CICSt (w :: ws@(_ :: _)) = 
  LPair (!* BitVec w) (CICSt ws)

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
  -> (1 reg: Reg (BitVec width) comb seq)
  -> seq (!* BitVec width) 
         (BitVec 1, BitVec width) 
         (BitVec 1, BitVec width)
combStg (MkReg get set) = 
  abst $ \ins => 
    let en  = proj1 ins
        xin = proj2 ins 
    in do prev <- get 
          let out = adder' xin (adder' (not prev) (const $ BV 1))
          _ <- set $ mux21 en xin prev
          pure $ prod en out
                    
cicInt3: (Seq comb seq, Primitive comb)
  => (1 regs: CICRegs [37, 37, 37] comb seq)
  -> seq (CICSt [37, 37, 37]) (BitVec 37) (BitVec 37)
cicInt3 (r1 # (r2 # r3)) = 
  (intStg r1) <<< (intStg r2) <<< (intStg r3)
                    
cicComb3: (Seq comb seq, Primitive comb)
  => (1 regs: CICRegs [37, 37, 37] comb seq)
  -> seq (CICSt [37, 37, 37]) 
         (BitVec 1, BitVec 37) 
         (BitVec 1, BitVec 37)
cicComb3 (r1 # (r2 # r3)) = 
  (combStg r1) <<< (combStg r2) <<< (combStg r3)
      
CIC3d128St: Type
CIC3d128St = 
  LPair (CICSt [37, 37, 37]) 
    $ LPair (Decimator128St 37)
            (CICSt [37, 37, 37])
  
%hint
cic3d128StIsSt: St CIC3d128St
cic3d128StIsSt = LP (LP LV (LP LV LV)) (LP (decimator128StIsSt 37) (LP LV (LP LV LV)))

%hide Prelude.concat
signExt: (Primitive comb)
  => comb () (BitVec 16)
  -> comb () (BitVec 37)
signExt x = 
  let sign = slice 15 16 x
  in mux21 sign 
       (concat (not $ const $ BV {n=21} 0) x)
       (concat (const $ BV {n=21} 0) x)

cic3d128': (Seq comb seq, Primitive comb)
  => (1 intRegs : CICRegs [37, 37, 37] comb seq)
  -> (1 decReg  : Reg (Decimator128St' 37) comb seq)
  -> (1 combRegs: CICRegs [37, 37, 37] comb seq)
  -> seq CIC3d128St (BitVec 16) (BitVec 1, BitVec 37)
cic3d128' intRegs decReg combRegs = 
  let _ = decimator128StIsSt 37
  in  (cicComb3 combRegs) <<< (abst $ decimator128 decReg (const $ BV 1)) 
         <<< (cicInt3 intRegs =<< pure (lam signExt))

cic3d128: (Seq comb seq, Primitive comb)
  => (1 intRegs : CICRegs [37, 37, 37] comb seq)
  -> (1 decReg  : Reg (Decimator128St' 37) comb seq)
  -> (1 combRegs: CICRegs [37, 37, 37] comb seq)
  -> comb () (BitVec 16)
  -> seq CIC3d128St () (BitVec 1, BitVec 37)
cic3d128 intRegs decReg combRegs x = 
  let _ = decimator128StIsSt 37
  in  (cic3d128' intRegs decReg combRegs) =<< (pure x)

Show (Decimator128St 37) where
  show _ = "decimator state"
  
%unhide Prelude.(>>=)
read: IO (BitVec 16)
read = do putStr "data: \n"
          fflush stdout
          x1Str <- getLine
          let dat = (BitVec.fromInteger {n=16} . cast) x1Str
          pure dat
          
cic3d128Prog: IO ()
cic3d128Prog = reactMealy read 
                 (runSeq $ cic3d128' (reg # reg # reg) reg (reg # reg # reg)) 
                 (((MkBang $ BV 0) # (MkBang $ BV 0) # (MkBang $ BV 0)) 
                 # (decimator128Init 37) 
                 # ((MkBang $ BV 0) # (MkBang $ BV 0) # (MkBang $ BV 0)))
                 
emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "cic3d128" $ shareExp $ elimDead $ flatTAC $ genTAC (cic3d128' (reg # reg # reg) reg (reg # reg # reg))

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
  => (1 regs: CICRegs [44, 37, 31, 26] comb seq)
  -> seq (CICSt [44, 37, 31, 26]) (BitVec 44) (BitVec 23)
cicInt4 (r1 # r2 # r3 # r4) = ((pure $ lam $ lsbTrunc 26 3) =<< intStg r4) 
                          <<< ((pure $ lam $ lsbTrunc 31 5) =<< intStg r3) 
                          <<< ((pure $ lam $ lsbTrunc 37 6) =<< intStg r2) 
                          <<< ((pure $ lam $ lsbTrunc 44 7) =<< intStg r1)
                    
cicComb4: (Seq comb seq, Primitive comb)
  => (1 regs: CICRegs [23, 22, 21, 20] comb seq)
  -> seq (CICSt [23, 22, 21, 20]) 
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
  LPair (CICSt [44, 37, 31, 26]) 
    $ LPair (Decimator128St 23)
            (CICSt [23, 22, 21, 20])
      
%hint
export
cic4d128StIsSt: St CIC4d128St
cic4d128StIsSt = LP (LP LV (LP LV $ LP LV LV)) (LP (decimator128StIsSt 23) (LP LV (LP LV $ LP LV LV)))


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
  => (1 intRegs : CICRegs [44, 37, 31, 26] comb seq)
  -> (1 decReg  : Reg (Decimator128St' 23) comb seq)
  -> (1 combRegs: CICRegs [23, 22, 21, 20] comb seq)
  -> seq CIC4d128St (BitVec 16) (BitVec 1, BitVec 18)
cic4d128' intRegs decReg combRegs = 
  let _ = decimator128StIsSt 23
  in (cicComb4 combRegs) 
        <<< (abst $ decimator128 decReg (const $ BV 1)) 
        <<< (cicInt4 intRegs =<< pure (lam signExt1644))

emitLLVMIR4: IO ()
emitLLVMIR4 = dumpLLVMIR "cic4d128" $ shareExp $ elimDead $ flatTAC $ genTAC (cic4d128' (reg # reg # reg # reg) reg (reg # reg # reg # reg))

-- cic3d128: (Seq comb seq, Primitive comb)
--   => (1 intRegs : CICRegs [37, 37, 37] comb seq)
--   -> (1 decReg  : Reg (Decimator128St' 37) comb seq)
--   -> (1 combRegs: CICRegs [37, 37, 37] comb seq)
--   -> comb () (BitVec 16)
--   -> seq CIC3d128St () (BitVec 1, BitVec 37)
-- cic3d128 intRegs decReg combRegs x = 
--   let _ = decimator128StIsSt 37
--   in  (cic3d128' intRegs decReg combRegs) =<< (pure x)
