module Examples.FMDemod.MACC

import SynQ

import Impl.HDL.Module
import Impl.HDL.Port
import Impl.HDL.NetList
import Data.Name
import Data.Value
import Control.Monad.State
import System.File

%hide Data.Linear.Interface.seq
%hide Prelude.const
%hide Prelude.pure
%hide Prelude.concat
%hide Data.LState.infixr.(<<<)

private infixl 9 <<<

interface Mult18 (0 comb: Type -> Type -> Type) where
  mult18: comb () (BitVec 18) -> comb () (BitVec 18)
       -> comb () (BitVec 36)
       
mult18Decl: ModuleDecl (BitVec 18, BitVec 18) (BitVec 36)
mult18Decl = MkModuleDecl 
            "mult18" [] 
            (CP (SP (NM "mult18_in_1") 18 UV) (SP (NM "mult18_in_2") 18 UV)) 
            (SP (NM "mult18_out") 36 UV)
       
Mult18 HDL.NetList.Combinational where
  mult18 x y = 
    MkComb $ do x' <- genComb x
                y' <- genComb y
                ST $ \c => let oP = SP (NM $ show c) 36 UV
                               mult = instinate 
                                        mult18Decl c [] 
                                        (CP x'.oPort y'.oPort) oP
                            in Id (S c, MkCNL (UP UN) oP
                                     (x'.assignedPorts ++ 
                                      y'.assignedPorts)
                                     (x'.instModules ++ 
                                      y'.instModules ++ 
                                     [mult]))
                                     
Mult18 Eval.Eval.Combinational where
  mult18 (MkComb x) (MkComb y) = MkComb $ const $ bvMult18 (x ()) (y ())

%hide Prelude.(>>=)

export
signExt: (Primitive comb)
  => comb () (BitVec 36)
  -> comb () (BitVec 48)
signExt x = let sign = slice 35 36 x
            in mux21 sign 
                 (concat (not $ const $ BV {n=12} 0) x) 
                 (concat (const $ BV {n=12} 0) x)

-- stgIn1: (Seq comb seq)
--      => {auto stIsSt: St st} 
--      -> {auto aIsSig: Sig a} 
--      -> {auto bIsSig: Sig b} 
--      -> {auto similar: SameShape a st} 
--      -> (1 reg: Reg a comb seq)
--      -> (f: comb () a -> comb () b)
--      -> comb () a -> seq st () b
-- stgIn1 (MkReg get set) f x = 
--   do x' <- get
--      _  <- set x
--      pure $ f x'

%ambiguity_depth 8
stgIn2: (Seq comb seq)
     => {auto stIsSt: St st} 
     -> {auto st2IsSt: St st2} 
     -> {auto aIsSig: Sig a} 
     -> {auto bIsSig: Sig b} 
     -> {auto similar: SameShape a st} 
     -> (1 reg: Reg a comb seq)
     -> (1 f: comb () a -> seq st2 () b)
     -> comb () a -> seq (LPair st st2) () b
stgIn2 (MkReg get set) f x = 
  do y <- (abst f)      <<< get
     _ <- pure (lam id) <<< set x
     pure y

acc: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 48) comb seq)
  -> (rst: comb () (BitVec 1))
  -> (x  : comb () (BitVec 36))
  -> seq (!* BitVec 48) () (BitVec 48)
acc (MkReg get set) rst x = 
  do x' <- get 
     _  <- set $ mux21 rst 
                       (signExt x) 
                       (adder' x' $ signExt x)
     pure x'

accStg: (Seq comb seq, Primitive comb)
  => (1 regAcc: Reg (BitVec 48) comb seq)
  -> (1 regIn : Reg (BitVec 36) comb seq)
  -> (rst: comb () (BitVec 1))
  -> (x: comb () (BitVec 36))
  -> seq (LPair (!* BitVec 36) (!* BitVec 48)) () (BitVec 48)
accStg regAcc regIn rst = stgIn2 regIn $ acc regAcc rst

multStg: (Seq comb seq, Mult18 comb)
   => (1 reg: Reg (BitVec 18, BitVec 18) comb seq)
   -> (x: comb () (BitVec 18, BitVec 18))
   -> seq (LPair (!* BitVec 18) (!* BitVec 18)) () (BitVec 36)
multStg (MkReg get set) x = 
  do prev <- get
     let x1 = proj1 prev 
         x2 = proj2 prev
     _ <- set x
     pure $ mult18 x1 x2


MACCSt: Type
MACCSt = LPair (LPair (!* BitVec 18) (!* BitVec 18)) (LPair (!* BitVec 36) (!* BitVec 48))

macc: (Seq comb seq, Mult18 comb, Primitive comb)
   => (1 regM: Reg (BitVec 18, BitVec 18) comb seq)
   -> (1 regAcc: Reg (BitVec 48) comb seq)
   -> (1 regIn : Reg (BitVec 36) comb seq)
   -> (rst: comb () (BitVec 1))
   -> (x  : comb () (BitVec 18, BitVec 18))
   -> seq MACCSt () (BitVec 48)
macc regM regAcc regIn rst x = (abst $ accStg regAcc regIn rst) <<< (multStg regM x)

macc': (Seq comb seq, Mult18 comb, Primitive comb)
   => (1 regM: Reg (BitVec 18, BitVec 18) comb seq)
   -> (1 regAcc: Reg (BitVec 48) comb seq)
   -> (1 regIn : Reg (BitVec 36) comb seq)
   -> seq MACCSt (BitVec 1, (BitVec 18, BitVec 18)) (BitVec 48)
macc' regM regAcc regIn = 
  abst $ \x => let rst = proj1 x
                   x   = proj2 x
               in macc regM regAcc regIn rst x

%hide Data.LState.(<*>)
%hide Data.Linear.(<*>)
%hide Data.Linear.(.)
%hide Impl.HDL.NetList.(.)
%hide Data.LState.pure
%hide Sym.Seq.Seq.pure
%hide Data.LState.(>>=)

%unhide Prelude.(>>=)
%unhide Prelude.pure
%hide Sym.Seq.SeqLib.(>>=)

read: IO (BitVec 1, BitVec 18, BitVec 18)
read = do putStr "rst: \n"
          fflush stdout
          rstStr <- getLine
          let rst = (BitVec.fromInteger {n=1} . cast) rstStr
          putStr "x1: \n"
          fflush stdout
          x1Str <- getLine
          let x1 = (BitVec.fromInteger {n=18} . cast) x1Str
          putStr "x2: \n"
          fflush stdout
          x2Str <- getLine
          let x2 = (BitVec.fromInteger {n=18} . cast) x2Str
          pure (rst, x1, x2)
          
maccProg: IO ()
maccProg = reactMealy read (runSeq $ macc' reg reg reg) 
  (((MkBang $ BV 0) # (MkBang $ BV 0)) # ((MkBang $ BV 0) # (MkBang $ BV 0)))

-- genVerilog: IO ()
-- genVerilog = writeVerilog "macc" (abst $ macc reg reg reg)
