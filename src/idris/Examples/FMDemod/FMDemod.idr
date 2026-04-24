module Examples.FMDemod.FMDemod

import SynQ
import Examples.FMDemod.UnwrapDiff
import Examples.FMDemod.DDC
import Examples.FMDemod.CordicAtan2
import Impl.TAC

private infixl 9 <<<

%hide Interface.seq
%hide Data.LState.infixr.(<<<)

FMDemodSt: Type
FMDemodSt = LPair DDCSt $ LPair DDCSt $ LPair CAtan2St UnwrapDiffSt

%hint
FMDemodStIsSt: St FMDemodSt
FMDemodStIsSt = LP DDCStIsSt (LP DDCStIsSt (LP CAtan2StIsSt UnwrapDiffStIsSt))

%ambiguity_depth 8

zip: (Comb comb, Primitive comb)
  => comb () (BitVec 1, BitVec 48)
  -> comb () (BitVec 1, BitVec 48)
  -> comb () (BitVec 1, (BitVec 32, BitVec 32))
zip x y = 
  let d1 = slice 16 48 $ proj2 x
      d2 = slice 16 48 $ proj2 y
      en = proj1 x
  in prod en $ prod d1 d2
 
fmDemod: (Seq comb seq, Primitive comb, Mult18 comb)
      => (1 ddcIRegs      : DDCRegs comb seq)
      -> (1 ddcQRegs      : DDCRegs comb seq)
      -> (1 catan2Regs    : CAtan2Regs comb seq)
      -> (1 unwrapDiffRegs: UnwrapDiffRegs comb seq)
      -> seq FMDemodSt (BitVec 16, BitVec 18, BitVec 18) (BitVec 1, BitVec 32)
fmDemod ddcIRegs ddcQRegs catan2Regs unwrapDiffRegs = 
  abst $ \xin => 
    let dIn   = proj1 xin
        loI   = proj1 $ proj2 xin 
        loQ   = proj2 $ proj2 xin 
        ddcI  = ddc' ddcIRegs
        ddcQ  = ddc' ddcQRegs
        atan2 = cordicAtan2' catan2Regs
        unwrapDiff = unwrapDiff' unwrapDiffRegs
    in do ifI <- (pure $ lam id) <<< (pure $ lam id) <<< (pure $ lam id)      <<< ddcI loI dIn 
          ifQ <- (pure $ lam id) <<< (pure $ lam id) <<<  ddcQ loQ dIn        <<< (pure unit)
          res <- unwrapDiff      <<< atan2           <<< (pure $ zip ifI ifQ) <<< (pure unit)
          pure res

emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "fm_demod" $ shareExp $ elimDead $ flatTAC $ genTAC (fmDemod ddcRegs ddcRegs catan2Regs unwrapDiffRegs)
