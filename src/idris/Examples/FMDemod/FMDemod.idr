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

zip: (Seq comb seq, Primitive comb)
  => {auto _: St s}
  -> comb () (BitVec 1, BitVec 48)
  -> comb () (BitVec 1, BitVec 48)
  -> seq s () (BitVec 1, (BitVec 32, BitVec 32))
zip x y = 
  let d1 = slice 16 48 $ proj2 x
      d2 = slice 16 48 $ proj2 y
      en = proj1 x
  in pure $ prod en $ prod d1 d2
 
pass: (Seq comb seq)
  => {auto _: Sig a}
  -> {auto _: St s}
  -> seq s a a
pass = pure $ lam id

nop: (Seq comb seq)
  => {auto _: St s}
  -> seq s () ()
nop = pure $ unit

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
        (ddcI # ddcQ): LPair _ _ = (ddc' ddcIRegs) # (ddc' ddcQRegs)
--        ddcQ  = ddc' ddcQRegs
        atan2 = cordicAtan2' catan2Regs
        unwrapDiff = unwrapDiff' unwrapDiffRegs
    in do ifI <- pass       <<< pass  <<< pass         <<< ddcI loI dIn 
          ifQ <- pass       <<< pass  <<< ddcQ loQ dIn <<< nop
          res <- unwrapDiff <<< atan2 <<< zip ifI ifQ  <<< nop
          pure res

emitLLVMIR: IO ()
emitLLVMIR = dumpLLVMIR "fm_demod" $ shareExp $ elimDead $ flatTAC $ genTAC (fmDemod ddcRegs ddcRegs catan2Regs unwrapDiffRegs)
