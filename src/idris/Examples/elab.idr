import SynQ
import Language.Reflection
import Impl.Compile

%hide Data.Linear.Interface.seq
--%hide SeqLib.(>>=)

fn: (reg: Reg (BitVec 8) Compile.Combinational Compile.Sequential) 
 -> Compile.Sequential (!* BitVec 8) (BitVec 8) (BitVec 8)
fn (MkReg get set) = 
  abst {b = BitVec 8} $ \x => 
    do y <- get {s = !* BitVec 8}
       _ <- set {s = !* BitVec 8} x
       pure {b = BitVec 8} y
--                  (\t => set x)
  -- MkSeq $ do set' <- quote (\x => set {s = !* (BitVec 8)} x)
  --            set' <- check set'
  --            lambda _ $ \x => 
  --              let (MkSeq y') : Compile.Sequential (!* (BitVec 8)) () () 
  --                     =  set' $ (Compile.MkComb $ pure $ \_:() => x) 
  --              in y' <*> pure ()

%language ElabReflection

--f': (Seq comb seq) => seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
-- f' = fn $ reg {a=BitVec 8}

test: Elab $ (BitVec 8) -> LState (!* BitVec 8) (BitVec 8)
test = genSeq (fn Compile.SeqPrimitive.reg)

t: (BitVec 8) -> LState (!* BitVec 8) (BitVec 8)
t = %runElab test


-- (\x => set (Seq 
--    (\0 s, 0 b, 0 a, aIsSig, bIsSig, sIsState, 1 arg => let MkBang f = let MkSeq f' = arg sigConstant in MkBang (quote arg >>= (\f => check f)) in MkSeq (lambda a (\x => f >>= (\f => pure (f (MkComb (pure (\_ => x)))) >>= (\_ => let MkSeq y = _ in y <*> (pure (()))))))) 
--    (\0 s, 0 b, 0 a, aIsSig, bIsSig, sIsState, arg => pure arg) 
--    (\0 s, 0 c, 0 b, 0 a, aIsSig, bIsSig, cIsSig, sIsState, 1 arg, 1 arg => arg =<< arg) 
--    (\0 s2, 0 s1, 0 c, 0 b, 0 a, aIsSig, bIsSig, cIsSig, s1IsState, s2IsState, 1 arg, 1 arg => arg <<< arg)) (BitVec 8) x)
