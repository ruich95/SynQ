import SynQ
import Language.Reflection
import Impl.Compile

%hide Data.Linear.Interface.seq

fn: (Seq comb seq, Reg (BitVec 8) comb seq, Primitive comb)
  => seq (!* BitVec 8) (BitVec 8) ()
fn = abst {comb=comb} $ \x => set {seq=seq} {comb=comb} x

%language ElabReflection

-- f': (Seq comb seq) => seq (!* (BitVec 8)) (BitVec 8) (BitVec 8)
-- f' = fn $ reg {a=BitVec 8}

test: Elab $ (BitVec 8) -> LState (!* BitVec 8) ()
test = genSeq (fn {comb= Compile.Combinational})

t: (BitVec 8) -> LState (!* BitVec 8) ()
t = %runElab test
