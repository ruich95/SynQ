import Language.Reflection

import Sym.Comb
import Sym.CombPrimitive
import Sym.CombLib

import Impl.Compile
import Impl.Eval

import Data.Bits
import Data.BitVec

%language ElabReflection

fn: {comb:_} -> (Comb comb, Primitive comb)
   => comb (BitVec 1, BitVec 8, BitVec 8) (BitVec 8)
fn = lam $ \x => (mux21 (proj1 x) (proj1 $ proj2 x) (proj2 $ proj2 x))

-- fn in env with partial knowledge
fn': {comb:_} -> (Comb comb, Primitive comb)
   => comb (BitVec 8, BitVec 8) (BitVec 8)
fn' = (lam $ \x => app fn (prod (const 1) x))


term1: (BitVec 8, BitVec 8) -> (BitVec 8)
term1 = %runElab (genComb fn')

term2: (BitVec 8, BitVec 8) -> (BitVec 8)
term2 = runComb fn'

{-
- + "Main.prop1" [P]
 `-- (z : (BitVec 8, BitVec 8)) -> fst z = fst z
-}
prop1: (z: (BitVec 8, BitVec 8)) -> term1 z = fst z

{-
- + "Main.prop2" [P]
 `-- (z : (BitVec 8, BitVec 8)) -> (if 1 == 1 then MkComb (\x => fst z) else MkComb (\x => snd z)) .runComb () = fst z
-}
prop2: (z: (BitVec 8, BitVec 8)) -> term2 z = fst z
