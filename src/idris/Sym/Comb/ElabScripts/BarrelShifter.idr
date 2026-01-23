module Sym.Comb.ElabScripts.BarrelShifter

import Sym.Comb.Comb
import Sym.Comb.CombPrimitive
import Data.BitVec
import Data.Signal

import Language.Reflection
import Data.Vect

import Sym.Comb.ElabScripts.Unpack

public export
data ShiftDir = LL | RL | RA

public export
barrelShifter': (Comb comb, Primitive comb)
  => {dataWidth: Nat}
  -> {shtmtWidth: Nat}
  -> (shifter: Nat 
        -> comb () (BitVec dataWidth) 
        -> comb () (BitVec dataWidth))
  -> (shtExp: Nat)
  -> (idx: Vect shtmtWidth (comb () (BitVec 1)))
  -> Elab ((k: comb (BitVec dataWidth) (BitVec dataWidth))
        -> comb (BitVec dataWidth) (BitVec dataWidth))
barrelShifter' _ shtExp [] = 
  lambda _ $ \k => pure $ lam $ \y => app k y
barrelShifter' shifter 0 (i :: is) = 
  lambda _ $ \k => 
    let r  = barrelShifter' {dataWidth=dataWidth} shifter 1 is
        k' = lam $ \y => mux21 i (shifter 1 y) y
    in r <*> pure k'
barrelShifter' shifter shtExp (i :: is) = 
  lambda _ $ \k => 
    let r  = barrelShifter' {dataWidth=dataWidth} shifter (shtExp + 1) is
        k' = lam $ \y => app k $ mux21 i (shifter (2 `power` shtExp) y) y
    in r <*> pure k'

public export
barrelShifter: (Comb comb, Primitive comb)
  => {dataWidth: Nat}
  -> {shtmtWidth: Nat}
  -> (shiftDir: ShiftDir)
  -> Elab $ comb () (BitVec shtmtWidth) 
         -> comb () (BitVec dataWidth)
         -> comb () (BitVec dataWidth)
barrelShifter shiftDir = 
  let shifter = case shiftDir of
                  LL => shiftLL
                  RL => shiftRL
                  RA => shiftRA
  in lambda _ $ \shtmt => 
       lambda _ $ \x => 
         do shtmt: (Vect shtmtWidth $ comb () (BitVec 1)) 
                 <- Unpack.unpack <*> Prelude.pure shtmt
            shift: (comb (BitVec dataWidth) (BitVec dataWidth)) 
                 <- (barrelShifter' shifter 0 $ reverse shtmt) 
                    <*> Prelude.pure (lam $ \y => y)
            pure $ app shift x
