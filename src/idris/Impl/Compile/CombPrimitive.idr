module Impl.Compile.CombPrimitive

import Sym.Comb.CombPrimitive
import Impl.Compile.Compile
import Language.Reflection
import Data.BitVec
import Data.Bits

%language ElabReflection

public export
Primitive Combinational where
  const x = MkComb $ pure (const x)
  
  add (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvAdd x' y' |] |]
    
  slice lower upper (MkComb x) = 
    let x' = x <*> pure ()
        f = (bvSlice lower upper) 
    in MkComb [| const [| f x' |] |]
  
  ltu (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvLtu x' y' |] |]
    
  eq (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvEq x' y' |] |]
    
  mux21 (MkComb b) (MkComb x) (MkComb y) = 
    MkComb $ do
      b' <- b 
      x' <- x 
      y' <- y 
      pure $ \u => if (b' ()) == (BV {n=1} 1) then (x' ()) else (y' ())
  
  not (MkComb x) = 
    MkComb [| const [| bvNot (x <*> pure ()) |] |]
  
  concat (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvConcat x' y' |] |]
  
  and (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvAnd x' y' |] |]
  
  or (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvOr x' y' |] |]
  
  xor (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvXor x' y' |] |]
  
  lt (MkComb x) (MkComb y) = 
    let x' = x <*> pure ()
        y' = y <*> pure ()
    in MkComb [| const [| bvLt x' y' |] |]
  
  shiftLL sht (MkComb x) = 
    MkComb $ do
      x' <- x
      pure $ const $ bvSll sht (x' ())
  
  shiftRL sht (MkComb x) = 
    let x' = x <*> pure ()
        f = bvSrl sht
    in MkComb [| const [| f x' |] |]
  
  shiftRA sht (MkComb x) = 
    let x' = x <*> pure ()
        f = bvSra sht
    in MkComb [| const [| f x' |] |]
