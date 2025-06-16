module Sym.Comb.ElabScripts.RepeatUtil

import Sym.Comb.CombPrimitive
import Sym.Comb.Comb
import Language.Reflection

import Data.Nat
import Data.Vect
import Data.Signal
import Data.BitVec
import Sym.Comb.ElabScripts.Unpack

public export
head: (Comb comb) 
  => {n: Nat} ->  {auto 0 prf: LTE 1 n}
  -> {auto aIsSig: Sig a}
  -> Elab $ comb () (Repeat n a) -> comb () a
head {n = 0} {prf=p} impossible
head {n = (S 0)} = pure id
head {n = (S (S k))} = lambda (comb () $ (a, Repeat (S k) a)) $ \xs => 
  let bIsSig = repeatRestSig (S k) (repeatSig (S $ S k) aIsSig)
  in pure $ proj1 xs

public export
tail: (Comb comb) 
  => {n: Nat}
  -> {auto aIsSig: Sig a}
  -> Elab $ comb () (Repeat (S n) a) -> comb () (Repeat n a)
tail {n = 0} = pure $ const unit
tail {n = 1} = pure $ proj2
tail {n = (S k)} = lambda _ $ \xs => 
  let bIsSig = repeatRestSig (S k) (repeatSig (S $ S k) aIsSig)
  in pure $ proj2 xs
  
public export
nth: (Comb comb) 
  => {m: Nat} -> (n: Nat) -> {auto 0 prf: LTE (S n) m}
  -> {auto aIsSig: Sig a}
  -> Elab $ comb () (Repeat m a) -> comb () a
nth {m = 0} _ {prf=p} impossible
nth {m = (S k)} 0 {prf} = head
nth {m = (S k)} (S n) {prf= LTESucc prf} = lambda _ $ \xs => (nth n) <*> (tail <*> pure xs)

public export
split: (Comb comb) 
  => {m: Nat} -> {n: Nat}
  -> {auto aIsSig: Sig a}
  -> Elab $ comb () (Repeat (m+n) a) -> (comb () (Repeat m a), comb () (Repeat n a))
split {m = 0} = pure $ \xs => (unit, xs)
split {m = (S k)} = lambda _ $ \xs => 
  do x <- head <*> pure xs
     (xs', ys) <- split <*> (tail <*> pure xs)
     pure $ (pack (prod {bIsSig=repeatSig k aIsSig} x xs'), ys)
where
  pack: {k:Nat} 
    -> comb () (a, Repeat k a) 
    -> comb () (Repeat (S k) a) 
  pack {k = 0} x = proj1 x
  pack {k = (S k)} x = x

public export
fromVect: (Comb comb, Primitive comb) 
       => {m:_} -> {auto aIsSig: Sig a}
       -> Vect (S m) (comb () a)
       -> Elab $ comb () $ Repeat (S m) a
fromVect {m=0} (x :: []) = pure x
fromVect {m=S m} (x :: y :: xs) = 
  pure (prod {bIsSig = repeatSig (S m) aIsSig} x) <*> (fromVect (y::xs))
      
public export
unpack: (Comb comb, Primitive comb) 
  => {n: Nat} 
  -> Elab $ comb () (BitVec n)
         -> comb () (Repeat n $ BitVec 1)
unpack {n = 0} = pure $ const unit
unpack {n = (S k)} = lambda _ $ \x => 
  (Unpack.unpack <*> pure x) >>= fromVect

public export
unpackV: (Comb comb, Primitive comb) 
  => {n: Nat} -> {auto aIsSig: Sig a}
  -> Elab $ comb () (Repeat n a) -> Vect n $ comb () a
unpackV {n = 0} = pure $ \_ => []
unpackV {n = (S k)} = lambda _ $ \xs => 
  do x  <- head <*> pure xs 
     [| (x ::) (unpackV <*> (tail <*> pure xs)) |]
