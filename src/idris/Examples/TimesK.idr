module Examples.TimesK

import SynQ
import Data.Vect

%tcinline
div2: Nat -> Nat
div2 0 = 0
div2 1 = 0
div2 (S (S k)) = S $ div2 k

mod2: Nat -> Nat
mod2 (S (S k)) = mod2 k
mod2 k = k

unpack: Nat -> (n: Nat ** Vect n Bool)
unpack 0 = (0 ** [])
unpack k = 
  let (n ** pfx) = unpack $ div2 k
      v = mod2 k == 1
  in ((S n) ** pfx `snoc` v)
  
shtmt: (n: Nat ** Vect n Bool) -> (m:Nat ** (Nat, Vect m Nat))
shtmt (0 ** snd) = (0 ** (0, []))
shtmt ((S k) ** (False :: xs)) = shtmt (k ** xs) 
shtmt ((S k) ** (True  :: xs)) = 
  let (m ** (_, tl)) = shtmt (k ** xs)
  in (S m ** (k, k :: tl))

%hide Prelude.concat

%spec n, m, maxSht, shtmt
shift: (Comb comb, Primitive comb) 
  => {n: _} 
  -> (m: Nat) -> (maxSht: Nat) -> (shtmt: Vect m Nat) 
  -> (x: comb () (BitVec n))
  -> comb () (Repeat m $ BitVec $ S (maxSht+n))
shift 0 _ shtmt x = unit
shift (S 0) maxSht [0] x = 
  concat (const $ BV {n=S maxSht} 0) x
shift (S 0) maxSht [shtmt] x = 
  shiftLL shtmt $ concat (const $ BV {n=S maxSht} 0) x
shift (S (S k)) maxSht (0 :: xs) x     = 
  let prf = repeatSig (S k) (BV {n=(S maxSht)+n})
  in prod (concat (const $ BV {n=S maxSht} 0) x) 
          (shift (S k) maxSht xs x)
shift (S (S k)) maxSht (shtmt :: xs) x = 
  let prf = repeatSig (S k) (BV {n=(S maxSht)+n})
  in prod (shiftLL shtmt $ concat (const $ BV {n=S maxSht} 0) x) 
          (shift (S k) maxSht xs x)

sum: (Comb comb, Primitive comb) 
  => {m: _} -> {n: _} 
  -> comb () (Repeat (S m) $ BitVec n)
  -> comb () (BitVec n)
sum x = 
  let all = repeatImpliesAll {a=BitVec n} m
      sig = repeatSig (S m) $ BV {n=n}
  in (reduce adder) << x
  
timesK': (Comb comb, Primitive comb) 
  => {n: Nat} 
  -> (k: Nat)
  -> (m: Nat ** comb (BitVec n) (BitVec (S $ m+n)))
timesK' k = 
  let (nSht ** (maxSht, shtVec)) = shtmt $ unpack k
  in case nSht of 
       0     => (0 ** lam $ \x => const $ BV 0)
       (S m) => (maxSht ** lam $ \x => TimesK.sum $ shift nSht maxSht shtVec x)

%spec k, maxSht
timesK: (Comb comb, Primitive comb) 
  => {n: Nat} 
  -> (x: comb () $ BitVec n)
  -> (k: Nat)
  -> (maxSht: Nat)
  -> comb () $ BitVec (S $ maxSht+n)
timesK x k maxSht = 
  let (nSht ** (_, shtVec)) = shtmt $ unpack k
      shifted = shift nSht maxSht shtVec x  
  in case nSht of 
       0     => const $ BV 0
       (S m) => TimesK.sum shifted

pointwiseMultK: (Comb comb, Primitive comb) 
  => {n: Nat} -> {m: Nat}
  -> (x: comb () $ Repeat m $ BitVec n)
  -> (k: Vect m Nat)
  -> (maxSht: Nat)
  -> comb () $ Repeat m $ BitVec (S $ maxSht+n)
pointwiseMultK {m=0} x [] maxSht = x
pointwiseMultK {m=S 0} x [k] maxSht 
  = timesK x k maxSht
pointwiseMultK {m=S (S m)} x (k :: ks) maxSht 
  = let prf1 = repeatSig (S m) (BV {n=n}) 
        prf2 = repeatSig (S m) (BV {n=S $ maxSht+n}) 
        z    = timesK (proj1 x) k maxSht
    in prod z $ pointwiseMultK (proj2 x) ks maxSht

public export
dotK: (Comb comb, Primitive comb) 
  => {n: Nat} -> {m: Nat}
  -> (x: comb () $ Repeat (S m) $ BitVec n)
  -> (k: Vect (S m) Nat)
  -> (maxSht: Nat)
  -> comb () $ BitVec (S $ maxSht+n)
dotK x k maxSht = TimesK.sum $ pointwiseMultK x k maxSht

export
%spec k, maxSht
timesKs: (Comb comb, Primitive comb) 
  => {n: Nat} -> {m: Nat}
  -> (x: comb () $ BitVec n)
  -> (k: Vect m Nat)
  -> (maxSht: Nat)
  -> comb () $ Repeat m $ BitVec (S $ maxSht+n)
timesKs x [] maxSht = unit
timesKs {m=1} x (k :: ks) maxSht = timesK x k maxSht
timesKs {m=S $ S m} x (k :: ks) maxSht = 
  let y = timesK x k maxSht
      prf1 = repeatSig (S m) $ BV {n=S $ maxSht+n}
  in prod y (timesKs x ks maxSht)
  
export
%spec k
neg: (Comb comb, Primitive comb) 
  => {n: Nat} -> {m: Nat}
  -> (k: Vect m Bool)
  -> (x: comb () (Repeat m $ BitVec n))
  -> comb () (Repeat m $ BitVec n)
neg {m = 0} [] x = x
neg {m = (S 0)} [y] x = 
  if y then adder' (not x) (const $ BV 1)
       else x
neg {m = (S (S k))} (y :: ys) x = 
  let _ = repeatSig (S k) $ BV {n=n}
      hd = if y then adder' (not $ proj1 x) 
                            (const $ BV 1)
                else proj1 x
      tl = neg ys (proj2 x)
  in prod hd tl


times15: (Comb comb, Primitive comb) 
  => comb UInt8 (BitVec 17)
times15 = 
  lam $ \x => timesK x 15 8
  
test: UInt8 -> BitVec 17
test = runComb times15

test': (m:Nat ** UInt8 -> BitVec (S $ m + 8))
test' = 
  let (m ** sys) = timesK' {comb=Eval.Combinational} {n=8} 15
  in case sys of
          (MkComb fn) => (m ** fn)
