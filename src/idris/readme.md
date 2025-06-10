# SynQ
SynQ (**Syn**chronous System Design with **Q**uantitative Types) is an embedded domain-specific language (EDSL) for synchronous system design and an Idris2 package.

## Usage

 - Just as an Idris2 package (cf. [the official documentation](https://idris2.readthedocs.io/en/latest/reference/packages.html#using-package-files)).
 - The simulation functionality depends on C functions introduced as FFI, following [this document](https://idris2.readthedocs.io/en/latest/ffi/ffi.html#ffi-example) to compile `src/c/libbv.c` to `libbv.so` and put it in a proper location.
 - The generated Verilog HDL file consists of the top-level module only; components referred to in the file are defined in `src/verilog/components.v`.

## A Crash Course in SynQ

As its name suggests, SynQ is a DSL targeting the design of synchronous systems, which, intuitively, are reactive systems that always produce an event when an event is consumed.

```idris
import SynQ
```

<!-- idris
import Data.String
import Data.List1
import Data.Vect
import Data.Nat

%hide Prelude.(>>=)
%hide Prelude.pure
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%hide Data.LState.(<<<)
%ambiguity_depth 8
-->

<!-- idris 
-- so that tye declaration of isIncr comes later
mutual
-->

```idris

  isIncr (MkReg get set) = abst $ \xin =>
    do pre <- get
       _   <- set xin
       pure $ ltu pre xin
```

```idris
  isIncr: (Seq comb seq, Primitive comb)
    => (1 reg: Reg UInt8 comb seq)
    -> seq (!* UInt8) UInt8 (BitVec 1)
```
<!--
mutual end
-->

## Run as a program
```idris
%unhide Prelude.(>>=)
%unhide Prelude.pure

input: IO UInt8
input = do str <- getLine
           Just x <- pure $ parseInteger {a=Integer} str
             | _ => do putStrLn "{\"warning\": \" Not integer, treat as zero\"}\n" 
                       pure $ BV 0
           pure $ BV $ fromInteger x
           
reactIsIncr: IO ()
reactIsIncr = runReact input (isIncr reg) (MkBang $ BV 0)

%hide Prelude.(>>=)
%hide Prelude.pure

```

<!-- idris

0 lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

-- %hint
lteRefl: {n:Nat} -> LTE n n
lteRefl {n=0} = LTEZero
lteRefl {n=(S k)} = LTESucc (lteRefl)

0 minusZero: (n:Nat) -> n = minus n 0
minusZero 0 = Refl
minusZero (S k) = Refl

0 minusSucc: (n:Nat) -> 1 = minus (S n) n
minusSucc 0 = Refl
minusSucc (S k) = (minusSucc k)

take: (Primitive comb)
  => {n:_} 
  -> (k: Nat) 
  -> {0 prf: LTE (S k) n}
  -> comb () (BitVec n)
  -> comb () (BitVec 1)
take 0 {prf} x = slice 0 1 x
take (S k) {prf} x = 
  rewrite minusSucc k 
  in slice {n=n} {prf_lower=lteSucc $ S k} {prf_upper=prf} (S k) (S $ S k) x

ns: (k: Nat) -> (n: Nat) -> {prf: LTE n k} ->  Vect n (m: Nat ** LTE (S m) k)
ns k 0 {prf} = []
ns k (S m) {prf} = (m ** prf) :: ns k m {prf = lteSuccLeft prf}

unpack': (Primitive comb)
  => {n:_} -> comb () (BitVec n)
  -> Vect k (m: Nat ** LTE (S m) n)
  -> Vect k (comb () $ BitVec 1)
unpack' x [] = []
unpack' x ((i ** prf_i) :: is) = 
  (take i {prf=prf_i} x) :: (unpack' x is)

unpack: {0 comb:_} -> (Primitive comb)
  => {n:_} -> comb () (BitVec n)
  -> Vect n (comb () $ BitVec 1)
unpack x = unpack' x (ns n n {prf=lteRefl})

-- unpack' {n = 0} x = []
-- unpack' {n = (S k)} x = 
--   let b =  slice {prf_upper=lteRefl} {prf_lower=lteSucc k} k (S k) x 
--       bs = slice {prf_upper=lteSucc k} 0 k x
--   in (rewrite minusSucc k in b) :: unpack (rewrite minusZero k in bs)

%unhide Prelude.(>>=)
%unhide Prelude.pure

hds: List1 a -> (n: Nat) -> Maybe $ List1 a
hds (x ::: xs) 0 = Nothing
hds (x ::: xs) (S 0) = Just $ x:::[]
hds (x ::: []) (S (S k)) = Just $ (x ::: [])
hds (x ::: (y :: xs)) (S (S k)) = 
  do tl <- hds (y:::xs) (S k)
     pure $ cons x tl

tls: List1 a -> (n: Nat) -> Maybe $ List a
tls (x ::: xs) 0 = Nothing
tls (x ::: xs) (S 0) = Just xs
tls (x ::: []) (S (S k)) = Just []
tls (x ::: (y :: xs)) (S (S k)) = 
  tls (y:::xs) (S k)

splitAt: List1 a -> (n: Nat) -> Maybe (List1 a, List a)
splitAt xs n = pure MkPair <*> hds xs n <*> tls xs n

%hide Prelude.(>>=)
%hide Prelude.pure

lutGen': (Primitive comb)
     => (idx_width: Nat)
     -> (data_width: Nat)
     -> (List1 $ BitVec data_width)
     -> Vect idx_width (comb () $ BitVec 1)
     -> comb () (BitVec data_width)
lutGen' 0 data_width xs [] = const $ head xs
lutGen' (S 0) data_width xs (i :: []) = 
  case xs of 
    (x ::: []) => const x
    (x1 ::: x2 :: xs) => mux21 i (const x2) (const x1)
lutGen' (S (S k)) data_width xs (i1 :: i2 :: is) = 
  let partLen = (power 2 (S k))
  in -- if length xs <= partLen then lutGen' (S k) data_width xs (i2 :: is)
     -- else 
     case splitAt xs partLen of
       Just (hs, []) => lutGen' (S k) data_width xs (i2 :: is)
       Just (hs, (t::ts)) => 
         mux21 i1 (lutGen' (S k) data_width (t:::ts) (i2 :: is))
                  (lutGen' (S k) data_width hs       (i2 :: is))
       _ => lutGen' (S k) data_width xs (i2 :: is)


lutGen: (Primitive comb)
     => {idx_width: Nat}
     -> {data_width: Nat}
     -> (List1 $ BitVec data_width)
     -> comb () (BitVec idx_width) 
     -> comb () (BitVec data_width)
lutGen {idx_width} {data_width} xs idx 
  = let idx' = unpack idx 
    in lutGen' idx_width data_width xs idx'
  
sine: List1 UInt8
sine = (100) ::: [119, 138, 155, 170, 183, 192, 198, 200, 198, 192, 183, 170,
                  155, 138, 119, 100,  80,  61,  44,  29,  16,   7,   1,   0, 1,
                  7,   16,  29,  44,  61,  80]

sineSig: (Comb comb, Primitive comb)
     => comb () UInt8 -> comb () UInt8
sineSig idx = lutGen sine idx

sineSrc: (Seq comb seq, Primitive comb)
  => (1 reg: Reg UInt8 comb seq)
  -> seq (!* UInt8) () UInt8
sineSrc (MkReg get set) = 
  do cur_idx <- get
     o <- pure $ sineSig cur_idx
     _ <- set (mux21 (ltu cur_idx $ const $ 31)
                     (slice 0 8 $ add cur_idx $ const $ 1)
                     (const $ 0))
     pure o
     
sineSigProg: IO ()
sineSigProg = putStrLn $ show $ runMealy (sineSrc reg) (MkBang 0) 
              [(), (), (), (), (), (), (), (), (), (), () , (), (), (), (), (), (), (), (), ()]
               -- (), (), (), (), (), (), (), (), (), (), (), ()]
              
genSine: IO ()
genSine = writeVerilog "sine" (sineSrc reg)
-->

## Generate HDL
```idris
genDemo: IO ()
genDemo = writeVerilog "demo_sys" (isIncr reg)
```

```bash
λΠ> :exec genHDL
```

## Unrestricted Register Usage

```idris
test: (Seq comb seq, Primitive comb, 
       Reg UInt8 comb seq)
  => seq (!* UInt8) UInt8 UInt8
test = abst $ \x => 
  do o  <- get
     _  <- set (const 42)
     x1 <- get
     x2 <- get
     _  <- set x
     pure x2

testHDL: IO ()
testHDL = writeVerilog "seq_assign" $ test {comb = NetList.Combinational}

```


## Prove Properties
```idris
%default total
isIncrMealy: (st: !* UInt8) 
  -> List UInt8 -> (List $ BitVec 1)
isIncrMealy = runMealyIO (isIncr reg)

isIncrMealyPropP: (st: !* UInt8) 
  -> (xs: List UInt8) -> (x: UInt8) -> (y: UInt8)
  -> (p_ltu: bvLtu x y = BV 1)
  -> (ys: List (BitVec 1) ** (isIncrMealy st (xs ++ [x] ++ [y])) = ys ++ [BV 1])
isIncrMealyPropP (MkBang st) [] x y p_ltu = 
  rewrite p_ltu in ([bvLtu st x] ** Refl)
isIncrMealyPropP (MkBang st) (st' :: xs) x y p_ltu = 
  let (ys ** prf) = isIncrMealyPropP (MkBang st') xs x y p_ltu
  in rewrite prf in (bvLtu st st' :: ys ** Refl)

isIncrMealyPropN: (st: !* UInt8) 
  -> (xs: List UInt8) -> (x: UInt8) -> (y: UInt8)
  -> (p_ltu: bvLtu x y = BV 0)
  -> (ys: List (BitVec 1) ** (isIncrMealy st (xs ++ [x] ++ [y])) = ys ++ [BV 0])
isIncrMealyPropN (MkBang st) [] x y p_ltu = 
  rewrite p_ltu in ([bvLtu st x] ** Refl)
isIncrMealyPropN (MkBang st) (st' :: xs) x y p_ltu = 
  let (ys ** prf) = isIncrMealyPropN (MkBang st') xs x y p_ltu
  in rewrite prf in (bvLtu st st' :: ys ** Refl)
      
```
