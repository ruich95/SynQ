# SynQ
SynQ (**Syn**chronous System Design with **Q**uantitative Types) is an embedded domain-specific language (EDSL) for synchronous system design and an Idris2 package.

## Usage

 - Just as an Idris2 package (cf. [the official documentation](https://idris2.readthedocs.io/en/latest/reference/packages.html#using-package-files)).
 - The simulation functionality depends on C functions introduced as FFI, following [this document](https://idris2.readthedocs.io/en/latest/ffi/ffi.html#ffi-example) to compile `src/c/libbv.c` to `libbv.so` and put it in a proper location.
 - The generated Verilog HDL file consists of the top-level module only; components referred to in the file are defined in `src/verilog/components.v`.

## A Crash Course in SynQ

```idris
import SynQ
import Data.String
```

<!-- idris
import Data.List1
%hide Prelude.(>>=)
%hide Prelude.pure
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
%ambiguity_depth 8
-->

```idris
isIncr: (Seq comb seq, Primitive comb)
  => (1 reg: Reg UInt8 comb seq)
  -> seq (!* UInt8) UInt8 (BitVec 1)
isIncr (MkReg get set) = abst $ \xin =>
  do pre <- get
     _   <- set xin
     pure $ ltu pre xin
```

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
%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

minusZero: (n:Nat) -> n = minus n 0
minusZero 0 = Refl
minusZero (S k) = Refl

lutGen': (Comb comb, Primitive comb)
     => (idx_width: Nat)
     -> (data_width: Nat)
     -> (List1 $ BitVec data_width)
     -> (start: comb () $ BitVec idx_width)
     -> comb () (BitVec idx_width) 
     -> comb () (BitVec data_width)
lutGen' idx_width data_width (x ::: []) start idx = const x
lutGen' idx_width data_width (x ::: (y :: xs)) start idx = 
  let next_start = rewrite minusZero idx_width 
                   in slice 0 idx_width $ add start $ const $ 1
  in mux21 (eq start idx) (const x) 
           (lutGen' idx_width data_width (y:::xs) next_start idx)


lutGen: (Comb comb, Primitive comb)
     => {idx_width: Nat}
     -> {data_width: Nat}
     -> (List1 $ BitVec data_width)
     -> comb () (BitVec idx_width) 
     -> comb () (BitVec data_width)
lutGen {idx_width} {data_width} xs idx 
  = lutGen' idx_width data_width xs (const $ 0) idx
  
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
     _ <- set (mux21 (ltu cur_idx $ const $ 32)
                     (slice 0 8 $ add cur_idx $ const $ 1)
                     (const $ 0))
     pure o
-->

## Generate HDL
```idris

sineSigProg: IO ()
sineSigProg = putStrLn $ show $ runMealy (sineSrc reg) (MkBang 0) 
              [(), (), (), (), (), (), (), (), (), (), (), (), (), (), ()]

sample: (Seq comb seq, Reg a comb seq)
  => {auto aIsSig: Sig a} -> {auto sIsState: St s}
  -> {auto similar: SameShape a s}
  -> seq s a a
sample = abst $ \x => 
  do o <- get
     _ <- set x
     pure o

wrapped: (Seq comb seq, Primitive comb, 
          Reg (BitVec 1) comb seq)
  => (1 reg1: Reg UInt8 comb seq)
  -> (1 reg2: Reg UInt8 comb seq)
  -> seq (LPair (LPair (!* UInt8) (!* UInt8)) (!* BitVec 1)) 
         () (BitVec 1)
wrapped reg1 reg2 = sample <<< (isIncr reg2) <<< (sineSrc reg1)

genHDL: IO ()
genHDL = writeVerilog "sine" (sineSrc reg)
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

```idris
test_sys: (Seq comb seq, Primitive comb)
  => (1 reg: Reg UInt8 comb seq)
  -> seq (!* UInt8) (BitVec 1) UInt8
test_sys (MkReg get set) = 
  abst $ \x => do y <- get
                  _ <- set (mux21 (ltu y $ const 32)
                              (slice 0 8 $ add y $ const 1)
                              (const 0))
                  pure y

test': (Comb comb, Primitive comb)
  => comb UInt8 UInt8
test' = 
  lam $ \y => (mux21 (ltu y $ const 32)
                     (slice 0 8 $ add y $ const 1)
                     (const 0))
                                                      
genTest: IO ()
genTest = writeVerilog "test" (test_sys reg)

genTest': IO ()
genTest' = writeCombVerilog "test_c" (test')
```
