# SynQ
**Syn**chronous System Design with **Q**uantitative Types

```idris
import SynQ
import Data.String
```

<!-- idris
-- %hide Prelude.(>>=)
-- %hide Prelude.pure
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)
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
input: IO UInt8
input = do str <- getLine
           Just x <- pure $ parseInteger {a=Integer} str
             | _ => do putStrLn "{\"warning\": \" Not integer, treat as zero\"}\n" 
                       pure $ BV 0
           pure $ BV $ fromInteger x
           
reactIsIncr: IO ()
reactIsIncr = runReact input (isIncr reg) (MkBang $ BV 0)
```

## Generate HDL
```idris
sample: (Seq comb seq, Primitive comb, 
         Reg a comb seq)
  => {auto aIsSig: Sig a} -> {auto sIsState: St s}
  -> {auto similar: SameShape a s}
  -> seq s a a
sample = abst $ \x => do o <- get
                         _ <- set x
                         pure o
                      
wrapped: (Seq comb seq, Primitive comb, 
          Reg (BitVec 1) comb seq)
  => (1 reg: Reg UInt8 comb seq)
  -> seq (LPair (!* UInt8) (!* BitVec 1)) 
         UInt8 (BitVec 1)
wrapped reg = sample {comb=comb} <<< (isIncr reg)

genHDL: IO ()
genHDL = writeVerilog "demo_sys" (wrapped reg)
```

```bash
λΠ> :exec genHDL
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
