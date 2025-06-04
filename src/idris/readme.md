# SynQ
**Syn**chronous System Design with **Q**uantitative Types

```idris
import SynQ
```

<!-- idris
%hide Prelude.(>>=)
%hide Prelude.pure
%hide Data.Linear.Interface.seq
%hide Data.LState.(>>=)

UInt8: Type
UInt8 = BitVec 8
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
