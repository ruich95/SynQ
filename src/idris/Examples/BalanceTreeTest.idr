import SynQ
import Examples.BalanceTree

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

Shape: Type
Shape = (((BitVec 32, BitVec 32), BitVec 32), ((BitVec 32, ((BitVec 32, BitVec 32), BitVec 32)), BitVec 32))

allShape: All (OfType $ BitVec 32) Shape
allShape = AllP (AllP (AllP (AllU Refl) (AllU Refl)) 
                      (AllU Refl)) 
                (AllP (AllP (AllU Refl) 
                            (AllP (AllP (AllU Refl) (AllU Refl)) 
                                  (AllU Refl))) 
                      (AllU Refl))

adder: {comb:_} -> {n:_} 
  -> (Comb comb, Primitive comb)
  => comb (BitVec n, BitVec n) (BitVec n)
adder = lam $ \x => lower' n (add (proj1 x) (proj2 x))

balancedSum: {comb: _} -> (Comb comb, Primitive comb)
  => (step:Nat) 
  -> comb Shape
          (BitVec 32)
balancedSum step = balancedReduce {max_iter=step} adder {allA=allShape}

IRegShape: Type
IRegShape = (LPair (LPair (LPair (!* BitVec 32) (!* BitVec 32)) (!* BitVec 32)) (LPair (LPair (!* BitVec 32) (LPair (LPair (!* BitVec 32) (!* BitVec 32)) (!* BitVec 32))) (!* BitVec 32)))

RegShape: Type
RegShape = LPair IRegShape (!* BitVec 32)

Similar: SameShape (Shape, BitVec 32) (LPair IRegShape (!* BitVec 32))
Similar = P (P (P (P BV BV) BV) (P (P BV (P (P BV BV) BV)) BV)) BV

{- 
    +===+    +----+    +===+ 
 -> |dly| -> | ?f | -> |dly| ->
    +===+    +----+    +===+
-}

dlyio: {comb: _} -> {seq: _}
  -> (Seq comb seq)
  => (1 reg: Reg comb seq)
  -> {auto sIsState: St (LPair si so)} 
  -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
  -> {auto similar: SameShape (a, b) (LPair si so)}
  -> (f: comb a b)
  -> (seq (LPair si so) a b)
dlyio (MkReg get set) f 
  = abst $ \xin => (abst $ \x => (pure $ (proj2 x)) =<< (set (prod xin (app f (proj1 x)))))
                   =<< (get {aIsSig = P aIsSig bIsSig})

dlyio': {comb: _} -> {seq: _}
  -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq)
  -> {auto sIsState: St (LPair si so)} 
  -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
  -> {auto similar: SameShape (a, b) (LPair si so)}
  -> (f: comb a b)
  -> (seq (LPair si so) a b)
dlyio' (MkReg get set) f 
  = abst $ \xin => do x <- (get {aIsSig = P aIsSig bIsSig})
                      _ <- (set (prod xin (app f (proj1 x)))) 
                      pure $ (proj2 x)
