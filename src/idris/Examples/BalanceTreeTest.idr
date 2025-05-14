import SynQ
import Examples.BalanceTree
import Data.LState2

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

IType: Type
IType = (((BitVec 32, BitVec 32), BitVec 32), ((BitVec 32, ((BitVec 32, BitVec 32), BitVec 32)), BitVec 32))

allShape: All (OfType $ BitVec 32) IType
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
  => (step:Nat) -> comb IType (BitVec 32)
balancedSum step = balancedReduce {max_iter=step} adder {allA=allShape}

IRegType: Type
IRegType = (LPair (LPair (LPair (!* BitVec 32) (!* BitVec 32)) (!* BitVec 32)) (LPair (LPair (!* BitVec 32) (LPair (LPair (!* BitVec 32) (!* BitVec 32)) (!* BitVec 32))) (!* BitVec 32)))

RegType: Type
RegType = LPair IRegType (!* BitVec 32)

Similar: SameShape (IType, BitVec 32) (LPair IRegType (!* BitVec 32))
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
  = abst $ \xin => do x <- (get {aIsSig = P aIsSig bIsSig})
                      _ <- (set (prod xin (app f (proj1 x)))) 
                      pure $ (proj2 x)

dlyio': {comb: _} -> {seq: _}
  -> (Seq comb seq)
  => (1 reg: Reg comb seq)
  -> {auto sIsState: St (LPair si so)} 
  -> {auto aIsSig: Sig a} -> {auto bIsSig: Sig b}
  -> {auto similar: SameShape (a, b) (LPair si so)}
  -> (f: comb a b)
  -> (seq (LPair si so) a b)
dlyio' (MkReg get set) f 
  = abst $ \xin => (abst $ \x => (pure $ (proj2 x)) 
                             =<< ((abst set) =<< (pure $ prod xin (app f (proj1 x))))) 
               =<< (get {aIsSig = P aIsSig bIsSig})                      

btree: {comb: _} -> {seq: _}
  -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) -> (step: Nat) -> seq RegType IType (BitVec 32)
btree reg step = dlyio reg (balancedSum {comb=comb} step)

test: {comb: _} -> {seq: _}
  -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq) 
  -> seq (LPair (LPair (!* BitVec 8) (!* BitVec 8)) (!* BitVec 8)) (BitVec 8, BitVec 8) (BitVec 8)
test reg = dlyio' reg (adder {comb=comb})

%ambiguity_depth 5

readIn: IO (BitVec 8, BitVec 8)
readIn = do str1 <- getLine
            i1 <- Prelude.pure $ BitVec.fromInteger $ cast str1
            str2 <- getLine
            i2 <- Prelude.pure $ BitVec.fromInteger $ cast str2
            Prelude.pure (i1, i2)

main: IO ()
main = reactMealy readIn (runSeq $ test reg) (((MkBang 0) # (MkBang 0)) # (MkBang 0))
