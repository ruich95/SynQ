import SynQ

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide LState.(>>=)
%hide Prelude.(=<<)
%hide Prelude.pure

public export
RepeatSt: Nat -> (s: Type) -> Type
RepeatSt 0 s = ()
RepeatSt (S 0) s = s
RepeatSt (S (S k)) s = LPair s (RepeatSt (S k) s)

%hint
repeatStIsSt: {auto sIsSt: St s} -> {n: Nat} -> St (RepeatSt n s)
repeatStIsSt {n = 0} = LU
repeatStIsSt {n = (S 0)} = sIsSt
repeatStIsSt {n = (S (S k))} = LP sIsSt repeatStIsSt

%hint
sameShape: {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s} 
  -> {auto similar: SameShape a s}
  -> {n: Nat} -> SameShape (Repeat n a) (RepeatSt n s)
sameShape {n = 0} = U
sameShape {n = (S 0)} = similar
sameShape {n = (S (S k))} = P similar (sameShape {n=(S k)})
  
dropLast: (Comb comb, Primitive comb)
  => {auto aIsSig: Sig a} 
  -> {n: _}
  -> comb () (Repeat (S n) a)
  -> comb () (Repeat n a)
dropLast {n = 0} x = unit
dropLast {n = (S 0)} x = proj1 x
dropLast {n = (S (S k))} x = 
  let _ = repeatSig (S k) aIsSig
  in prod (proj1 x) (dropLast $ proj2 x)

movingWindow: (Seq comb seq, Primitive comb)
  => {auto aIsSig: Sig a}
  -> {auto sIsSt : St s}
  -> {auto similar: SameShape a s}
  -> (n: Nat)
  -> (init: comb () (Repeat (S n) a))
  -> (1 reg: Reg (Repeat (S n) a) comb seq)
  -> LC (comb () (BitVec 1) -> comb () (BitVec 1) 
           -> comb () a -> seq (RepeatSt (S n) s) () ())
        (seq (RepeatSt (S n) s) () (Repeat (S n) a))
movingWindow 0     init (MkReg get set) = (\rst, skip => set) # get
movingWindow (S k) init (MkReg get set) = 
  let prf1 = repeatStIsSt {sIsSt = sIsSt} {n=S $ S k}
      prf3 = sameShape {similar=similar} {n=S $ S k}
      prf2 = repeatSig (S k) aIsSig
  in (\rst, skip, xin => 
         do cur  <- get {similar=prf3}
            let tail = dropLast {n=S k} cur
                nxt  = if_ rst init $ if_ skip cur (prod xin tail)
            set nxt)
   # get {similar=prf3}
             
init0: (Comb comb, Primitive comb)
  => (n: Nat) 
  -> comb () (Repeat n UInt8)
init0 0     = unit
init0 (S 0) = const $ BV 0
init0 (S (S k)) = 
  let prf1 = repeatSig (S k) $ BV {n=8} 
  in prod (const $ BV 0) $ init0 (S k)
  
test: (Seq comb seq, Primitive comb)
  => {n: Nat}
  -> (1 reg: Reg (Repeat (S n) UInt8) comb seq)
  -> seq (RepeatSt (S n) (!* UInt8)) 
         UInt8
         (Repeat (S n) UInt8)
test reg = 
  let mvset # mvget = movingWindow {s= !* UInt8} n (init0 (S n)) reg
      prf1 = repeatSig (S n) $ BV {n=8}
      prf2 = repeatStIsSt {sIsSt=LV {n=8}} {n=S n}
  in abst $ \xin => 
       let rst  = const $ BV {n=1} 0
           skip = const $ BV {n=1} 0
       in do o <- mvget 
             _ <- mvset rst skip xin
             pure o

sys: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (Repeat 4 UInt8) comb seq)
  -> seq (RepeatSt 4 (!* UInt8)) 
         UInt8 (Repeat 4 UInt8)
sys reg = test {n=3} reg

initSt0: (n: Nat) -> (RepeatSt n $ !* UInt8)
initSt0 0     = ()
initSt0 (S 0) = MkBang (BV 0)
initSt0 (S (S k)) = (MkBang $ BV 0) # initSt0 (S k)

sysSoft: List UInt8 -> List $ Repeat 4 UInt8
sysSoft = runMealyIO (sys Eval.SeqPrimitive.reg) (initSt0 4)



