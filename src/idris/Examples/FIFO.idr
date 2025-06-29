import SynQ

import Data.Linear
import Examples.Sel
import System.File

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide LState.(>>=)
%hide Prelude.(=<<)
%hide Prelude.pure

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

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

record 
  AxiSFIFO {0 s:Type} (n: Nat) (0 a: Type) (cntWidth: Nat) 
           (0 comb: Type -> Type -> Type)
           (0 seq: Type -> Type -> Type -> Type) where
  constructor MkAxiSFIFO
  1 fifoForward: {auto aIsSig: Sig a} 
      -> {auto sIsSt: St s}
      -> {auto similar: SameShape a s}
      -> (dat: comb () a) 
      -> (rst_n : comb () (BitVec 1))
      -> seq (LPair (!* BitVec cntWidth) (RepeatSt n s)) () ((BitVec 1, a), BitVec 1) 
                                                         -- (validO, dataO, readyO)
           
  1 fifoBackward: {auto aIsSig: Sig a} 
      -> {auto sIsSt: St s}
      -> {auto similar: SameShape a s}
      -> (dat: comb () a) 
      -> (validI: comb () (BitVec 1)) 
      -> (rst_n : comb () (BitVec 1)) 
      -> (readyI: comb () (BitVec 1))
      -> seq (LPair (!* BitVec cntWidth) (RepeatSt n s)) () ()


fifo': forall s. (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> LPair ((dat: comb () a) 
         -> (validI: comb () (BitVec 1)) 
         -> (rst_n : comb () (BitVec 1)) 
         -> (readyI: comb () (BitVec 1))
         -> seq (LPair (!* BitVec cWidth) (RepeatSt n s)) () ())
        ((dat: comb () a) -> (rst_n : comb () (BitVec 1)) 
         -> seq (LPair (!* BitVec cWidth) (RepeatSt n s)) () ((BitVec 1, a), BitVec 1)) 
                                                           --(validO, dataO, readyO)
fifo' (MkReg get set) = 
  let pSig0: Sig (Repeat n a) = repeatSig n aIsSig
      pSig1: Sig (BitVec cWidth, Repeat n a) = P BV pSig0
      pSt0: St (RepeatSt n s) = repeatStIsSt 
      pSt1: St (LPair (!* BitVec cWidth) (RepeatSt n s)) = LP LV pSt0
      pSame0: SameShape (Repeat n a) (RepeatSt n s)
        = sameShape
      pSame1: SameShape (BitVec cWidth, Repeat n a) 
                        (LPair ((!*) (BitVec cWidth)) 
                        (RepeatSt n s)) 
        = P BV pSame0
  in (\dat => \validI => \rst_n => \readyI => 
         do curSt      <- get
            let curCount = proj1 curSt
                curMemSt = proj2 curSt
                produce  = (not $ curCount `eq` (const $ BV 0)) `and` (readyI)
                nxtCount = mux21 produce 
                                 (lower' cWidth $ add curCount (not $ const $ BV 0))
                                 curCount
                maxCount = const (BV {n=cWidth} (cast n))
                en       = (curCount `ltu` maxCount) `and` validI
                nxtCount = mux21 en
                                 (lower' cWidth $ add nxtCount (const $ BV 1))
                                 curCount       
            update     <- pure $ case n of 
                               0         => unit
                               (S 0)     => dat
                               (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
                                                 dat (dropLast curMemSt)
            set $ prod (mux21 rst_n nxtCount (const $ BV 0)) 
                       (if_ en update curMemSt))
   # (\dat => \rst_n => 
        do curSt      <- get
           let curCount = proj1 curSt
               curMemSt = proj2 curSt
               maxCount = const (BV {n=cWidth} (cast n))
               readyO   = (curCount `ltu` maxCount)
           out        <- pure $ sel (lower' cWidth $ add curCount (not $ const $ BV 0))
                                    curMemSt
                                    dat
           validO     <- pure $ (not $ curCount `eq` (const $ BV 0))
           pure $ prod (prod (rst_n `and` validO) out) (rst_n `and` readyO))

mkFIFO: (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {0 s:_} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> AxiSFIFO {s=s} n a cWidth comb seq
mkFIFO reg = 
  let (bwd # fwd) = fifo' {n=n} {sIsSt=sIsSt} reg
  in MkAxiSFIFO fwd bwd


fifo4': (Seq comb seq, Primitive comb)
 => (1 reg: Reg (BitVec 3, Repeat 4 UInt8) comb seq)
 -> (LPair (seq (LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8))) 
                (UInt8, BitVec 1)  -- dataI rst_n
                ((BitVec 1, UInt8), BitVec 1)) 
           (seq (LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8))) 
                       ((BitVec 1, UInt8), BitVec 1, BitVec 1) -- validI dataI rst_n readyI
                       ()))
fifo4' reg = 
  let MkAxiSFIFO fwd bwd = mkFIFO {s= (!* UInt8)} {a=UInt8} {n=4} reg 
    
  in (abst $ \xin => fwd (proj1 xin) (proj2 xin)) 
   # (abst $ \xin  => 
        let validI = proj1 $ proj1 xin 
            dataI  = proj2 $ proj1 xin 
            rst_n  = proj1 $ proj2 xin
            readyI = proj2 $ proj2 xin
        in bwd dataI validI rst_n readyI)

fifo4: LPair ((UInt8, BitVec 1) 
                -> LState (LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8))) 
                          ((BitVec 1, UInt8), BitVec 1))
             (((BitVec 1, UInt8), BitVec 1, BitVec 1) 
                -> LState (LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8))) 
                          ())
fifo4 = let (fwd # bwd) = fifo4' Eval.SeqPrimitive.reg 
        in (runSeq fwd # runSeq bwd)

%unhide Prelude.(>>=)
progFIFO4: (ini: LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8)))
        -> (read1: IO ((BitVec 1, UInt8), BitVec 1))    -- validI dataI rst_n
        -> (read2: IO (BitVec 1)) -- readyI
        -> IO () 
progFIFO4 ini read1 read2 = 
  let fwd # bwd = fifo4 
  in do let (MkBang count # content) = ini
            (MkBang p1 # (MkBang p2 # (MkBang p3 # MkBang p4))) = content
        putStrLn "{\"state\": {\"count\": \"\{show count}\", \"content\": [\"\{show p1}\", \"\{show p2}\",\"\{show p3}\",\"\{show p4}\"]}}"
        fflush stdout
        ((validI, dataI), rst_n) <- read1 
        let LST fwd = fwd (dataI, rst_n)
            (st # ((validO, dataO), readyO)) = fwd ini
        putStrLn "{\"valid\" : \"\{show validO}\", \"data\"  : \"\{show dataO}\", \"ready\" : \"\{show readyO}\"}"
        fflush stdout
        readyI <- read2
        let LST bwd = bwd ((validI, dataI), rst_n, readyI)
            (st # _) = bwd st
        progFIFO4 st read1 read2
        
iniSt: LPair (!* BitVec 3) (RepeatSt 4 (!* UInt8))
iniSt = (MkBang 0) # (MkBang 0 # (MkBang 0 # (MkBang 0 # MkBang 0)))

%unhide Prelude.pure
%ambiguity_depth 4
read1: IO ((BitVec 1, UInt8), BitVec 1)
read1 = do putStr "Current Input Valid?: \n"
           fflush stdout
           validI <- (pure $ BitVec.fromInteger . cast) <*> getLine
           putStr "Current Input: \n"
           fflush stdout
           dataI <- (pure $ BitVec.fromInteger . cast) <*> getLine
           putStr "Reset? (active low): \n"
           fflush stdout
           rst_n <- (pure $ BitVec.fromInteger . cast) <*> getLine
           pure ((validI, dataI), rst_n)

read2: IO (BitVec 1)
read2 = do putStr "Next Stg Ready?: \n"
           fflush stdout
           (pure $ BitVec.fromInteger . cast) <*> getLine


