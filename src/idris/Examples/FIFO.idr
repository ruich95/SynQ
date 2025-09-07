import SynQ

import Data.Linear
import Examples.Sel
import System.File
import Data.List

import Impl.TAC

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

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)


mkFIFO: forall s. (Seq comb seq, Primitive comb)
  => {cWidth: _} -> {n: Nat} 
  -> {0 a:_} -> {auto aIsSig: Sig a} 
  -> {auto sIsSt: St s}
  -> {auto similar: SameShape a s}
  -> {auto notEmpty: LTE 1 n}
  -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
  -> LPair
       -- forward path
       -- input: rst_n
       -- output: (validO, dataO)
       ((rst_n : comb () (BitVec 1))
         -> seq (LPair (!* BitVec cWidth) (RepeatSt n s)) () (BitVec 1, a)) 
       -- backward path
       -- input:  dataI, validI, readyI (from the successor stage), rst_n
       -- output: readyO (to previous stage)
       ((dataI: comb () a) 
         -> (validI: comb () (BitVec 1)) 
         -> (rst_n : comb () (BitVec 1)) 
         -> (readyI: comb () (BitVec 1))
         -> seq (LPair (!* BitVec cWidth) (RepeatSt n s)) () (BitVec 1))
mkFIFO {n} {notEmpty} (MkReg get set) =
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
  in (\rst_n => 
        do curSt  <- get
           let curCount = proj1 curSt
               curMemSt = proj2 curSt
           out    <- pure $ sel {prf=notEmpty} 
                                (lower' cWidth $ add curCount (not $ const $ BV 0))
                                curMemSt
           validO <- pure $ (not $ curCount `eq` (const $ BV 0))
           pure $ prod (rst_n `and` validO) out)
   # (\dataI => \validI => \rst_n => \readyI => 
         do curSt <- get
            let curCount = proj1 curSt
                curMemSt = proj2 curSt
                produce  = (not $ curCount `eq` (const $ BV 0)) `and` (readyI)
                nxtCount = mux21 produce 
                                 (lower' cWidth $ add curCount (not $ const $ BV 0))
                                 curCount
                maxCount = const (BV {n=cWidth} (cast n))
                readyO   = (nxtCount `ltu` maxCount)
                en       = readyO `and` validI
                nxtCount = mux21 en
                                 (lower' cWidth $ add nxtCount (const $ BV 1))
                                 nxtCount
            update <- pure $ case n of 
                               0         => unit
                               (S 0)     => dataI
                               (S (S k)) => prod {bIsSig=repeatSig (S k) aIsSig} 
                                                 dataI (dropLast curMemSt)
            _      <- set $ prod (mux21 rst_n nxtCount (const $ BV 0)) 
                                 (if_ en update curMemSt)
            pure (rst_n `and` readyO))

public export
SigTy: (n:Nat) -> Type
SigTy n = (BitVec n, BitVec 1)

public export
StTy: (n:Nat) -> Type
StTy n = (LPair (!* BitVec n) (!* BitVec 1))

fifo4: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 3, Repeat 4 (SigTy 32)) comb seq)
  -> LPair
       -- forward path
       -- input: rst_n
       -- output: (validO, dataO)
       (seq (LPair (!* BitVec 3) (RepeatSt 4 (StTy 32)))
            (BitVec 1) (BitVec 1, SigTy 32)) 
       -- backward path
       -- input:  ((validI, dataI), rst_n, readyI)
       -- output: readyO (to previous stage)
       (seq (LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))) 
            ((BitVec 1, SigTy 32), BitVec 1, BitVec 1) (BitVec 1))
fifo4 reg = 
  let fwd # bwd = mkFIFO {n=4} reg 
  in (abst $ \xin => fwd xin)
   # (abst $ \xin => 
        let validI = proj1 $ proj1 xin
            dataI  = proj2 $ proj1 xin
            rst_n  = proj1 $ proj2 xin
            readyI = proj2 $ proj2 xin
         in bwd dataI validI rst_n readyI)
         
fifo4One: (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 3, Repeat 4 (SigTy 32)) comb seq)
  -> seq (LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))) 
         ((BitVec 1, SigTy 32), BitVec 1, BitVec 1) 
         ((BitVec 1, SigTy 32), BitVec 1)
fifo4One reg = 
  abst $ \xin => 
    let validI = proj1 $ proj1 xin
        dataI  = proj2 $ proj1 xin
        rst_n  = proj1 $ proj2 xin
        readyI = proj2 $ proj2 xin
        fwd # bwd = mkFIFO {n=4} reg 
    in do dataO  <- fwd rst_n 
          readyO <- (bwd dataI validI rst_n readyI)
          pure $ prod dataO readyO

export
fifo4': (Seq comb seq, Primitive comb)
  => (1 reg: Reg (BitVec 3, Repeat 4 (SigTy 32)) comb seq)
  -> seq (LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))) 
         ((BitVec 1, SigTy 32), BitVec 1) 
         ((BitVec 1, SigTy 32), BitVec 1)
fifo4' reg = 
  abst $ \xin => 
    let validI = proj1 $ proj1 xin
        dataI  = proj2 $ proj1 xin
        readyI = proj2 xin
        rst_n = const $ BV {n=1} 1
        fwd # bwd = mkFIFO {n=4} reg 
    in do dataO  <- fwd rst_n 
          readyO <- (bwd dataI validI rst_n readyI)
          pure $ prod dataO readyO

export
iniSt: LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))
iniSt = (MkBang $ BV {n=3} 0) # ((MkBang (BV {n=32} 0) # MkBang (BV {n=1} 0)) # ((MkBang (BV {n=32} 0) # MkBang (BV {n=1} 0)) # ((MkBang (BV {n=32} 0) # MkBang (BV {n=1} 0)) # (MkBang (BV {n=32} 0) # MkBang (BV {n=1} 0)))))

-- repeat: (n: Nat) -> a -> List a
-- repeat 0 x = []
-- repeat (S k) x = x :: repeat k x

-- zipList: List a -> List b -> List (a, b)
-- zipList [] ys = []
-- zipList (x :: xs) [] = []
-- zipList (x :: xs) (y :: ys) = (x, y) :: zipList xs ys

-- mapList: (f: a -> b) -> List a -> List b
-- mapList f [] = []
-- mapList f (x::xs) = (f x) :: (mapList f xs)

-- behaviour: List ((BitVec 1, SigTy 32), BitVec 1) 
--   -> List ((BitVec 1, SigTy 32), BitVec 1)
-- behaviour = snd . ((runMealy $ fifo4' reg) iniSt)

-- squeeze: List (BitVec 1, SigTy 32) -> List (BitVec 1) 
--   -> List (SigTy 32)
-- squeeze [] ys = []
-- squeeze (x :: xs) [] = []
-- squeeze ((valid, dat) :: xs) (ready :: ys) = 
--   if (valid == BV 1) && (ready == BV 1) 
--   then dat :: squeeze xs ys
--   else squeeze xs ys
  
-- data Prefix: List a -> List a -> Type where
--   PrefixBase: Prefix [] _
--   PrefixSucc: Prefix xs ys -> Prefix (x::xs) (x::ys)
  
-- prop: (xs: List ((BitVec 1, SigTy 32), BitVec 1))
--   -> Prefix (squeeze (mapList Builtin.fst $ behaviour xs) (mapList Builtin.snd xs))
--             (squeeze (mapList Builtin.fst xs) (mapList Builtin.snd $ behaviour xs))
-- prop [] = ?rhs_prop1 -- PrefixBase
-- prop (((validI, datI), readyI)::xs) = ?rhs_prop2


-- genHDL: IO ()
-- genHDL = writeVerilog "fifo4" (fifo4One reg)
 
-- progFIFO4: 
--   LPair 
--     ((BitVec 1) 
--       -> LState (LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))) 
--                 (BitVec 1, SigTy 32))
--     (((BitVec 1, SigTy 32), BitVec 1, BitVec 1) 
--       -> LState (LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))) 
--                 (BitVec 1))
-- progFIFO4 = 
--   let fwd # bwd = (fifo4 Eval.SeqPrimitive.reg) 
--   in  (runSeq fwd) # (runSeq bwd)

-- %unhide Prelude.pure
-- %unhide Prelude.(>>=)
-- %ambiguity_depth 5
-- read1: IO (BitVec 1)
-- read1 = do putStr "Reset? (active low): \n"
--            fflush stdout
--            rst_n <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            pure rst_n

-- read2: IO ((BitVec 1, SigTy 32), BitVec 1)
-- read2 = do putStr "Current Input Valid? : \n"
--            fflush stdout
--            validI <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            putStr "Current Input: \n"
--            fflush stdout
--            dataI <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            putStr "Last? : \n"
--            fflush stdout
--            tLast <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            putStr "Next Stg Ready?: \n"
--            fflush stdout
--            readyI <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            pure ((validI, (dataI, tLast)), readyI)
           
-- runFIFO4: (st: LPair (!* BitVec 3) (RepeatSt 4 (StTy 32))) -> IO () 
-- runFIFO4 st = 
--   let fwd # bwd = progFIFO4 
--   in do let (MkBang count # content) = st
--             ((MkBang p1 # MkBang tLast1) 
--               # ((MkBang p2 # MkBang tLast2) 
--               # ((MkBang p3 # MkBang tLast3) 
--               #  (MkBang p4 # MkBang tLast4)))) = content
--         putStrLn "{\"state\": {\"count\": \"\{show count}\", \"content\": [\"\{show p1}\", \"\{show p2}\",\"\{show p3}\",\"\{show p4}\"], \"last\": [\"\{show tLast1}\", \"\{show tLast2}\",\"\{show tLast3}\",\"\{show tLast4}\"]}}"
--         fflush stdout
--         rst_n <- read1 
--         let LST fwd = fwd rst_n
--             (st # (validO, dataO)) = fwd st
--         putStrLn "{\"valid\" : \"\{show validO}\", \"data\"  : \"\{show (fst dataO)}\", \"last\"  : \"\{show (snd dataO)}\"}"
--         fflush stdout
--         ((validI, dataI), readyI) <- read2
--         let LST bwd = bwd ((validI, dataI), rst_n, readyI)
--             (st # readyO) = bwd st
--         putStrLn "{\"ready\" : \"\{show readyO}\"}"
--         fflush stdout
--         runFIFO4 st

-- record 
--   AxiSFIFO {0 s:Type} (n: Nat) (0 a: Type) (cntWidth: Nat) 
--            (0 comb: Type -> Type -> Type)
--            (0 seq: Type -> Type -> Type -> Type) where
--   constructor MkAxiSFIFO
--   1 fifoForward: {auto aIsSig: Sig a} 
--       -> {auto sIsSt: St s}
--       -> {auto similar: SameShape a s}
--       -> (dat: comb () a) 
--       -> (rst_n : comb () (BitVec 1))
--       -> seq (LPair (!* BitVec cntWidth) (RepeatSt n s)) () (BitVec 1, a)
--                                                          -- validO, dataO
           
--   1 fifoBackward: {auto aIsSig: Sig a} 
--       -> {auto sIsSt: St s}
--       -> {auto similar: SameShape a s}
--       -> (dat: comb () a) 
--       -> (validI: comb () (BitVec 1)) 
--       -> (rst_n : comb () (BitVec 1)) 
--       -> (readyI: comb () (BitVec 1))
--       -> seq (LPair (!* BitVec cntWidth) (RepeatSt n s)) () (BitVec 1) -- readyO

-- mkFIFO: (Seq comb seq, Primitive comb)
--   => {cWidth: _} -> {0 s:_} -> {n: Nat} 
--   -> {0 a:_} -> {auto aIsSig: Sig a} 
--   -> {auto sIsSt: St s}
--   -> {auto similar: SameShape a s}
--   -> (1 reg: Reg (BitVec cWidth, Repeat n a) comb seq)
--   -> AxiSFIFO {s=s} n a cWidth comb seq
-- mkFIFO reg = 
--   let (bwd # fwd) = fifo' {n=n} {sIsSt=sIsSt} reg
--   in MkAxiSFIFO fwd bwd


-- fifo4': (Seq comb seq, Primitive comb)
--  => (1 reg: Reg (BitVec 3, Repeat 4 (UInt8, BitVec 1)) comb seq)
--  -> (LPair (seq (LPair (!* BitVec 3) (RepeatSt 4 (LPair (!* UInt8) (!* BitVec 1)))) 
--                 ((UInt8, BitVec 1), BitVec 1)  -- dataI rst_n
--                 (BitVec 1, (UInt8, BitVec 1)))
--            (seq (LPair (!* BitVec 3) (RepeatSt 4 (LPair (!* UInt8) (!* BitVec 1)))) 
--                        ((BitVec 1, (UInt8, BitVec 1)), BitVec 1, BitVec 1) -- validI dataI rst_n readyI
--                        (BitVec 1))) -- readyO
-- fifo4' reg = 
--   let MkAxiSFIFO fwd bwd = mkFIFO {s= (LPair (!* UInt8) (!* BitVec 1))} {a=(UInt8, BitVec 1)} {n=4} reg 
    
--   in (abst $ \xin => fwd (proj1 xin) (proj2 xin)) 
--    # (abst $ \xin  => 
--         let validI = proj1 $ proj1 xin 
--             dataI  = proj2 $ proj1 xin 
--             rst_n  = proj1 $ proj2 xin
--             readyI = proj2 $ proj2 xin
--         in bwd dataI validI rst_n readyI)

-- fifo4: LPair (((UInt8, BitVec 1), BitVec 1) 
--                 -> LState (LPair (!* BitVec 3) (RepeatSt 4 (LPair (!* UInt8) (!* BitVec 1)))) 
--                           (BitVec 1, (UInt8, BitVec 1)))
--              (((BitVec 1, (UInt8, BitVec 1)), BitVec 1, BitVec 1) 
--                 -> LState (LPair (!* BitVec 3) (RepeatSt 4 (LPair (!* UInt8) (!* BitVec 1)))) 
--                           (BitVec 1))
-- fifo4 = let (fwd # bwd) = fifo4' Eval.SeqPrimitive.reg 
--         in (runSeq fwd # runSeq bwd)

-- %unhide Prelude.(>>=)
-- progFIFO4: (ini: LPair (!* BitVec 3) (RepeatSt 4 (LPair (!* UInt8) (!* BitVec 1))))
--         -> (read1: IO ((BitVec 1, (UInt8, BitVec 1)), BitVec 1))    -- validI dataI rst_n
--         -> (read2: IO (BitVec 1)) -- readyI
--         -> IO () 
-- progFIFO4 ini read1 read2 = 
--   let fwd # bwd = fifo4 
--   in do let (MkBang count # content) = ini
--             ((MkBang p1 # MkBang tLast1) 
--               # ((MkBang p2 # MkBang tLast2) 
--               # ((MkBang p3 # MkBang tLast3) 
--               #  (MkBang p4 # MkBang tLast4)))) = content
--         putStrLn "{\"state\": {\"count\": \"\{show count}\", \"content\": [\"\{show p1}\", \"\{show p2}\",\"\{show p3}\",\"\{show p4}\"], \"last\": [\"\{show tLast1}\", \"\{show tLast2}\",\"\{show tLast3}\",\"\{show tLast4}\"]}}"
--         fflush stdout
--         ((validI, dataI), rst_n) <- read1 
--         let LST fwd = fwd (dataI, rst_n)
--             (st # (validO, dataO)) = fwd ini
--         putStrLn "{\"valid\" : \"\{show validO}\", \"data\"  : \"\{show (fst dataO)}\", \"last\"  : \"\{show (snd dataO)}\"}"
--         fflush stdout
--         readyI <- read2
--         let LST bwd = bwd ((validI, dataI), rst_n, readyI)
--             (st # readyO) = bwd st
--         putStrLn "{\"ready\" : \"\{show readyO}\"}"
--         fflush stdout
--         progFIFO4 st read1 read2
        
-- iniSt: LPair (!* BitVec 3) (RepeatSt 4 (LPair (!* UInt8) (!* BitVec 1)))
-- iniSt = (MkBang 0) # ((MkBang 0 # MkBang 0) # ((MkBang 0 # MkBang 0) # ((MkBang 0 # MkBang 0) # (MkBang 0 # MkBang 0))))

-- %unhide Prelude.pure
-- %ambiguity_depth 5
-- read1: IO ((BitVec 1, (UInt8, BitVec 1)), BitVec 1)
-- read1 = do putStr "Current Input Valid? : \n"
--            fflush stdout
--            validI <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            putStr "Current Input: \n"
--            fflush stdout
--            dataI <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            putStr "Last? : \n"
--            fflush stdout
--            tLast <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            putStr "Reset? (active low): \n"
--            fflush stdout
--            rst_n <- (pure $ BitVec.fromInteger . cast) <*> getLine
--            pure ((validI, (dataI, tLast)), rst_n)

-- read2: IO (BitVec 1)
-- read2 = do putStr "Next Stg Ready?: \n"
--            fflush stdout
--            (pure $ BitVec.fromInteger . cast) <*> getLine


