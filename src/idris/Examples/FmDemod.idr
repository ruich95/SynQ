import SynQ
import System.File

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide Prelude.const
%hide Prelude.pure
%hide Prelude.concat
%hide Data.LState.infixr.(<<<)

private infixl 9 <<<

namespace LO
  export
  LOSt': Type
  LOSt' = BitVec 24
  
  export
  LOSt: Type
  LOSt = !* (BitVec 24)
  
  export
  %hint
  loStIsSt: St LOSt
  loStIsSt = LV
  
  export
  loInitSt: LOSt
  loInitSt = MkBang $ BV 0
  
  export
  lo: (Seq comb seq, Primitive comb) 
   => (1 acc: Reg LOSt' comb seq)
   -> (step: comb () $ BitVec 24)
   -> seq LOSt () (BitVec 1, BitVec 1)
  lo (MkReg get set) step = 
    do acc_val <- get
       let nxt_acc = adder' acc_val step
           lo_i  = not $ slice 23 24 acc_val
           lo_q  = not $ slice 23 24 (adder' acc_val $ shiftLL 22 (const $ BV 1))
       _ <- set nxt_acc
       pure $ prod lo_i lo_q
         
  nco': (Seq comb seq, Primitive comb) 
    => (1 acc: Reg LOSt' comb seq)
    -> seq LOSt (BitVec 24) (BitVec 1, BitVec 1)       
  nco' reg = abst $ \xin => lo reg xin
  
namespace Util
  export
  mixer: (Comb comb, Primitive comb)
    => (lo_iq: comb () (BitVec 1, BitVec 1))
    -> (signal: comb () (BitVec 16))
    -> comb () (BitVec 16, BitVec 16)
  mixer lo_iq signal = 
    let lo_i = proj1 lo_iq 
        lo_q = proj2 lo_iq
    in prod (mux21 lo_i signal (const $ BV 0)) 
            (mux21 lo_q signal (const $ BV 0))
            
  export
  toComplement: (Comb comb, Primitive comb)
    => (signal: comb () (BitVec 16))
    -> comb () (BitVec 16)
  toComplement signal = adder' signal $ shiftLL 15 (const $ BV  1)
  
  export
  genVerilog: IO ()
  genVerilog = writeCombVerilog "to_complement" 
             $ lam $ \x => toComplement x
  
  export
  neg: {auto n: _} -> (Primitive comb)
    => comb () (BitVec n)
    -> comb () (BitVec n)
  neg x = adder' (not x) (const $ BV 1)
  
  prf1: (x: Nat) -> LTE x x
  prf1 0 = LTEZero
  prf1 (S k) = LTESucc $ prf1 k
  
  prf2: (x: Nat) -> LTE x (S x)
  prf2 0 = LTEZero
  prf2 (S k) = LTESucc $ prf2 k
  
  prf3: (x: Nat) -> 1 = minus (S x) x
  prf3 0 = Refl
  prf3 (S k) = prf3 k
  
  export
  signExt: (Primitive comb)
    => {auto m:_} -> {auto n:_} 
    -> {auto prf: LT m n}
    -> comb () (BitVec m)
    -> comb () (BitVec n)
  signExt {m = 0} x = const $ BV 0
  signExt {m = (S k)} x = 
    let sign = rewrite prf3 k in slice {prf_upper = prf1 (S k)} {prf_lower = prf2 k}  k (S k) x
        nbits = minus n (S k)
        signs: comb () (BitVec nbits) = 
          mux21 sign 
            (not $ const $ BV {n=nbits} 0)
            (const $ BV {n=nbits} 0)
        extended: comb () (BitVec $ nbits + (S k))
          = concat signs x
        prf: n === (nbits + (S k)) = believe_me ()
    in rewrite prf in extended
  
namespace CIC3D16
  -- CIC, 3 stages, 16 times down converter
  -- export 
  -- INT3St': Type
  -- INT3St' = (BitVec 28, (BitVec 28, BitVec 28))
  
  -- export
  -- INT3St: Type   
  -- INT3St = LPair (!* BitVec 28) $ LPair (!* BitVec 28) (!* BitVec 28)
  
  -- export
  -- %hint
  -- int3StIsSt: St INT3St
  -- int3StIsSt = LP LV (LP LV LV)
  
  
  -- int3: (Seq comb seq, Primitive comb)
  --   => (1 reg: Reg INT3St' comb seq)
  --   -> (xin: comb () (BitVec 28))
  --   -> seq INT3St () (BitVec 28)
  -- int3 (MkReg get set) xin = 
  --   do prev <- get
  --      let prev1 = proj1 prev
  --          out1  = adder' xin prev1
  --          prev2 = proj1 $ proj2 prev
  --          out2  = adder' out1 prev2
  --          prev3 = proj2 $ proj2 prev
  --          out3  = adder' out2 prev3
  --          nxt_st = prod out1 $ prod out2 out3
  --      _ <- set nxt_st
  --      pure out3
  
  -- export 
  -- COMB3St': Type
  -- COMB3St' = (BitVec 28, (BitVec 28, BitVec 28))
  
  -- export
  -- COMB3St: Type   
  -- COMB3St = LPair (!* BitVec 28) $ LPair (!* BitVec 28) (!* BitVec 28)
  
  -- export
  -- %hint
  -- comb3StIsSt: St INT3St
  -- comb3StIsSt = LP LV (LP LV LV)
  
  -- comb3: (Seq comb seq, Primitive comb)
  --   => (1 reg: Reg COMB3St' comb seq)
  --   -> (xin: comb () (BitVec 28))
  --   -> (en:  comb () (BitVec 1))
  --   -> seq COMB3St () (BitVec 28)
  -- comb3 (MkReg get set) xin en = 
  --   do prev <- get
  --      let prev1 = proj1 prev
  --          out1  = adder' xin (neg {n=28} prev1)
  --          prev2 = proj1 $ proj2 prev
  --          out2  = adder' out1 (neg {n=28} prev2)
  --          prev3 = proj2 $ proj2 prev
  --          out3  = adder' out2 (neg {n=28} prev3)
  --          nxt1 = mux21 en xin prev1
  --          nxt2 = mux21 en out1 prev2
  --          nxt3 = mux21 en out2 prev3
  --          nxt_st = prod nxt1 $ prod nxt2 nxt3
  --      _ <- set nxt_st
  --      pure out3
  
  -- export     
  -- CICDSt': Type
  -- CICDSt' = (BitVec 4, INT3St', COMB3St')
  
  -- export
  -- CICDSt: Type
  -- CICDSt = LPair (!* BitVec 4) $ LPair INT3St COMB3St
  
  -- export
  -- %hint
  -- cicDStIsSt: St CICDSt
  -- cicDStIsSt = LP LV $ LP int3StIsSt comb3StIsSt
  
  
  -- %ambiguity_depth 8
  
  -- export
  -- cic3D16: (Seq comb seq, Primitive comb)
  --   => (1 int3Reg: Reg INT3St' comb seq)
  --   -> (1 comb3Reg: Reg COMB3St' comb seq)
  --   -> (1 reg: Reg (BitVec 4) comb seq)
  --   -> (xin: comb () (BitVec 16))
  --   -> seq CICDSt () (BitVec 1, BitVec 16)
  -- cic3D16 int3Reg comb3Reg (MkReg get set) xin = 
  --   let 1 int3  = int3 int3Reg 
  --       1 comb3 = comb3 comb3Reg
  --   in do sampleSt <- (pure $ lam id) <<< get
  --         let en = eq sampleSt (const $ BV 0)
  --             nxtSampleSt = adder' sampleSt (const $ BV 1)
  --         res <- (abst $ \x => comb3 x en) 
  --                  <<< (int3 $ signExt xin) 
  --                  <<< (set nxtSampleSt)
  --         pure $ prod en (slice 0 16 (shiftRA 12 res))
  
  -- cic3D16': (Seq comb seq, Primitive comb)
  --   => (1 int3Reg: Reg INT3St' comb seq)
  --   -> (1 comb3Reg: Reg COMB3St' comb seq)
  --   -> (1 reg: Reg (BitVec 4) comb seq)
  --   -> seq CICDSt (BitVec 16) (BitVec 1, BitVec 16)
  -- cic3D16' int3Reg comb3Reg reg = abst $ cic3D16 int3Reg comb3Reg reg

  -- export
  -- genVerilog: IO ()
  -- genVerilog = writeVerilog "cic3d16" $ cic3D16' reg reg reg
  
namespace CIC3U16
  
  export
  regWidth: Nat
  regWidth = 28
  
  export 
  INT3USt': Type
  INT3USt' = (BitVec 28, (BitVec 28, BitVec 28))
  
  export
  INT3USt: Type   
  INT3USt = LPair (!* BitVec 28) $ LPair (!* BitVec 28) (!* BitVec 28)
  
  export
  %hint
  int3UStIsSt: St INT3USt
  int3UStIsSt = LP LV (LP LV LV)
  
  intStg: (Seq comb seq, Primitive comb)
    => {auto n: Nat}
    -> (1 reg: Reg (BitVec n) comb seq)
    -> (xin: comb () (BitVec n))
    -> seq (!* BitVec n) () (BitVec n)
  intStg (MkReg get set) xin = 
    do st <- get 
       let res = adder' st xin
       _ <- set res
       pure res
  
  export
  Regs: (Nat, Nat, Nat) 
     -> (comb: Type -> Type -> Type)
     -> (seq: Type -> Type -> Type -> Type) 
     -> Type
  Regs (w1, w2, w3) comb seq = 
    LPair (Reg (BitVec w1) comb seq) 
      $ LPair (Reg (BitVec w2) comb seq)
              (Reg (BitVec w3) comb seq)
  
  %ambiguity_depth 8
  int3: (Seq comb seq, Primitive comb)
    => (1 regs: Regs (28, 28, 28) comb seq)
    -> (xin: comb () (BitVec 28))
    -> seq INT3USt () (BitVec 28, BitVec 28, BitVec 28)
  int3 (reg1 # reg2 # reg3) xin = 
    let 1 intStg1 = intStg {n=28} reg1
        1 intStg2 = intStg {n=28} reg2
        1 intStg3 = intStg {n=28} reg3
    in do out1 <- (pure $ lam id) <<< intStg1 xin
          let out1' = out1
          out2 <- (pure $ lam id) <<< intStg2 out1' <<< pure unit
          let out2' = out2
          out3 <- intStg3 out2' <<< (pure unit) <<< (pure unit)
          pure $ prod out1 $ prod out2 out3
        
  export 
  COMB3USt': Type
  COMB3USt' = (BitVec 28, (BitVec 28, BitVec 28))
  
  export
  COMB3USt: Type   
  COMB3USt = LPair (!* BitVec 28) $ LPair (!* BitVec 28) (!* BitVec 28)
  
  export
  %hint
  comb3UStIsSt: St COMB3USt
  comb3UStIsSt = LP LV (LP LV LV)
  
  combStg: (Seq comb seq, Primitive comb)
    => {auto n: Nat}
    -> (1 reg: Reg (BitVec n) comb seq)
    -> (xin: comb () (BitVec n))
    -> (valid: comb () (BitVec 1))
    -> seq (!* BitVec n) () (BitVec n)
  combStg (MkReg get set) xin valid = 
    do prev <- get 
       _    <- set (mux21 valid xin prev)
       pure $ adder' xin (neg {n=n} prev)
  
  comb3: (Seq comb seq, Primitive comb)
    => (1 regs: Regs (28, 28, 28) comb seq)
    -> (xin: comb () (BitVec 28))
    -> (valid:  comb () (BitVec 1))
    -> seq COMB3USt () (BitVec 28)
  comb3 (reg1 # reg2 # reg3) xin valid = 
    let combStg1 = combStg {n=28} reg1
        combStg2 = combStg {n=28} reg2
        combStg3 = combStg {n=28} reg3
    in do out1 <- (pure $ lam id) <<< (pure $ lam id) <<< combStg1 xin valid
          (abst $ \x => combStg3 x valid) <<< combStg2 out1 valid <<< pure unit
          
  
  export
  CICUSt: Type
  CICUSt = LPair COMB3USt $ LPair (!* BitVec 28) INT3USt
  
  export
  %hint
  cicUStIsSt: St CICUSt
  cicUStIsSt = LP comb3UStIsSt $ LP LV int3UStIsSt
  
  export
  cic3U16: (Seq comb seq, Primitive comb)
    => (1 int3Regs : Regs (28, 28, 28) comb seq)
    -> (1 comb3Regs: Regs (28, 28, 28) comb seq)
    -> (1 stgReg   : Reg  (BitVec 28)  comb seq)
    -> (xin: comb () (BitVec 1, BitVec 16))
    -> seq CICUSt () (BitVec 28, BitVec 28, BitVec 28, BitVec 28)
  cic3U16 int3Regs comb3Regs (MkReg get set) xin = 
    let 1 int3  = int3 int3Regs 
        1 comb3 = comb3 comb3Regs
        valid   = proj1 xin
        xin     = signExt {m=16} {n=28} $ proj2 xin
    in do comb3Out <- (pure $ lam id) <<< comb3 xin valid
          int3In   <- (pure $ lam id) <<< get <<< pure unit
          let -- upsampling by filling zero
              nxtInt3In = mux21 valid comb3Out (const $ BV 0)
          int3Out <- int3 int3In <<< pure unit <<< pure unit
          _ <- (pure unit) <<< (set nxtInt3In) <<< (pure unit)
          pure $ prod int3In int3Out
          
  
  cic3U16': (Seq comb seq, Primitive comb)
    => (1 int3Regs:  Regs (28, 28, 28) comb seq)
    -> (1 comb3Regs: Regs (28, 28, 28) comb seq)
    -> (1 stgReg   : Reg  (BitVec 28)  comb seq)
    -> seq CICUSt (BitVec 1, BitVec 16) 
                  (BitVec 28, BitVec 28, BitVec 28, BitVec 28)
  cic3U16' int3Regs comb3Regs stgReg = 
    abst $ cic3U16 int3Regs comb3Regs stgReg
    
  export
  genVerilog: IO ()
  genVerilog = writeVerilog "cic3u16" $ cic3U16' (reg # reg # reg) (reg # reg # reg) reg

namespace SH
  
  SHSt': Nat -> Type
  SHSt' n = (BitVec 1, BitVec n)
  
  SHSt: Nat -> Type
  SHSt n = LPair(!* BitVec 1) (!* BitVec n)
  
  sampleHold: (Seq comb seq, Primitive comb)
    => (n: Nat) 
    -> (1 reg: Reg (SHSt' n) comb seq)
    -> (xin: comb () (BitVec 1, BitVec n))
    -> seq (SHSt n) () (BitVec 1, BitVec n)         
  sampleHold n (MkReg get set) xin = 
    let valid = proj1 xin 
        dat   = proj2 xin
    in do prev <- get 
          let nxtDat = mux21 valid dat (proj2 prev)
              nxtValid = valid
          _ <- set (prod nxtValid nxtDat)
          pure prev
          
  sampleHold': (Seq comb seq, Primitive comb)
    => (n: Nat) 
    -> (1 reg: Reg (SHSt' n) comb seq)
    -> seq (SHSt n) (BitVec 1, BitVec n) 
                    (BitVec 1, BitVec n)
  sampleHold' n reg = abst $ sampleHold n reg
  
  export
  genVerilog: IO ()
  genVerilog = writeVerilog "sampleHold" $ sampleHold' 16 reg
  
  
