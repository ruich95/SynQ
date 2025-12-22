import SynQ

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)

namespace NCO

  NCOStVal: Type
  NCOStVal = BitVec 24
  
  NCOSt: Type
  NCOSt = !* (BitVec 24)
  
  nco: (Seq comb seq, Primitive comb) 
    => (1 acc: Reg NCOStVal comb seq)
    -> seq NCOSt (BitVec 24) (BitVec 14)
  nco (MkReg get set) = 
    abst $ \step => 
      do acc_val <- get
         let nxt_acc = adder' acc_val step
             output  = slice 10 24 acc_val
         _ <- set nxt_acc
         pure output
         
namespace DFF
  
  export
  DFFStVal: Type
  DFFStVal = (BitVec 1, BitVec 1)
  
  export
  DFFSt: Type
  DFFSt = LPair (!* BitVec 1) (!* BitVec 1)
  
  export
  %hint
  DFFStIsSt: St DFFSt
  DFFStIsSt = LP LV LV
  
  export
  dff: (Seq comb seq, Primitive comb) 
    => (1 reg: Reg DFFStVal comb seq)
    -> (dat: comb () (BitVec 1))
    -> (clr: comb () (BitVec 1))
    -> (clk: comb () (BitVec 1))
    -> seq DFFSt () (BitVec 1)
  dff (MkReg get set) dat clr clk = 
    do st <- get
       let prev_out = proj1 st
           prev_clk = proj2 st
           output   = mux21 clr 
                        (const $ BV 0) 
                        (mux21 ((not prev_clk) `and` clk) 
                           dat prev_out)
           nxt_st = prod output clk
       _ <- set nxt_st
       pure output
       
namespace PFD
  
  PFDStVal: Type
  PFDStVal = (BitVec 1, DFFStVal, DFFStVal)
  
  
  PFDSt: Type
  PFDSt = LPair (!* BitVec 1) $ LPair DFFSt DFFSt
  
  %ambiguity_depth 6
  pfd: (Seq comb seq, Primitive comb) 
    => (1 dffAReg: Reg DFFStVal comb seq)
    -> (1 dffBReg: Reg DFFStVal comb seq)
    -> (1 reg: Reg (BitVec 1) comb seq)
    -> (x: comb () (BitVec 1))
    -> (y: comb () (BitVec 1))
    -> seq PFDSt () (BitVec 1, BitVec 1)
  pfd dffAReg dffBReg (MkReg get set) x y = 
    let 1 dffA = \clr => dff dffAReg (const $ BV 1) clr x
        1 dffB = \clr => dff dffBReg (const $ BV 1) clr y
    in do clr  <- (pure (lam id) <<< pure (lam id)) <<< get
          outA <- (pure (lam id) <<< dffA clr)      <<< pure unit
          outB <- (dffB clr      <<< pure unit)     <<< pure unit
          _    <- (pure unit     <<< pure unit)     <<< set (outA `and` outB)
          pure $ prod outA outB
  
  
                       


