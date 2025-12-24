import SynQ
import System.File

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide Prelude.const

namespace NCO
  export
  NCOStVal: Type
  NCOStVal = BitVec 24
  
  export
  NCOSt: Type
  NCOSt = !* (BitVec 24)
  
  export
  ncoInitSt: NCOSt
  ncoInitSt = MkBang $ BV 0
  
  export
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
         
  %unhide Prelude.(>>=)    
  read: IO (BitVec 24)
  read = do putStr "step: \n"
            fflush stdout
            step <- (pure $ BitVec.fromInteger . cast) <*> getLine
            pure step
            
  %hide Prelude.(>>=) 
  
  ncoFn: BitVec 24 -> LState NCOSt (BitVec 14)
  ncoFn = runSeq $ nco reg
  
  export
  ncoSW: IO ()
  ncoSW = reactMealy read ncoFn ncoInitSt
  
  export
  genVerilog: IO ()
  genVerilog = writeVerilog "nco" $ nco reg
  
  
namespace LUTDecode
  
  idxDecode: (Comb comb, Primitive comb)
       => comb (BitVec 14) (BitVec 12)
  idxDecode = 
    lam $ \idx => 
      let sign2 = slice 12 13 idx
          raw_idx  = slice 0 12 idx
      in mux21 sign2
           (adder' (const $ BV 4095)
                   (adder' (not raw_idx) 
                           (const $ BV 1)))
           raw_idx
           
  lutDecode: (Comb comb, Primitive comb)
       => comb (BitVec 14, BitVec 16) (BitVec 16)
  lutDecode = 
    lam $ \ins => 
      let idx = proj1 ins
          dat = proj2 ins
          sign1 = slice 13 14 idx
      in mux21 sign1 dat
           (adder' (const $ BV 65535)
                   (adder' (not dat) 
                           (const $ BV 1)))
                           
  
  idxDecFn: BitVec 14 -> BitVec 12
  idxDecFn = runComb idxDecode
  
  lutDecFn: (BitVec 14, BitVec 16) -> BitVec 16
  lutDecFn = runComb lutDecode

  %unhide Prelude.(>>=)
  export
  decodeProg: IO ()
  decodeProg = 
    do putStr "index: \n"
       fflush stdout
       index <- (pure $ BitVec.fromInteger . cast) <*> getLine
       let index' = idxDecFn index
       putStr "\{show index'}\n"
       fflush stdout
       rawData <- (pure $ BitVec.fromInteger . cast) <*> getLine
       let dat = lutDecFn (index, rawData)
       putStr "\{show dat}\n"
       fflush stdout
       decodeProg
  
  export
  genVerilog: IO ()
  genVerilog = do writeCombVerilog "idx_decoder"  idxDecode;
                  writeCombVerilog "data_decoder" lutDecode
  
  %hide Prelude.(>>=)  
namespace DFF
  
  export
  DFFStVal: Type
  DFFStVal = (BitVec 1, BitVec 1)
  
  export
  DFFSt: Type
  DFFSt = LPair (!* BitVec 1) (!* BitVec 1)
  
  export
  dffInitSt: DFFSt
  dffInitSt = (MkBang $ BV 0) # (MkBang $ BV 0)
  
  show': DFFSt -> String
  show' = show
  
  export
  Show DFFSt where
    show = show'
  
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
  export
  PFDStVal: Type
  PFDStVal = (BitVec 1, DFFStVal, DFFStVal)
  
  export
  PFDSt: Type
  PFDSt = LPair (!* BitVec 1) $ LPair DFFSt DFFSt
  
  export
  pfdInitSt: PFDSt
  pfdInitSt = (MkBang $ BV 0) # dffInitSt # dffInitSt
  
  
  %ambiguity_depth 6
  export
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
  
  %unhide Prelude.(>>=)      
  read: IO (BitVec 1, BitVec 1)
  read = do putStr "reference signal: \n"
            fflush stdout
            refSig <- (pure $ BitVec.fromInteger . cast) <*> getLine
            putStr "input signal: \n"
            fflush stdout
            inputSig <- (pure $ BitVec.fromInteger . cast) <*> getLine
            pure (refSig, inputSig)
  %hide Prelude.(>>=)
            
  pfdFn: (BitVec 1, BitVec 1) -> LState PFDSt (BitVec 1, BitVec 1)
  pfdFn = runSeq 
        $ abst $ \ins => let x = proj1 ins
                             y = proj2 ins
                         in pfd reg reg reg x y
                         
  [pfdOutShow] Show (BitVec 1, BitVec 1) where
    show (x, y) = "{\"a_ahead_b\": \"\{show x}\", \"b_ahead_a\": \"\{show y}\"}"
    
  show': PFDSt -> String
  show' = show
  
  [pfdStShow] Show PFDSt where
    show = show'
  
  export                      
  pfdProg: IO ()
  pfdProg = reactMealy @{(pfdOutShow, pfdStShow)} read pfdFn pfdInitSt
  
  export
  pfd': (Seq comb seq, Primitive comb) 
    => (1 dffAReg: Reg DFFStVal comb seq)
    -> (1 dffBReg: Reg DFFStVal comb seq)
    -> (1 reg: Reg (BitVec 1) comb seq)
    -> seq PFDSt (BitVec 1, BitVec 1) (BitVec 1, BitVec 1)
  pfd' dffAReg dffBReg reg = abst $ \ins => pfd dffAReg dffBReg reg (proj1 ins) (proj2 ins)
  
  export
  genVerilog: IO ()
  genVerilog = writeVerilog "pfd" $ pfd' reg reg reg
  
namespace ACC
  export
  ACCSt': Type
  ACCSt' = BitVec 32
  
  export
  ACCSt: Type 
  ACCSt = !* BitVec 32
  
  export
  acc: (Seq comb seq, Primitive comb) 
    => (1 reg: Reg ACCSt' comb seq)
    -> (input: comb () (BitVec 1, BitVec 1))
    -> seq ACCSt () (BitVec 32)
  acc (MkReg get set) input = 
    let a2b = proj1 input
        b2a = proj2 input
    in do prev_acc <- get 
          let nxt_acc = mux21 (a2b `xor` b2a) 
                          (mux21 a2b
                             (adder' prev_acc (const $ BV 1))
                             (adder' prev_acc (not $ const $ BV 0)))
                          prev_acc
          _ <- set nxt_acc
          pure $ shiftLL 10 nxt_acc
          
  export
  genVerilog: IO ()
  genVerilog = writeVerilog "acc" $ abst $ \input => acc reg input
  
namespace DIV2
  
  export
  DIV2St': Type
  DIV2St' = (BitVec 1, BitVec 1)
  
  export
  DIV2St: Type
  DIV2St = LPair (!* BitVec 1)  (!* BitVec 1)
  
  export
  div2: (Seq comb seq, Primitive comb)
     => (1 reg: Reg DIV2St' comb seq)
     -> (input: comb () $ BitVec 1)
     -> seq DIV2St () (BitVec 1)
  div2 (MkReg get set) input = 
    do prevInOut <- get
       let prevIn  = proj1 prevInOut
           prevOut = proj2 prevInOut
           rising  = (not prevIn) `and` input
           output  = mux21 rising
                       (not prevOut)
                       prevOut
       _ <- set $ prod input output
       pure output
  
  export
  genVerilog: IO ()
  genVerilog = writeVerilog "div2" $ abst $ \input => div2 reg input
  
PLLSt':Type
PLLSt' = (PFDStVal, (DIV2St', (ACCSt', NCOStVal)))

PLLSt: Type
PLLSt = LPair PFDSt $ LPair DIV2St $ LPair ACCSt NCOSt

pll: (Seq comb seq, Primitive comb)
  => (1 pfdReg : Reg PFDStVal comb seq)
  -> (1 div2Reg: Reg DIV2St'  comb seq)
  -> (1 accReg : Reg ACCSt'   comb seq)
  -> (1 ncoReg : Reg NCOStVal comb seq)
  -> seq PLLSt (BitVec 16, BitVec 16) (BitVec 14)
pll pfdReg div2Reg accReg ncoReg = 
  let 1 pfd = PFD.pfd' pfdReg
  in ?pll_rhs


