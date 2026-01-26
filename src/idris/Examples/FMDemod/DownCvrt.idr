import SynQ
import System.File

%hide Data.Linear.Interface.seq
%hide Prelude.(>>=)
%hide Prelude.const
%hide Prelude.pure
%hide Prelude.concat
%hide Data.LState.infixr.(<<<)

private infixl 9 <<<


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
          
downCnvrt: (Seq comb seq, Primitive comb) 
  => (1 loReg: Reg LOSt' comb seq)
  -> seq LOSt (BitVec 24, BitVec 16) (BitVec 16, BitVec 16)
downCnvrt loReg = 
  abst $ \ins => 
    let tw = proj1 ins
        signal = proj2 ins
    in (pure $ lam $ \x => mixer x signal) 
         =<< (nco' loReg) 
         =<< (pure tw)
         
%unhide Prelude.(>>=)
%unhide Prelude.pure
read: IO (BitVec 24, BitVec 16)
read = do putStr "freq tw: \n"
          fflush stdout
          tw <- getLine
          let tw = (BitVec.fromInteger {n=24} . cast) tw
          putStr "data: \n"
          fflush stdout
          dat <- getLine
          let dat = (BitVec.fromInteger {n=16} . cast) dat
          pure (tw, dat)
       
