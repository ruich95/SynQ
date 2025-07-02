module Examples.Sel

import SynQ

%hint
lteSucc: (n:Nat) -> LTE n (S n)
lteSucc 0 = LTEZero
lteSucc (S k) = LTESucc (lteSucc k)

-- %spec n, dat, cWidth
sel': {cWidth: _} -> (Comb comb, Primitive comb)
  => {n: Nat}
  -> {auto aIsSig: Sig a}
  -> (count: comb () (BitVec cWidth))
  -> (dat: comb () (Repeat (S n) a))
  -> (pre: (comb () (BitVec cWidth) -> comb () a) -> comb () a)
  -> (idx: comb () (BitVec cWidth))
  -> comb () a
sel' {n = 0} count dat pre idx = pre $ \_ => dat
sel' {n = (S 0)} count dat pre idx = 
  pre $ \_ => if_ (idx `eq` count) 
                  (proj1 dat) 
                  (proj2 dat)
sel' {n = (S (S k))} count dat pre idx = 
  let dataSig = repeatSig (S (S k)) aIsSig
      pre' = \f => pre $ \idx' => if_ (idx `eq` count) 
                                      (proj1 dat) 
                                      (f idx')
  in sel' {n=(S k)} (lower' cWidth $ add count (const $ BV 1)) (proj2 dat) pre' idx

export
sel2: {cWidth: _} -> (Comb comb, Primitive comb)
  => {n: Nat}
  -> {auto aIsSig: Sig a}
  -> (idx: comb () (BitVec cWidth))
  -> (dat: comb () (Repeat n a))
  -> (otherwise: comb () a)
  -> comb () a
sel2 {n = 0} idx dat otherwise = otherwise
sel2 {n = (S k)} idx dat otherwise = sel' {n=k} (const $ BV 0) dat (\f => f idx) idx

export
-- %spec dat, n
sel: {cWidth: _} -> (Comb comb, Primitive comb)
  => {n: Nat}
  -> {auto aIsSig: Sig a}
  -> {auto prf: LTE 1 n}
  -> (idx: comb () (BitVec cWidth))
  -> (dat: comb () (Repeat n a))
  -> comb () a
sel {n = (S k)} {prf = (LTESucc x)} idx dat = 
  sel' {n= k} (const $ BV 0) dat (\f => f idx) idx

trySel: (Comb comb, Primitive comb) 
  => (idx: comb () (BitVec 3)) -> comb () UInt8
trySel idx = sel {n=5} idx 
                  (prod (const $ BV {n=8} 3) 
                  (prod (const $ BV {n=8} 1) 
                  (prod (const $ BV {n=8} 4) 
                  (prod (const $ BV {n=8} 5) 
                        (const $ BV {n=8} 9))))) 
                                                      
runSel: BitVec 3 -> UInt8
runSel x = (runComb $ lam trySel) x

