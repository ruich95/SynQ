# Toggle IO

In this demo, we creat a simple system that __toggles its output on input events__.

The module *SynQ* exports all components we are going to use.

```idris
import SynQ

%hide Linear.seq
```

## Input Events as Clock

We start by specifying a system that is triggered by input events in *SynQ*. By triggering the system with input events, input events themselves form clock events, which should give us the minimal system that achieve our objectives. As the first step, we specify the function `toggle1Fn` that invoked on an event. This function should has the following type:

```idris
toggle1Fn: {comb:_} -> (Comb comb, Primitive comb) 
  => comb (BitVec 1)  -- current output
          (BitVec 1)  -- next output
```

in which the first line suggests that the implementation of the function requires __stateless__ glue and atomic components defined by the `Comb` and `Primitive` interface, respectively. Meanwhile, the secode line implies that this function itself is a stateless component that has a 1 bit input (the system's output before the event) and a 1 bit output (the system's output after the event). A possible implementation will be:

```idris
toggle1Fn = lam $ \x => not x
```

in which the lambda function `\x => not x` specifies that the current output `x` is toggled (negated) on an event and `lam: (comb () a -> comb () b) -> comb a b` packes the function as a component.

Lastly, we should introduce a feedback loop so that the current *next output* can be the next *current output*. We do so by using a register to introducing an unit delayed backward path. The system's type will be:

```idris
toggle1: {comb:_} -> {seq: _}
  -> (Seq comb seq, Primitive comb, Reg comb seq)
  => seq (!* BitVec 1) () (BitVec 1)
```

The first two lines of this type suggests that the system `toggle1` is a stateful (sequential) system built upon stateless and stateful glues and atomic components. In the mean time, `seq (!* BitVec 1) () (BitVec 1)` indicates that the system has an internal state `!* BitVec 1`, which is an linear term that can be unrestricted (`!*` modality), specifying 1-bit registers in which the value stored can be used unrestrictly, who, itself cannot be duplicated due to linearity. The last two parameters of `seq (!* BitVec 1) () (BitVec 1)` suggests that the system has no input, because the input is the *clock event*, and 1-bit output. The inplementation is shown below:

```idris
toggle1 = (abst $ \x => (pure $ proj1 x) =<< (set $ proj2 x)) 
      =<< (Seq.pure $ lam $ \x => prod x (app toggle1Fn x)) 
      =<< get
```

which indicates that the system is implemented by stages composed by `=<<`. This composition implies that all stages sequentilly (from rhs to lhs) modify the *same* state, while concurrency among computations on non-linear veriables are preserved. 

We may run `toggle1` as a __reactive program__. The first step is to define a function to read from `stdin` as follows

```idris
readIn1: IO ()
readIn1 = do _ <- getLine
             pure ()
```

Note that for `toggle1`, the content read in does not matter because all we need is distinguishing different clock events from input events synchronised with the clock. The program is given as follows:

```idris
toggleSW1: IO ()
toggleSW1 = reactMealy readIn1 -- specify how input is interperated
                      (runSeq $ toggle1 {seq=Eval.Sequential}      -- specialise the specification
                                        {comb=Eval.Combinational}) -- to an Idris2 function
                      (MkBang 0)  -- specify initial state(s)
```
which can be compiled and executed as a regular Idris2 program.

## Input Events Sampled by the Clock

Even though the example above do work as expected, using system's input as the clock is not the conventional way how an synchronous system is modelled. As already shown in the type of `toggle1`, with this kind of modelling, the system may be specified __without__ any explicit input.

In this part, we model the input as a free-running signal __sampled__ by the system's clock, which is the more conventional way of specifying reactive synchronous systems. 

### Detecting Input Events

Since input events are not clock events any more, we first define what an input event is and specify the corresponding sub-system that detects input events.

In this demo, we define the input events as the __rising edge__ of a 1-bit input. Specifically, for an synchronised input, its rising edge is defined as following:

> $r_k$ is a rising edge of the input signal at clock $k$ iff $i_k$ (input at clock $k$) equals to 1 and $i_{k-1}$ equals to 0.

The input detection sub-system can be specified by first specifying a two-inputs combinational (sub-)sub-system whose inputs corresponding to the current and previous inputs of the system, respectively, as follows:

```idris
isRisingFn: {comb:_} -> (Comb comb, Primitive comb)
  => (curIn : comb () $ BitVec 1)
  -> (prevIn: comb () $ BitVec 1)
  -> comb () $ BitVec 1
isRisingFn curIn prevIn = 
  mux21 (and (eq curIn  (const $ BV 1))
             (eq prevIn (const $ BV 0)))
        (const $ BV 1)
        (const $ BV 0)
```

which, comparing to `toggle1Fn` has not been packed as a component with `lam` yet, and hence cannot be directly interpreted as software/hardware. On the other hand, specifying components in this way allows us to further leverage the meta-language to specify how components are connected, as we are going to present.

The second step is puting `isRisingFn` into the invironment so that its seconde input is always the __one-clock delayed__ current input. To do so, we should consider how to preform a one-clock delay on an input signal. Interfaces defined in `Sym.Seq` and `Sym.SeqPrimitive` do not provide a method which allow us to insert a delay into a forward path. Indeed, delays can not be directly used as components because all delays are implicitly assumed to form loops between paired varibales bind with mutiplicity 1 (linear variables). To delaying a signal, we may use the following components: 

```idris
dly: {n:_} -> {comb:_} -> {seq:_} 
  -> (Seq comb seq)
  => (1 reg: Reg comb seq)
  -> (comb () $ BitVec n)
  -> seq (!* BitVec n) () (BitVec n)
dly (MkReg get set) xIn = (abst $ \x => (pure $ proj1 x) 
                                    =<< (set $ proj2 x)) 
                      =<< (pure $ lam $ \x => prod x xIn) 
                      =<< get
```

which retrives the value from the current state as the current output and set the current input as the new state. Note that in the type of `dly`, instead of using `Reg` as an interface at the lhs of `=>`, it is used as a linear term in the context, which restrict us to use __exactly one__ pair of `get` and `set`. Its another otion enabled by quantitative types that allows us to have a fine-grained control of resources (components).

With delay specified, we can define the sub-system of rising-edge detecting as follows:

```idris
isRising: {comb:_} -> {seq:_} 
  -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq)
  -> seq (!* BitVec 1) (BitVec 1) (BitVec 1)
isRising reg = abst $ \curIn => (pure  (lam $ isRisingFn curIn))  
                            =<< (dly reg curIn)
```

in which, instead of connecting stages in a __point-free__ style, `curIn` as the input is served to both the first and secod stage of the system. In this way, specifying intermediate components as functions in the meta-language allows us to further leveraging the meta-language to specify how components are connected, as we discussed eariler.

### Toggling the Output

Similar as eariler, we start by specifying the sub-system's combinational part:

```idris
toggle2Fn: {comb:_} -> (Comb comb, Primitive comb)
  => (isRising: comb () $ BitVec 1)
  -> (curOut: comb () $ BitVec 1)
  -> (comb () $ BitVec 1) -- next out
toggle2Fn isRising curOut = 
  mux21 isRising (not curOut) (curOut)
```
To apply `toggle2Fn` in a stateful component

```idris

toggle2Fn': {comb:_} -> (Comb comb, Primitive comb)
  => comb (BitVec 1, BitVec 1) 
          (BitVec 1, BitVec 1)
toggle2Fn' = 
  lam $ \ins => let isRis  = proj1 ins
                    curOut = proj2 ins
                    nextOut = toggle2Fn isRis curOut
                in prod curOut
                        nextOut 
                       
  
toggle2: {comb:_} -> {seq:_} 
  -> (Seq comb seq, Primitive comb)
  => (1 reg: Reg comb seq)
  -> seq (!* BitVec 1) (BitVec 1) (BitVec 1)
toggle2 reg = scan reg toggle2Fn'
```

```idris
toggle: {comb:_} -> {seq:_} 
    -> (Seq comb seq, Primitive comb)
    => (1 regInner: Reg comb seq)
    -> (1 regDly:   Reg comb seq)
    -> seq (LPair (!* BitVec 1) (!* BitVec 1)) 
           (BitVec 1) (BitVec 1)
toggle regToggle regDly = (toggle2 regToggle) <<< (isRising regDly)
```

```idris
toggle_step: (BitVec 1) 
      -> (1 _: LPair (!* BitVec 1) (!* BitVec 1)) 
      -> LC (LPair (!* BitVec 1) (!* BitVec 1)) (BitVec 1)
toggle_step x = runState $ runSeq (toggle reg reg) $ x

getState: (LC s a) -> s
getState (l # v) = l

getOut: (LC s a) -> a
getOut (l # v) = v

fst': (LPair (!* a) (!* b)) -> a
fst' (MkBang x # MkBang _) = x

snd': (LPair (!* a) (!* b)) -> b
snd' (MkBang _ # MkBang x) = x



lemma1: bvAnd {n = 1} (BV 0) (BV 1) = BV 0
lemma2: bvAnd {n = 1} (BV 1) (BV 1) = BV 1
lemma3: bvAnd {n = 1} (BV 0) (BV 0) = BV 0
lemma4: bvAnd {n = 1} (BV 1) (BV 0) = BV 0

prop1: (xin: BitVec 1) -> (st: LPair (!* BitVec 1) (!* BitVec 1))
  -> (getOut $ toggle_step xin st) = (snd' st)
prop1 xin ((MkBang st1) # (MkBang st2)) = Refl

prop2: (xin: BitVec 1) -> (st: LPair (!* BitVec 1) (!* BitVec 1))
  -> (fst' $ getState $ toggle_step xin st) = xin
prop2 xin ((MkBang st1) # (MkBang st2)) = Refl

prop3: (st2: (!* BitVec 1))
  -> (let st = ((MkBang $ BV 0) # st2) in (snd' $ getState $ toggle_step (BV 1) st)) 
  = (let (MkBang st2') = st2 in bvNot st2')
prop3 (MkBang st2') = rewrite lemma2 in Refl

prop4: (st2: (!* BitVec 1))
  -> (let st = ((MkBang $ BV 0) # st2) in (snd' $ getState $ toggle_step (BV 0) st)) 
  = (let (MkBang st2') = st2 in st2')
prop4 (MkBang st2') = rewrite lemma1 in Refl

prop5: (xin: BitVec 1) -> (st2: (!* BitVec 1))
  -> (let st = ((MkBang $ BV 1) # st2) in (snd' $ getState $ toggle_step xin st)) 
  = (let (MkBang st2') = st2 in st2')
prop5 xin (MkBang st2') with (xin == BV 1)
  prop5 xin (MkBang st2') | False = rewrite lemma3 in Refl
  prop5 xin (MkBang st2') | True = rewrite lemma4 in Refl

```


```idris

-- toggleFn: {comb:_} -> (Comb comb, Primitive comb)
--     => (curIn:  comb () $ BitVec 1)
--     -> (prevIn: comb () $ BitVec 1)
--     -> (curSt:  comb () $ BitVec 1)
--     -> comb () (BitVec 1, BitVec 1) -- (current output, next state)
-- toggleFn curIn prevIn curSt = 
--   let toggle = and (eq curIn  (const $ BV 1))
--                    (eq prevIn (const $ BV 0))
--   in prod curSt
--          (mux21 toggle (not curSt) curSt)
         
-- toggleInner: {comb:_} -> {seq:_} 
--     -> (Seq comb seq, Primitive comb)
--     => (1 reg: Reg comb seq)
--     -> (curIn:  comb () $ BitVec 1)
--     -> (prevIn: comb () $ BitVec 1)
--     -> seq (!* BitVec 1) () (BitVec 1)           
-- toggleInner reg curIn prevIn = 
--   scan reg (lam $ \x => toggleFn curIn prevIn (proj2 x))
  
-- toggle: {comb:_} -> {seq:_} 
--     -> (Seq comb seq, Primitive comb)
--     => (1 regInner: Reg comb seq)
--     -> (1 regDly:   Reg comb seq)
--     -> seq (LPair (!* BitVec 1) (!* BitVec 1)) 
--            (BitVec 1) (BitVec 1)
-- toggle regInner regDly = (abst $ \x => toggleInner regInner (proj1 x) (proj2 x)) 
--                      <<< (abst $ \x => (pure $ lam $ prod x) =<< (dly regDly x))

-- readIn: IO (BitVec 1)
-- readIn = do str <- getLine
--             pure $ if str == "1" 
--                    then BV 1 
--                    else BV 0
                   
-- genProg: IO ()
-- genProg = reactMealy readIn 
--                  (runSeq $ toggle reg reg) 
--                  (MkBang 0 # MkBang 0)
                 
-- genVerilog: IO ()
-- genVerilog = writeVerilog "toggle" (toggle reg reg)
```
