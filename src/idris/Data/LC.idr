module Data.LC

import Data.Linear

public export
record LC s a where
  constructor (#)
  1 l: s
  v: a

public export
snd: (Consumable s) => (1 _: LC s a) -> (!* a)
snd (l # v) = let () = consume l in (MkBang v)

public export
Show a => Show (!* a) where
  show (MkBang x) = "! \{show x}"

public export
(Show s, Show a) => Show (LC s a) where
  show (l # v) = "<\{show l}, \{show v}>"

public export
(Show a, Show b) => Show (LPair a b) where
  show (x # y) = "\{show x} # \{show y}"



