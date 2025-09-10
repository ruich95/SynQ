module Impl.TAC.Pass.Common

import Data.List

public export 
record Zipper (a: Type) where
  constructor MkZipper
  prev: List a
  cur : Maybe a
  rest: List a
  
%name Zipper z1, z2
  
public export
fromList: List a -> Zipper a
fromList [] = 
  MkZipper [] Nothing []
fromList (x :: xs) = 
  MkZipper [] (Just x) xs

public export
toList: Zipper a -> List a
toList (MkZipper prev Nothing rest) = 
  prev ++ rest
toList (MkZipper prev (Just x) rest) = 
  prev ++ [x] ++ rest
  
public export
isEnd: Zipper a -> Bool
isEnd (MkZipper _ _ []) = True
isEnd (MkZipper _ _ (x :: xs)) = False

public export
next: Zipper a -> Zipper a
next z@(MkZipper prev cur []) = z
next z@(MkZipper prev cur (x :: xs)) = 
  case cur of
    Nothing => 
      {cur := Just x, rest := xs} z
    (Just y) => 
      {prev := snoc prev y, 
       cur  := Just x, 
       rest := xs} z

public export
drop: Zipper a -> Zipper a
drop z = {cur := Nothing} z

public export
isElement: (Eq a) => a -> List a -> Bool
isElement x [] = False
isElement x (y :: xs) = 
  if x == y then True 
  else isElement x xs
