module Data.Name

public export
data Name: Type where
  UN: Name
  NM: String -> Name
%name Name nm, nm1, nm2

export
Show Name where
  show UN = "unknown"
  show (NM str) = str
  
export
Eq Name where
  (==) UN UN = True
  (==) (NM s1) (NM s2) = (s1 == s2)
  (==) _ _ = False
