module Impl.HDL.Verilog

import Impl.HDL.Flatten
import Impl.HDL.Port

import Data.List
import Data.String
import System.File

import Data.Name
import Data.Value
import Data.BitVec

import Data.Linear

deleteAll: Eq a => a -> List a -> List a
deleteAll x xs = filter ((/=) x) xs

unique: Eq a => List a -> List a
unique [] = []
unique (x :: xs) = x :: unique (deleteAll x xs)

getPortsModule: FlattenModuleInst -> List AtomicPort
getPortsModule (MkFlattenModule _ _ _ iPA oPA) 
  = (map rhs iPA) ++ (map rhs oPA)
  
getUsedPortsNL: FlattenCombNL -> List AtomicPort
getUsedPortsNL (MkFCNL _ _ assignedPorts instModules) 
  = let portsAssigned = (map rhs assignedPorts) ++ (map lhs assignedPorts)
        portsToModule = getPortsModule =<< instModules
    in unique $ portsAssigned ++ portsToModule


getIOPortsNL: FlattenCombNL -> List AtomicPort
getIOPortsNL (MkFCNL iPort oPort _ _) = iPort ++ oPort 

isVarPort: AtomicPort -> Bool
isVarPort (AP (NM _) len UV) = True
isVarPort _ = False

getVarPort: List AtomicPort -> List AtomicPort
getVarPort = filter isVarPort

getInnerPortsNL: FlattenCombNL -> List AtomicPort
getInnerPortsNL nl = 
  let ports = getUsedPortsNL nl
      ioPorts = unique $ getIOPortsNL nl
  in getVarPort $ ports \\ ioPorts

portDeclStr: AtomicPort -> String
portDeclStr (AP UN len val) = "// unknown"
portDeclStr (AP (NM nm) len val) = "wire [\{show $ minus len 1}:0] w_\{nm}"

portStr: AtomicPort -> String
portStr (AP UN len UV)      = "// unknown"
portStr (AP nm len (V x))   = "\{show x}"
portStr (AP (NM nm) len UV) = "w_\{nm}"

regDeclStr': AtomicPort -> String
regDeclStr' (AP UN len val) = "// unknown"
regDeclStr' (AP (NM nm) len val) = "reg [\{show $ minus len 1}:0] r_\{nm}"

regDeclStr: AtomicPortAssign -> String
regDeclStr (APA lhs rhs) = regDeclStr' lhs --?regDeclStr_rhs_0

regStr: AtomicPort -> String
regStr (AP UN len UV)      = "// unknown"
regStr (AP nm len (V x))   = "r_\{show x}"
regStr (AP (NM nm) len UV) = "r_\{nm}"

portAssignStr: AtomicPortAssign -> String
portAssignStr (APA lhs rhs) = 
  let left  = portStr lhs
      right = portStr rhs
  in "assign \{left} = \{right};"

regGetStr: AtomicPortAssign -> String
regGetStr (APA lhs rhs) = 
  let left  = portStr lhs
      right = regStr  lhs
  in "assign \{left} = \{right};"

regSetStr: AtomicPortAssign -> String
regSetStr (APA lhs rhs) = 
  let left  = regStr  lhs
      right = portStr rhs
  in "\{left} <= \{right};"

moduleParamStr: (String, Nat) -> String
moduleParamStr (param, val) = ".\{param}(\{show val})"

modulePortStr: AtomicPortAssign -> String
modulePortStr (APA (AP UN len val) rhs) = "// unknown"
modulePortStr (APA (AP (NM nm) len val) rhs) = ".\{nm}(\{portStr rhs})"

moduleInstStr: (indent_:Nat) -> FlattenModuleInst 
  -> List String
moduleInstStr indent_ (MkFlattenModule name idx params iPA oPA) 
  = let module_nm = "\{name}"
        params' = "#(" ++ (joinBy ", " $ map moduleParamStr params) ++ ")"
        inst_nm = "\{name}_\{show idx}"
        ports = "(" ++ (joinBy ", " $ map modulePortStr (iPA ++ oPA)) ++ ");"
    in case params of 
        [] => [indent indent_ "\{module_nm} \{inst_nm} \{ports}"]
        _  => [indent indent_ "\{module_nm} \{params'}",
               indent (indent_ + 2) "\{inst_nm} \{ports}"]
        
preJoinBy: String -> List String -> List String
preJoinBy _ [] = []
preJoinBy _ [x] = [x]
preJoinBy s (x :: (y :: xs)) = ((x++s) :: preJoinBy s (y :: xs))

combNetListIOStr: (indent_:Nat) -> FlattenCombNL 
  -> List String
combNetListIOStr indent_ (MkFCNL iPort oPort _ _) = 
  let iPStr = map ((indent indent_) . (\x => "input "  ++ portDeclStr x)) iPort
      oPStr = map ((indent indent_) . (\x => "output " ++ portDeclStr x)) oPort
  in preJoinBy "," (iPStr ++ oPStr)

combNetListDeclStr: (indent_:Nat) -> FlattenCombNL 
  -> List String
combNetListDeclStr indent_ m = 
  map ((indent indent_) 
       . (\x => x ++ ";") 
       . portDeclStr) 
     $ getInnerPortsNL m

combNetListAssignStr: (indent_:Nat) -> FlattenCombNL 
  -> List String
combNetListAssignStr indent_ (MkFCNL _ _ assignedPorts _) = 
  map ((indent indent_) . portAssignStr) assignedPorts
  
combNetListModuleStr: (indent_:Nat) -> FlattenCombNL 
  -> List String
combNetListModuleStr indent_ (MkFCNL _ _ _ instModules) = 
  (moduleInstStr indent_) =<< instModules
  
snocLast: String -> List String -> List String
snocLast s [] = []
snocLast s (x :: []) = [x ++ s]
snocLast s (x :: (y :: xs)) = x :: snocLast s (y :: xs)

export
combNetListStr: (name: String) -> FlattenCombNL 
  -> List String
combNetListStr name m = ["module \{name} ("]
                 ++ snocLast ");" (combNetListIOStr 4 m)
                 ++ [""]
                 ++ combNetListDeclStr 2 m
                 ++ [""]
                 ++ combNetListAssignStr 2 m
                 ++ [""]
                 ++ combNetListModuleStr 2 m
                 ++ [""]
                 ++ ["endmodule"]
                 
netListRegDeclStr: (indent_ : Nat) -> List AtomicPortAssign
  -> List String
netListRegDeclStr indent_ lPort = 
  map ((indent indent_) 
       . (\x => x ++ ";") 
       . regDeclStr) 
      lPort

netListRegWireDeclStr: (indent_ : Nat) -> List AtomicPortAssign
  -> List String
netListRegWireDeclStr indent_ lPort = 
  map ((indent indent_) 
       . (\x => x ++ ";") 
       . portDeclStr) 
      (unique $ (map lhs lPort) ++ (map rhs lPort))

netListRegGetStr: (indent_ : Nat) -> List AtomicPortAssign
  -> List String
netListRegGetStr indent_ lPort = 
  map ((indent indent_) 
       . regGetStr)
      lPort

netListRegSetStr: (indent_ : Nat) -> List AtomicPortAssign
  -> List String
netListRegSetStr indent_ lPort = 
  map ((indent indent_) 
       . regSetStr)
      lPort

export
netListStr: (name: String) -> FlattenNetList
  -> List String
netListStr name m
  = let (cm, lp) = unpackNetList m
    in ["module \{name} ("]
           ++ snocLast ");" ((indent 4 "input wire clk,") :: combNetListIOStr 4 cm)
           ++ [""]
           ++ combNetListDeclStr 2 cm
           ++ [""]
           -- ++ netListRegWireDeclStr 2 lp
           -- ++ [""]
           ++ netListRegDeclStr 2 lp
           ++ [""]
           ++ netListRegGetStr 2 lp
           ++ [""]
           ++ combNetListAssignStr 2 cm
           ++ [""]
           ++ combNetListModuleStr 2 cm
           ++ [""]
           ++ [indent 2 "always @ (posedge clk) begin"]
           ++ netListRegSetStr 4 lp
           ++ ["end"]
           ++ [""]
           ++ ["endmodule"]

export
writeLns: File -> List String -> IO ()
writeLns f [] = pure ()
writeLns f (x :: xs) = do Right () <- fPutStrLn f x
                            | Left err => printLn err
                          writeLns f xs

-- export               
-- writeCombVerilog: (name: String) -> FlattenCombNL -> IO ()
-- writeCombVerilog name m = 
--   let lns = combNetListStr name m
--   in do (Right f) <- openFile "\{name}.v" WriteTruncate
--           | (Left err) => printLn err
--         writeLns f lns
--         closeFile f

-- export               
-- writeVerilog: (name: String) -> (1 _: !* FlattenNetList) -> IO ()
-- writeVerilog name (MkBang m) = 
--   let lns = netListStr name m
--   in do (Right f) <- openFile "\{name}.v" WriteTruncate
--           | (Left err) => printLn err
--         writeLns f lns
--         closeFile f
