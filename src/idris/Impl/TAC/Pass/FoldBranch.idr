module Impl.TAC.Pass.FoldBranch 

import Impl.TAC.TAC
import Impl.TAC.Data
import Impl.TAC.Pass.Common

data BFTACBlk = Empty | Block (List FlatOp) BFTACBlk | Branch TACData BFTACBlk BFTACBlk

