import subprocess
import re
from typing import Tuple
import json
from numpy import uint32

def extract_numbers(input_string: str) -> Tuple[Tuple[int, int, int], int]:
    """
    Extract numbers from the given string in the format `((1'dAAA, (32'dBBB, 32'dCCC)), 32'dDDD)`
    and return them as a tuple of integers.

    Args:
        input_string (str): The input string containing the numbers.

    Returns:
        Tuple[Tuple[int, int, int], int]: A tuple in the format ((AAA, BBB, CCC), DDD).
    """
    # Regular expression to extract numbers after "d"
    pattern = r"\d+'d(\d+)"
    
    # Find all matches of numbers in the input string
    matches = re.findall(pattern, input_string)
    
    # Convert matches to integers
    numbers = list(map(int, matches))
    
    # Create and return the desired tuple structure
    return ((numbers[0], numbers[1], numbers[2]), numbers[3])

class RV32I(object):
    def __init__(self, exec: str):
        self.process = \
            subprocess.Popen(exec, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True)
    
    def forward(self, inst: uint32, pc: uint32, silent: bool = False) \
                    -> Tuple[Tuple[uint32, uint32, uint32], uint32]:
        inst_str = "{}\n".format(inst)
        pc_str   = "{}\n".format(pc)

        current_state = self.process.stdout.readline().rstrip("\n")
        if not silent:
            print(current_state)

        inst_req = self.process.stdout.readline().rstrip("\n")

        if not silent:
            print(inst_req + "{:#010x}".format(inst))

        self.process.stdin.write(inst_str)
        self.process.stdin.flush()

        req_pc = self.process.stdout.readline().rstrip("\n")

        if not silent:
            print(req_pc + pc_str, end="")

        self.process.stdin.write(pc_str)
        self.process.stdin.flush()

        out_str = json.loads(self.process.stdout.readline())["output"]
        
        return extract_numbers(out_str)
    
    def stop(self):
        self.process.terminate()
        self.process.kill()
        # _ = self.process.communicate()
        
        

