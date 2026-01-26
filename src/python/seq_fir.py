import subprocess
import os
import signal
import numpy as np

def to_number(num_str:str) -> np.uint64:
    # get the lower 48 bits
    val = np.uint64(num_str[num_str.find("\'")+2:]) & 0xFFFFFFFFFFFF
    # extend the sign bit
    if (val & 0x800000000000):
       val = val | 0xFFFF000000000000
    return val

class FIR(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.fir_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, en: bool, dat: np.uint32) -> tuple[bool, np.uint64]:

        current_state = self.fir_process.stdout.readline().rstrip("\n")

        if not self.silent:
            print("Current State:", current_state)

        en_req = self.fir_process.stdout.readline().rstrip("\n")
        en_str = ("1" if en else "0") + "\n"
        self.fir_process.stdin.write(en_str)
        self.fir_process.stdin.flush()

        dat_req = self.fir_process.stdout.readline().rstrip("\n")
        dat_str = str(dat) + "\n"
        self.fir_process.stdin.write(dat_str)
        self.fir_process.stdin.flush()

        result_str = self.fir_process.stdout.readline().rstrip("\n")
        result_str = result_str[1:-1] # remove '(' and ')'
        valid_str, result_num_str = result_str.split(", ")
        valid = (valid_str == "1'd1")
        result = to_number(result_num_str) # / (2**34 - 1)
        
        return valid, result


    def terminate(self):
        os.killpg(os.getpgid(self.fir_process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    pass
