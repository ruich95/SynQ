import subprocess
import os
import signal
import numpy as np

def to_number(num_str:str) -> np.int64:
    # get the lower 48 bits
    val = np.uint64(num_str[num_str.find("\'")+2:]) & 0xFFFFFFFFFFFF
    # extend the sign bit
    if (val & 0x800000000000):
       val = val | 0xFFFF000000000000
    return np.int64(val)

class Decimator(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.decimator_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, en: bool, dat: np.float64) -> tuple[bool, np.float64]:
        

        dat = np.uint64(np.int64(dat * (2**47 - 1)))
        
        #get the lower 48 bits
        dat = dat & 0xFFFFFFFFFFFF
        #extent the sign bit
        if (dat & 0x800000000000):
           dat = dat | 0xFFFF000000000000

        current_state = self.decimator_process.stdout.readline().rstrip("\n")

        if not self.silent:
            print("Current State:", current_state)

        en_req = self.decimator_process.stdout.readline().rstrip("\n")
        en_str = ("1" if en else "0") + "\n"
        self.decimator_process.stdin.write(en_str)
        self.decimator_process.stdin.flush()

        dat_req = self.decimator_process.stdout.readline().rstrip("\n")
        dat_str = str(dat) + "\n"
        self.decimator_process.stdin.write(dat_str)
        self.decimator_process.stdin.flush()

        result_str = self.decimator_process.stdout.readline().rstrip("\n")
        result_str = result_str[1:-1] # remove '(' and ')'
        valid_str, result_num_str = result_str.split(", ")
        valid = (valid_str == "1'd1")
        result = to_number(result_num_str) / (2**47 - 1)
        
        return valid, result


    def terminate(self):
        os.killpg(os.getpgid(self.decimator_process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    try:
        decimator = Decimator(exec_path="../../build/exec/decimator2")
        data = [0.1 * i for i in range(10)]
        for i in range(10):
            valid, result = decimator.forward(en=True, dat=data[i])
            print(f"Valid: {valid}, Result: {result}")
    finally:
        decimator.terminate()
