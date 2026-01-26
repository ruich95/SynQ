import subprocess
import os
import signal
import numpy as np

def to_number(num_str:str) -> np.uint64:
    # get the lower 37 bits
    val = np.uint64(num_str[num_str.find("\'")+2:]) & 0x1FFFFFFFFF
    # extend the sign bit
    if (val & 0x1000000000):
       val = val | np.uint64(0xFFFFFFE000000000)
    return val

class CIC3D128(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.cic_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, dat: np.uint16) -> tuple[bool, np.uint64]:
        

        current_state = self.cic_process.stdout.readline().rstrip("\n") 
        if not self.silent:
            print("Current State:", current_state)


        dat_req = self.cic_process.stdout.readline().rstrip("\n")
        dat_str = str(dat) + "\n"
        self.cic_process.stdin.write(dat_str)
        self.cic_process.stdin.flush()

        result_str = self.cic_process.stdout.readline().rstrip("\n")
        result_str = result_str[1:-1] # remove '(' and ')'
        valid_str, result_num_str = result_str.split(", ")
        valid = (valid_str == "1'd1")
        result = to_number(result_num_str)
        
        return valid, result


    def terminate(self):
        os.killpg(os.getpgid(self.cic_process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    pass
