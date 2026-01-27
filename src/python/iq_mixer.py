import subprocess
import os
import signal
import numpy as np
from common import to_number

class IQMixer(object):
    def __init__(self, exec_path: str, freq: np.float32, sample_rate: np.float32 = 122.88e6, silent: bool = True):
        self.process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent
        self.tuning_word = np.uint32(np.round((freq / sample_rate) * (2**24)))

    def forward(self, dat: np.uint16) -> tuple[np.uint16, np.uint16]:

        current_state = self.process.stdout.readline().rstrip("\n")

        if not self.silent:
            print("Current State:", current_state)

        tw_req = self.process.stdout.readline().rstrip("\n")
        tw_str = str(self.tuning_word) + "\n"
        self.process.stdin.write(tw_str)
        self.process.stdin.flush()

        dat_req = self.process.stdout.readline().rstrip("\n")
        dat_str = str(dat) + "\n"
        self.process.stdin.write(dat_str)
        self.process.stdin.flush()

        result_str = self.process.stdout.readline().rstrip("\n")
        result_str = result_str[1:-1] # remove '(' and ')'
        result_i_str, result_q_str = result_str.split(", ")
        result_i = to_number(result_i_str, nbits=16) & np.uint64(0xFFFF)
        result_q = to_number(result_q_str, nbits=16) & np.uint64(0xFFFF)
        result_i = result_i.astype(np.uint16)
        result_q = result_q.astype(np.uint16)
    
        return result_i, result_q


    def terminate(self):
        os.killpg(os.getpgid(self.process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    pass
