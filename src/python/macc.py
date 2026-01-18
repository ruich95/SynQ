import subprocess
import json
from typing import TypedDict
import os
import signal
import numpy as np
from tqdm import tqdm

def to_number(num_str:str) -> np.uint64:
    # get the lower 48 bits
    val = np.uint64(num_str[num_str.find("\'")+2:]) & 0xFFFFFFFFFFFF
    # extend the sign bit
    if (val & 0x800000000000):
       val = val | 0xFFFF000000000000
    return np.uint64(val)

class MACC(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.macc_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, rst: bool, x: np.uint32, y: np.uint32) -> np.uint64:

        current_state = self.macc_process.stdout.readline().rstrip("\n")

        rst_req = self.macc_process.stdout.readline().rstrip("\n")
        rst_str = ("1" if rst else "0") + "\n"
        self.macc_process.stdin.write(rst_str)
        self.macc_process.stdin.flush()

        x_req = self.macc_process.stdout.readline().rstrip("\n")
        x_str = str(int(x)) + "\n"
        self.macc_process.stdin.write(x_str)
        self.macc_process.stdin.flush()

        y_req = self.macc_process.stdout.readline().rstrip("\n")
        y_str = str(int(y)) + "\n"
        self.macc_process.stdin.write(y_str)
        self.macc_process.stdin.flush()

        output = self.macc_process.stdout.readline().rstrip("\n")
        output = to_number(output)
        
        return output

    def terminate(self):
        os.killpg(os.getpgid(self.macc_process.pid), signal.SIGTERM)


        
if __name__ == "__main__":
    try:
        sign_ext_48 = lambda x: np.uint64(x) if (x & 0x800000000000) == 0 else np.uint64(x | 0xFFFF000000000000)

        macc = MACC("../../build/exec/maccProg", silent=False)
        
        # rst_signal = np.zeros(32, dtype=bool)
        x_signal = np.random.randint(-500, 1000, size=32, dtype=np.int32)
        y_signal = np.random.randint(-500, 1000, size=32, dtype=np.int32)
        output_signal = np.zeros(32, dtype=np.int64)
        ref_out1 = np.zeros(32, dtype=np.int64)
        ref_out2 = np.zeros(32, dtype=np.int64)

        reset_at = 16

        for i, (x, y) in enumerate(zip(x_signal, y_signal)):
            rst = (i==reset_at)
            output_signal[i] = np.int64(macc.forward(rst, np.uint32(x), np.uint32(y)))

        ref_out1 = np.cumsum(x_signal.astype(np.int64)[:reset_at-2] * y_signal.astype(np.int64)[:reset_at-2]).astype(np.int64)
        ref_out2 = np.cumsum(x_signal.astype(np.int64)[reset_at-2:] * y_signal.astype(np.int64)[reset_at-2:]).astype(np.int64)

        print("Output Signal1:\t\t", output_signal[3:reset_at+1])
        print("Reference Output1:\t", ref_out1)

        print("Output Signal2:\t\t", output_signal[reset_at+1:])
        print("Reference Output2:\t", ref_out2[:-3])

    finally: 
        macc.terminate()