import subprocess
import json
from typing import TypedDict
import os
import signal
import numpy as np
from tqdm import tqdm

def to_number(num_str:str) -> np.uint32:
    # get the lower 18 bits
    val = np.uint32(num_str[num_str.find("\'")+2:]) & 0x3FFFF
    # extend the sign bit
    if (val & 0x20000):
        val = val | 0xFFFC0000
    return np.uint32(val)

class FIRCoef(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.coef_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, en: bool) -> int:

        current_state = self.coef_process.stdout.readline().rstrip("\n")

        en_req = self.coef_process.stdout.readline().rstrip("\n")
        en_str = ("1" if en else "0") + "\n"
        self.coef_process.stdin.write(en_str)
        self.coef_process.stdin.flush()

        output = self.coef_process.stdout.readline().rstrip("\n")
        output = to_number(output)
        
        return output

    def terminate(self):
        os.killpg(os.getpgid(self.coef_process.pid), signal.SIGTERM)


        
if __name__ == "__main__":
    try:
        coef = FIRCoef("../../build/exec/lpfCoef01025Prog", silent=False)
        
        en_signal = np.zeros(32, dtype=bool)
        en_signal[0] = True
        output_signal = np.zeros(32, dtype=np.int32)
        for i in range(len(en_signal)):
            output_signal[i] = np.int32(coef.forward(en_signal[i]))
        print("Enable Signal:", en_signal)
        print("Output Signal:", output_signal / 2**17)

    finally: 
        coef.terminate()