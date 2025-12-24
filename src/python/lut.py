import subprocess
import json
from typing import Callable, TypedDict
import os
import signal
import numpy as np
from param import output

def to_number(num_str:str) -> int:
    return int(num_str[num_str.find("\'")+2:])

class LUT(object):
    def __init__(self, exec_path: str, lut: np.ndarray[np.uint16], silent: bool = True):
        self.fifo_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent
        self.lut = lut

    def forward(self, index: np.uint16) -> np.uint16:
        if (not self.silent):
            print("input index: {}".format(index))

        idx_req = self.fifo_process.stdout.readline().rstrip("\n")
        idx_sig_str = str(index) + "\n"
        self.fifo_process.stdin.write(idx_sig_str)
        self.fifo_process.stdin.flush()

        index = self.fifo_process.stdout.readline().rstrip("\n")
        index = to_number(index)
        if (not self.silent):
            print("lut index: {}".format(index))

        raw_data = self.lut[index]
        data_sig_str = str(raw_data) + "\n"
        self.fifo_process.stdin.write(data_sig_str)
        self.fifo_process.stdin.flush()
        if (not self.silent):
            print("lut raw data: {}".format(raw_data))

        data = self.fifo_process.stdout.readline().rstrip("\n")
        data = to_number(data)

        if (not self.silent):
            print("return data: {}".format(data))
        
        return data


    def terminate(self):
        os.killpg(os.getpgid(self.fifo_process.pid), signal.SIGTERM)