import subprocess
import json
from typing import TypedDict
import os
import signal
from tqdm import tqdm
import matplotlib.pyplot as plt
import numpy as np
from scipy.interpolate import interp1d


def to_number(num_str:str) -> int:
    return int(num_str[num_str.find("\'")+2:])

class FIR(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.fifo_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def invoke(self, data:int, rst: bool = False, skip: bool = False) -> int:
        
        data = data if data < 256 else 255
        data = data if data >= 0  else 0

        rst_req = self.fifo_process.stdout.readline().rstrip("\n")
        rst_str = ("1" if rst else "0") + "\n"
        self.fifo_process.stdin.write(rst_str)
        self.fifo_process.stdin.flush()

        skip_req = self.fifo_process.stdout.readline().rstrip("\n")
        skip_str = ("1" if skip else "0") + "\n"
        self.fifo_process.stdin.write(skip_str)
        self.fifo_process.stdin.flush()

        data_req = self.fifo_process.stdout.readline().rstrip("\n")
        data_str = str(data) + "\n"
        self.fifo_process.stdin.write(data_str)
        self.fifo_process.stdin.flush()
        
        result_str = self.fifo_process.stdout.readline().rstrip("\n")
        result = json.loads(result_str)["output"]
        result = to_number(result)
        
        return result


    def terminate(self):
        os.killpg(os.getpgid(self.fifo_process.pid), signal.SIGTERM)

def num_convert(x: int) -> int:
    sign = x & (1<<20)
    if sign == 0:
        return x / (2**19-1)
    else:
        val = (x & (1 << 20) - 1)
        val = (~val) + 1 
        val = val & ((1 << 20) - 1)
        return (-1 * val) / (2**19-1)


if __name__ == "__main__":
    try:
        fir = FIR("../../build/exec/fir", silent=False)
        inputs = [0 for i in range(27)]
        inputs[0] = 255
        outputs = []
        for input in tqdm(inputs):
            outputs.append(fir.invoke(input))

        print(outputs)

        outputs = list(map(num_convert, outputs))

        x = np.arange(len(outputs))
        outputs_f = interp1d(x, outputs, kind='cubic')
        newx = np.arange(0, 16.1, 0.1)

        plt.plot(newx, outputs_f(newx), "--")
        plt.stem(x, outputs, 'o')
        plt.show()
    finally: 
        fir.terminate()
