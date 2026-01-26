import subprocess
import json
from typing import TypedDict
import os
import signal
from unittest import skip
from tqdm import tqdm
import matplotlib.pyplot as plt
import numpy as np
from scipy.interpolate import interp1d


def to_number(num_str:str) -> np.float64:
    return np.int32(np.uint32(num_str[num_str.find("\'")+2:])) / (2**29)

class CAtan2(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.catan2_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, en: bool, x1: np.float64, x2: np.float64) -> tuple[bool, np.float64]:
        
        x1 = np.uint32(np.int32(x1 * (2**29)))
        x2 = np.uint32(np.int32(x2 * (2**29)))

        current_state = self.catan2_process.stdout.readline().rstrip("\n")

        if not self.silent:
            print("Current State:", current_state)

        en_req = self.catan2_process.stdout.readline().rstrip("\n")
        en_str = ("1" if en else "0") + "\n"
        self.catan2_process.stdin.write(en_str)
        self.catan2_process.stdin.flush()


        # send x2 (x) before x1 (y) to compute atan2(x1/x2)
        x2_req = self.catan2_process.stdout.readline().rstrip("\n")
        x2_str = str(x2) + "\n"
        self.catan2_process.stdin.write(x2_str)
        self.catan2_process.stdin.flush()

        x1_req = self.catan2_process.stdout.readline().rstrip("\n")
        x1_str = str(x1) + "\n"
        self.catan2_process.stdin.write(x1_str)
        self.catan2_process.stdin.flush()


        result_str = self.catan2_process.stdout.readline().rstrip("\n")
        result_str = result_str[1:-1] # remove '(' and ')'
        valid_str, result_num_str = result_str.split(", ")
        valid = (valid_str == "1'd1")
        result = to_number(result_num_str)
        
        return valid, result


    def terminate(self):
        os.killpg(os.getpgid(self.catan2_process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    try:
        catan2 = CAtan2(exec_path="../../build/exec/atan2", silent=True) 
        x1 = np.random.uniform(-1.5, 1.5, 1000)
        x2 = np.random.uniform(-1.5, 1.5, 1000)
        

        ref = np.atan2(x1, x2)

        res = np.zeros_like(ref)

        for i, (x1_val, x2_val) in enumerate(tqdm(zip(x1, x2), total=len(x1))):
            for iter in range(32):
                if iter == 0:
                    en = True
                else:
                    en = False
                valid, res[i] = catan2.forward(en, x1_val, x2_val)

                if valid:
                    break

        err = np.abs(ref - res)

        print("Average Error: {}".format(np.mean(err)))

        print("Max Error:{} , at input x1, x2: {}, {}, ref: {}, res: {}".format(np.max(err), x1[np.argmax(err)], x2[np.argmax(err)], ref[np.argmax(err)], res[np.argmax(err)]))
        
    finally: 
        catan2.terminate()
