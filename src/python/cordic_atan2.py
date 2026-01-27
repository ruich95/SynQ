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
from common import to_number

class CAtan2(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.catan2_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, en: bool, x1: np.uint32, x2: np.uint32) -> tuple[bool, np.uint32]:

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
        result = np.uint32(to_number(result_num_str, nbits=32) & np.uint64(0xFFFFFFFF))
        
        return valid, result


    def terminate(self):
        os.killpg(os.getpgid(self.catan2_process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    try:
        catan2 = CAtan2(exec_path="../../build/exec/atan2", silent=True) 
        x1 = [-0.16424476, -0.41017246, -0.5811543 , -0.6371264 ] # np.random.uniform(-1, 1, 1000)
        x2 = [-0.6274776 , -0.49741298, -0.27006736,  0.01391446] # np.random.uniform(-1, 1, 1000)
        

        ref = np.atan2(x1, x2)

        res = np.zeros_like(ref, dtype=np.uint32)

        for i, (x1_val, x2_val) in enumerate(tqdm(zip(x1, x2), total=len(x1))):
            for iter in range(32):
                if iter == 0:
                    en = True
                else:
                    en = False
                x1_val = np.uint32(np.int32(x1_val * (2**29)))
                x2_val = np.uint32(np.int32(x2_val * (2**29)))
                valid, res[i] = catan2.forward(en, x1_val, x2_val)

                if valid:
                    break

        res = np.int32(res) / (2**29)

        err = np.abs(ref - res)

        print("Average Error: {}".format(np.mean(err)))

        print("Max Error:{} , at input x1, x2: {}, {}, ref: {}, res: {}".format(np.max(err), x1[np.argmax(err)], x2[np.argmax(err)], ref[np.argmax(err)], res[np.argmax(err)]))

        print(res)
        
    finally: 
        catan2.terminate()
