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

        x1_req = self.catan2_process.stdout.readline().rstrip("\n")
        x1_str = str(x1) + "\n"
        self.catan2_process.stdin.write(x1_str)
        self.catan2_process.stdin.flush()

        x2_req = self.catan2_process.stdout.readline().rstrip("\n")
        x2_str = str(x2) + "\n"
        self.catan2_process.stdin.write(x2_str)
        self.catan2_process.stdin.flush()


        result_str = self.catan2_process.stdout.readline().rstrip("\n")
        result_str = result_str[1:-1] # remove '(' and ')'
        valid_str, result_num_str = result_str.split(", ")
        valid = (valid_str == "1'd1")
        print("Result Str:", result_str)
        result = np.uint32(to_number(result_num_str, nbits=32) & np.uint64(0xFFFFFFFF))
        
        return valid, result


    def terminate(self):
        os.killpg(os.getpgid(self.catan2_process.pid), signal.SIGTERM)

    def __del__(self):
        self.terminate()


if __name__ == "__main__":
    try:
        catan2 = CAtan2(exec_path="../../build/exec/atan2", silent=True) 
        x1 = [-0.6821203231811523, -0.45667439699172974, -0.0808437 ,  0.41178885,  0.9737072 ,  
              1.54854262,  2.07132816, 2.46742916,  2.65620065,  2.56379938,  
              2.14471149,  1.40581024, 0.42329174, -0.65697902, -1.64068985, -2.32461715, -2.54850554,
             -2.24118853, -1.44869089, -0.33338216,  0.85900277,  1.85737669, 2.4327507 ,  2.45581794,  
             1.92798054,  0.97730058, -0.17828356, -1.28841996, -2.13112307, -2.56011271] # np.random.uniform(-1, 1, 1000)
        x2 = [2.592158317565918, 2.7595603466033936, 2.77324963,  2.66366911,  2.44840884,  2.11887074,  1.64744055,
         1.01130354,  0.2207378 , -0.66175127, -1.52066994, -2.20688033,
        -2.57222843, -2.50991035, -1.98965192, -1.08026946,  0.05565783,
         1.18824184,  2.07001328,  2.49698734,  2.36334205,  1.69292676,
         0.63696927, -0.56252807, -1.63354337, -2.34136915, -2.54336143,
        -2.21661162, -1.45306516, -0.42664894] # np.random.uniform(-1, 1, 1000)

        def cordic_atan(y: float, x: float, iterations: int = 16) -> float:
            angles = [np.arctan(2**-i) for i in range(iterations)]
            z = 0.0
            x_acc = x
            y_acc = y
            for i in range(iterations):
                s = 1.0 if y_acc < 0 else -1.0
                m = 1
                x_new = x_acc - s * (y_acc * m * (2 ** -i))
                y_new = y_acc + s * (x_acc * m * (2 ** -i))
                z = z - s * angles[i]
                x_acc = x_new
                y_acc = y_new
            return z 
        

        ref = np.arctan2(x1, x2)

        res = np.zeros_like(ref, dtype=np.uint32)

        for i, (x1_val, x2_val) in enumerate(tqdm(zip(x1, x2), total=len(x1))):
            for iter in range(32):
                if iter == 0:
                    print(np.uint32(np.int32(x1_val * (2**28))), np.uint32(np.int32(x2_val * (2**28))))
                    x1_val = np.uint32(np.int32(x1_val * (2**28)))
                    x2_val = np.uint32(np.int32(x2_val * (2**28)))
                    en = True
                else:
                    en = False
                valid, res_val = catan2.forward(en, x1_val, x2_val)

                print(np.uint32(res_val), ref[i] * (2**29))

                if valid:
                    res[i] = res_val

        res = np.int32(res) / (2**29)

        err = np.abs(ref - res)

        print("Average Error: {}".format(np.mean(err)))

        print("Max Error:{} , at input x1, x2: {} ({}), {} ({}), ref: {}, res: {}".format(np.max(err), x1[np.argmax(err)], np.uint32(np.int32(x1[np.argmax(err)] * (2**29))), x2[np.argmax(err)], np.uint32(np.int32(x2[np.argmax(err)] * (2**29))), ref[np.argmax(err)], res[np.argmax(err)]))
        print(cordic_atan(x1[np.argmax(err)], x2[np.argmax(err)], iterations=32))

        print(err)
        
    finally: 
        catan2.terminate()
