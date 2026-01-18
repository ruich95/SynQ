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

class FIRInBuffer(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.buffer_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, en: bool, dat: np.uint32) -> np.uint32:

        current_state = self.buffer_process.stdout.readline().rstrip("\n")
        # current_state = json.loads(current_state)
        # current_state["state"]["count"] = to_number(current_state["state"]["count"])
        # current_state["state"]["content"] = list(map(to_number, current_state["state"]["content"]))
        # current_state["state"]["last"] = list(map(lambda x: True if x == "1'd1" else False, current_state["state"]["last"]))
        # if (not self.silent):
        #     print(current_state)

        en_req = self.buffer_process.stdout.readline().rstrip("\n")
        en_str = ("1" if en else "0") + "\n"
        self.buffer_process.stdin.write(en_str)
        self.buffer_process.stdin.flush()

        dat_req = self.buffer_process.stdout.readline().rstrip("\n")
        dat_str = str(int(dat)) + "\n"
        self.buffer_process.stdin.write(dat_str)
        self.buffer_process.stdin.flush()

        output = self.buffer_process.stdout.readline().rstrip("\n")
        output = to_number(output)
        
        return output

    def terminate(self):
        os.killpg(os.getpgid(self.buffer_process.pid), signal.SIGTERM)


        
if __name__ == "__main__":
    try:
        buffer = FIRInBuffer("../../build/exec/firInBuffer", silent=False)
        
        input_signal = np.zeros(32, dtype=np.uint32)
        input_signal[0] = 123
        en_signal = np.zeros(32, dtype=bool)
        en_signal[0] = True
        output_signal = np.zeros_like(input_signal, dtype=np.uint32)
        for i in range(len(input_signal)):
            output_signal[i] = buffer.forward(en_signal[i], input_signal[i])
        print("Input Signal: ", input_signal)
        print("Output Signal:", output_signal)

        for _ in tqdm(range(100)):
            n_sample = np.random.randint(512, 1024)

            input_signal = np.random.randint(0, 2**17, size=n_sample).astype(np.uint32)
            en_signal = np.random.choice([False, True], size=n_sample, p=[0.3, 0.7])
            en_signal[-31:] = False
            en_signal[-32] = True

            output_signal = np.zeros_like(input_signal, dtype=np.uint32)
            for i in range(len(input_signal)):
                output_signal[i] = buffer.forward(en_signal[i], input_signal[i])
            
            valid_samples = np.array(list(map(lambda x: x[1], filter(lambda x: x[0], zip(en_signal, input_signal)))))
            if not np.array_equal(valid_samples[-32:], output_signal[-32:]):
                print("Mismatch Detected!")
                print("Input Signal: ", input_signal)
                print("Enable Signal:", en_signal)
    finally: 
        buffer.terminate()
