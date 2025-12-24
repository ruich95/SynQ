import subprocess
import json
from typing import Callable, TypedDict
import os
import signal
import numpy as np
from param import output

def to_number(num_str:str) -> int:
    return int(num_str[num_str.find("\'")+2:])

class NCO(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.fifo_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, step: np.uint32) -> np.uint16:
        if (not self.silent):
            print("input_step: {}".format(step))

        current_state = self.fifo_process.stdout.readline().rstrip("\n")
        current_state = json.loads(current_state)
        if (not self.silent):
            print(current_state)

        step_req = self.fifo_process.stdout.readline().rstrip("\n")
        step_str = str(step) + "\n"
        self.fifo_process.stdin.write(step_str)
        self.fifo_process.stdin.flush()


        output = self.fifo_process.stdout.readline().rstrip("\n")
        output = to_number(output)

        if (not self.silent):
            print(output)
        
        return output


    def terminate(self):
        os.killpg(os.getpgid(self.fifo_process.pid), signal.SIGTERM)

def nco_gen(initial_phase: float = 0,
            lut_size: int        = 2**14,
            phase_acc_width: int = 24) -> Callable[[np.uint32], np.uint16]:

  msk = (2 ** phase_acc_width) - 1
  phase_acc_val = np.uint32(initial_phase * (2 ** phase_acc_width))

  def nco(step: np.uint32) -> np.uint16:
    nonlocal phase_acc_val

    # output the index (higher 14 bits) of a waveform lut
    output        = (phase_acc_val & msk) >> 10
    # next acc value
    phase_acc_val = ((phase_acc_val & msk) + (step & msk)) & msk

    return output

  return nco
        
if __name__ == "__main__":
    try:
        length = 1000
        step = 2**19 + 2345
        impl_output = np.zeros(length, dtype=int)
        ref_output  = np.zeros(length, dtype=int)
        
        nco_impl = NCO("../../build/exec/nco", silent=True)
        nco_ref  = nco_gen()
        for i in range(length):
            impl_output[i] = nco_impl.forward(step)
            ref_output[i] = nco_ref(step)

        for i in range(length):
            if impl_output[i] != ref_output[i]:
                print(f"Mismatch at {i}: impl={impl_output[i]}, ref={ref_output[i]}")
                break
        else:
            print("All outputs match!")
        
    finally: 
        nco_impl.terminate()
