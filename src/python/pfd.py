import subprocess
import json
from typing import Callable, TypedDict
import os
import signal
import numpy as np
from param import output

class OutputTy(TypedDict):
    a_ahead_b: bool
    b_ahead_a: bool 

def output2int(output: OutputTy) -> int:
    if output["a_ahead_b"] and (not output["b_ahead_a"]):
        return 1
    elif (not output["a_ahead_b"]) and output["b_ahead_a"]:
        return -1
    else:
        return 0

def to_number(num_str:str) -> int:
    return int(num_str[num_str.find("\'")+2:])

class PFD(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.fifo_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, ref_signal: bool, input_signal: bool) -> OutputTy:
        if (not self.silent):
            print("ref_signal: {}, input_signal: {}".format(ref_signal, input_signal))

        current_state = self.fifo_process.stdout.readline().rstrip("\n")
        current_state = json.loads(current_state)
        if (not self.silent):
            print(current_state)

        ref_req = self.fifo_process.stdout.readline().rstrip("\n")
        ref_sig_str = ("1" if ref_signal else "0") + "\n"
        self.fifo_process.stdin.write(ref_sig_str)
        self.fifo_process.stdin.flush()

        input_req = self.fifo_process.stdout.readline().rstrip("\n")
        input_sig_str = ("1" if input_signal else "0") + "\n"
        self.fifo_process.stdin.write(input_sig_str)
        self.fifo_process.stdin.flush()

        output = self.fifo_process.stdout.readline().rstrip("\n")

        output = json.loads(output)
        output["a_ahead_b"] = True if output["a_ahead_b"] == "1'd1" else False
        output["b_ahead_a"] = True if output["b_ahead_a"] == "1'd1" else False
        output = output2int(output)

        if (not self.silent):
            print(output)
        
        return output


    def terminate(self):
        os.killpg(os.getpgid(self.fifo_process.pid), signal.SIGTERM)

def dff_gen()-> Callable[[bool, bool, bool], bool]:
  prev_out: bool = False
  prev_clk: bool = False

  def dff(input: bool, clear :bool, clk: bool) -> bool:
    nonlocal prev_out
    nonlocal prev_clk
    if clk and (not prev_clk):
      output   = 0 if clear else input
      prev_out = output
      prev_clk = clk
      return output

    prev_clk = clk
    prev_out = 0 if clear else prev_out
    return prev_out

  return dff

def pfd_gen():
  dff_a = dff_gen()
  dff_b = dff_gen()
  prev_clear: bool = False

  def pfd(a: bool, b: bool) -> np.int16:
    nonlocal dff_a
    nonlocal dff_b
    nonlocal prev_clear

    out_a = dff_a(True, prev_clear, a)
    out_b = dff_b(True, prev_clear, b)

    prev_clear = out_a and out_b

    out_a = 1  if out_a else 0
    out_b = -1 if out_b else 0

    output = out_a + out_b
    return output

  return pfd
        
if __name__ == "__main__":
    try:
        length = 50
        random_ref = np.random.randint(0, 2, size=length).astype(bool)
        random_input = np.random.randint(0, 2, size=length).astype(bool)
        impl_output = np.zeros(length, dtype=int)
        ref_output  = np.zeros(length, dtype=int)
        
        pfd_impl = PFD("../../build/exec/pfd", silent=False)
        pfd_ref  = pfd_gen()
        for i in range(length):
            impl_output[i] = pfd_impl.forward(random_ref[i], random_input[i])
            ref_output[i] = pfd_ref(random_ref[i], random_input[i])

        for i in range(length):
            if impl_output[i] != ref_output[i]:
                print(f"Mismatch at {i}: impl={impl_output[i]}, ref={ref_output[i]}")
                break
        else:
            print("All outputs match!")
        
    finally: 
        pfd_impl.terminate()
