import subprocess
import re
from typing import Tuple
import json
import os
import signal

def to_number(num_str:str) -> int:
    return int(num_str[num_str.find("\'")+2:])


class AxiSFIFO(object):
    def __init__(self, exec_path: str):
        self.fifo_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
    def forward(self, valid: bool, data: int, rst_n: bool = True):
        current_state = self.fifo_process.stdout.readline().rstrip("\n")
        current_state = json.loads(current_state)
        current_state["state"]["count"] = to_number(current_state["state"]["count"])
        current_state["state"]["content"] = list(map(to_number, current_state["state"]["content"]))
        print(current_state)

        valid_req = self.fifo_process.stdout.readline().rstrip("\n")
        valid_str = ("1" if valid else "0") + "\n"
        self.fifo_process.stdin.write(valid_str)
        self.fifo_process.stdin.flush()

        data_req = self.fifo_process.stdout.readline().rstrip("\n")
        data_str = str(data) + "\n"
        self.fifo_process.stdin.write(data_str)
        self.fifo_process.stdin.flush()

        reset_req = self.fifo_process.stdout.readline().rstrip("\n")
        reset_str = ("1" if rst_n else "0") + "\n"
        self.fifo_process.stdin.write(reset_str)
        self.fifo_process.stdin.flush()

        output = self.fifo_process.stdout.readline().rstrip("\n")
        output = json.loads(output)
        output["valid"] = True if output["valid"] == "1'd1" else False
        output["data"] = to_number(output["data"])
        output["ready"] = True if output["ready"] == "1'd1" else False
        print(output)

    def backward(self, ready: bool):
        ready_req = self.fifo_process.stdout.readline().rstrip("\n")
        ready_str = ("1" if ready else "0") + "\n"
        self.fifo_process.stdin.write(ready_str)
        self.fifo_process.stdin.flush()

    def terminate(self):
        os.killpg(os.getpgid(self.fifo_process.pid), signal.SIGTERM)
        #self.fifo_process.terminate()
        #self.fifo_process.kill()

        
if __name__ == "__main__":
    fifo = AxiSFIFO("../../build/exec/fifo4")
    fifo.forward(True, 9)
    fifo.backward(False)
    fifo.forward(True, 8)
    fifo.backward(False)
    fifo.forward(True, 7)
    fifo.backward(False)
    fifo.forward(True, 6)
    fifo.backward(False)
    fifo.forward(True, 5)
    fifo.terminate()
