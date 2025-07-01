import subprocess
import json
from typing import TypedDict
import os
import signal

class OutputTy(TypedDict):
    valid: bool
    data : int 
    last : bool

def to_number(num_str:str) -> int:
    return int(num_str[num_str.find("\'")+2:])

class AxiSFIFO(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.fifo_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def forward(self, rst_n: bool = True) -> OutputTy:

        current_state = self.fifo_process.stdout.readline().rstrip("\n")
        current_state = json.loads(current_state)
        current_state["state"]["count"] = to_number(current_state["state"]["count"])
        current_state["state"]["content"] = list(map(to_number, current_state["state"]["content"]))
        current_state["state"]["last"] = list(map(lambda x: True if x == "1'd1" else False, current_state["state"]["last"]))
        if (not self.silent):
            print(current_state)

        reset_req = self.fifo_process.stdout.readline().rstrip("\n")
        reset_str = ("1" if rst_n else "0") + "\n"
        self.fifo_process.stdin.write(reset_str)
        self.fifo_process.stdin.flush()

        output = self.fifo_process.stdout.readline().rstrip("\n")
        output = json.loads(output)
        output["valid"] = True if output["valid"] == "1'd1" else False
        output["data"]  = to_number(output["data"])
        output["last"]  = True if output["last"] == "1'd1" else False

        if (not self.silent):
            print(output)
        
        return output

    def backward(self, valid: bool, data: int, ready: bool, last: bool = False) -> bool:
        
        data = data if data < 256 else 255
        data = data if data >= 0  else 0

        valid_req = self.fifo_process.stdout.readline().rstrip("\n")
        valid_str = ("1" if valid else "0") + "\n"
        self.fifo_process.stdin.write(valid_str)
        self.fifo_process.stdin.flush()

        data_req = self.fifo_process.stdout.readline().rstrip("\n")
        data_str = str(data) + "\n"
        self.fifo_process.stdin.write(data_str)
        self.fifo_process.stdin.flush()

        last_req = self.fifo_process.stdout.readline().rstrip("\n")
        last_str = ("1" if last else "0") + "\n"
        self.fifo_process.stdin.write(last_str)
        self.fifo_process.stdin.flush()

        ready_req = self.fifo_process.stdout.readline().rstrip("\n")
        ready_str = ("1" if ready else "0") + "\n"
        self.fifo_process.stdin.write(ready_str)
        self.fifo_process.stdin.flush()
        
        ready_str = self.fifo_process.stdout.readline().rstrip("\n")
        ready = json.loads(ready_str)
        ready["ready"] = True if ready["ready"] == "1'd1" else False
        
        if (not self.silent):
            print(ready)
        return ready["ready"]


    def terminate(self):
        os.killpg(os.getpgid(self.fifo_process.pid), signal.SIGTERM)


        
if __name__ == "__main__":
    try:
        fifo = AxiSFIFO("../../build/exec/fifo4", silent=False)
        fifo.forward()
        fifo.backward(True, 9, False)
        fifo.forward()
        fifo.backward(True, 8, False)
        fifo.forward()
        fifo.backward(True, 7, False)
        fifo.forward()
        fifo.backward(True, 6, False, last=True)
        fifo.forward()
        fifo.backward(True, 5, False)
        fifo.forward()
        fifo.backward(True, 5, True)
        fifo.forward()
        fifo.backward(True, 4, True)
        fifo.forward()
        fifo.backward(True, 3, True)
        fifo.forward()
        fifo.backward(True, 2, True)
        fifo.forward()
        fifo.backward(False, 2, True)
        fifo.forward()
        fifo.backward(False, 2, True)
        fifo.forward()
        fifo.backward(False, 2, True)
        fifo.forward()
        fifo.backward(False, 2, True)
        fifo.forward()
        fifo.backward(False, 2, True)
        fifo.forward()
        fifo.backward(True, 1, True)
        fifo.forward()
        fifo.backward(True, 1, True)
    finally: 
        fifo.terminate()
