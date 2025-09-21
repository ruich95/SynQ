import json
import subprocess
import os
import signal
import random
import matplotlib.pyplot as plt
import tqdm

mapping = ["P1", "P2"]

nSample = 1000

testMapping = {"input": ["P1"], 
               "output": ["P1"],
               "state":["P1", "P2", "P2"],
               "ops": ["P1", "P2", "P2", "P1", "P1", "P2", "P2", "P1", "P2", "P1", "P1", "P2", "P2"]}

def randomMapping(tac, mapInput, mapOutput):
    mapping = ["P1", "P2"]
    nInput  = len(tac["input"])
    nOutput = len(tac["output"])
    nState  = len(tac["state"])
    nOps    = len(tac["ops"])

    iMap = [mapInput for i in range(nInput)]
    oMap = [mapOutput for i in range(nOutput)]
    sMap = random.choices(mapping, weights=[0.5, 0.5], k=nState)
    opMap = random.choices(mapping, weights=[0.5, 0.5], k=nOps)

    return {"input": iMap, "output": oMap, "state": sMap, "ops": opMap}


class ProfileTAC(object):
    def __init__(self, exec_path: str, silent: bool = True):
        self.profile_process = \
            subprocess.Popen(exec_path, 
                             stdin  = subprocess.PIPE,
                             stdout = subprocess.PIPE, 
                             stderr = subprocess.PIPE,
                             text=True, preexec_fn=os.setsid)
        
        self.silent = silent

    def run(self, jStr: str, mStr:str):
        self.profile_process.stdin.write(jStr)
        self.profile_process.stdin.flush()
        self.profile_process.stdin.write(mStr)
        self.profile_process.stdin.flush()

        output = self.profile_process.stdout.readline().rstrip("\n")
        return json.loads(json.loads(output))

    def terminate(self):
        os.killpg(os.getpgid(self.profile_process.pid), signal.SIGTERM)

def profileTAC(tac:json, mapping:json):
    tacStr = json.dumps(tac)
    mapStr = json.dumps(mapping)
    try:
        process = ProfileTAC(exec_path="../../build/exec/evalTest")
        res = process.run(tacStr+"\n", mapStr+"\n")
    finally:
        process.terminate()
    return res


steps = []
communications = []

with open("../../regularFIR.json", "r") as f:
    tac = json.load(f)

    for i in tqdm.tqdm(range(nSample)):
        mapping = randomMapping(tac, "P1", "P1")
        res = profileTAC(tac, mapping)
        steps.append(res["steps"])
        communications.append(res["communications"])

    with open("res_regular.json", "w") as fRes:
        json.dump({"steps": steps, "communications": communications}, fRes)
    #plt.show()
         