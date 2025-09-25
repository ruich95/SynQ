import json
import subprocess
import os
import signal
import random
from multiprocessing import Process, Queue
import tqdm
from pathlib import Path

mapping = ["P1", "P2"]

nSample = 10000

regularTACPath = Path("../../balancedFIR128_75.json")
balancedTACPath = Path("../../balancedFIR128_110.json")

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

def profileTAC(tac:json, mapping:json, queue):
    tacStr = json.dumps(tac)
    mapStr = json.dumps(mapping)
    try:
        process = ProfileTAC(exec_path="../../build/exec/evalTest")
        res = process.run(tacStr+"\n", mapStr+"\n")
    finally:
        process.terminate()
    
    queue.put(res)


stepsRegular = []
stepsBalanced = []
communicationsRegular = []
communicationsBalanced = []

with open(regularTACPath, "r") as fRegular:
    tacRegular = json.load(fRegular)
    
with open(balancedTACPath, "r") as fRegular:
    tacBalanced = json.load(fRegular)

    for i in tqdm.tqdm(range(nSample//2)):
        mapping1 = randomMapping(tacRegular, "P1", "P2")
        mapping2 = randomMapping(tacRegular, "P1", "P2")
        
        qRegular1  = Queue()
        qBalanced1 = Queue()
        qRegular2  = Queue()
        qBalanced2 = Queue()

        pRegular1 = Process(target=profileTAC, args=(tacRegular, mapping1, qRegular1))
        pRegular1.start()

        pRegular2 = Process(target=profileTAC, args=(tacRegular, mapping2, qRegular2))
        pRegular2.start()

        pBalanced1 = Process(target=profileTAC, args=(tacBalanced, mapping1, qBalanced1))
        pBalanced1.start()

        pBalanced2 = Process(target=profileTAC, args=(tacBalanced, mapping2, qBalanced2))
        pBalanced2.start()

        pRegular1.join()
        # resRegular = profileTAC(tacRegular, mapping)
        resRegular = qRegular1.get()
        stepsRegular.append(resRegular["steps"])
        communicationsRegular.append(resRegular["communications"])

        pBalanced1.join()
        # resBalanced = profileTAC(tacBalanced, mapping) 
        resBalanced = qBalanced1.get()
        stepsBalanced.append(resBalanced["steps"])
        communicationsBalanced.append(resBalanced["communications"])

        pRegular2.join()
        resRegular = qRegular2.get()
        stepsRegular.append(resRegular["steps"])
        communicationsRegular.append(resRegular["communications"])

        pBalanced2.join()
        resBalanced = qBalanced2.get()
        stepsBalanced.append(resBalanced["steps"])
        communicationsBalanced.append(resBalanced["communications"])

with open("{}_res.json".format(regularTACPath.stem), "w") as fRes:
    json.dump({"steps": stepsRegular, "communications": communicationsRegular}, fRes)

with open("{}_res.json".format(balancedTACPath.stem), "w") as fRes:
    json.dump({"steps": stepsBalanced, "communications": communicationsBalanced}, fRes)
    #plt.show()
         