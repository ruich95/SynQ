import json
import subprocess
import os
import signal
import random
from multiprocessing import Process, Queue, Pool
from functools import partial
import tqdm
from pathlib import Path

mapping = ["P1", "P2"]

nSample = 10000

TACPath = Path("../../fir4.json")

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


def genMapping(tac, mapInput, mapOutput, numMapping):
    def _genMapping():
        for i in range(numMapping):
            yield randomMapping(tac, mapInput, mapOutput)
    
    return _genMapping

with open(TACPath, "r") as f:
    tac = json.load(f)

mapping = {"input": ["P1"], 
           "output": ["P1"],
           "state":["P1", "P2", "P2"],
           "ops": ["P1", "P2", "P2", "P1", "P1", "P2", "P2", "P2", "P1", "P1", "P1", "P2", "P2"]}

print(profileTAC(tac, mapping))

    # _mappings = genMapping(tac, "P1", "P2", nSample)
    # mappings = _mappings()

    # profileFn = partial(profileTAC, tac)

    # with Pool(16) as pool:
    #     res = tqdm.tqdm(pool.imap(profileFn, mappings), total=nSample)
    #     steps = map(lambda x: x["steps"], res)
    #     communications = map(lambda x: x["communications"], res)

    # with open("{}_res.json".format(TACPath.stem), "w") as fRes:
    #     json.dump({"steps": list(steps), "communications": list(communications)}, fRes)

    # for i in tqdm.tqdm(range(nSample//2)):    
    #     mapping1 = randomMapping(tac, "P1", "P2")
    #     mapping2 = randomMapping(tac, "P1", "P2")
        
    #     q1  = Queue()
    #     q2  = Queue()
        

    #     p1 = Process(target=profileTAC, args=(tac, mapping1, q1))
    #     p1.start()

    #     p2 = Process(target=profileTAC, args=(tac, mapping2, q2))
    #     p2.start()

    #     p1.join()
    #     # resRegular = profileTAC(tacRegular, mapping)
    #     res = q1.get()
    #     steps.append(res["steps"])
    #     communications.append(res["communications"])


    #     p2.join()
    #     res = q2.get()
    #     steps.append(res["steps"])
    #     communications.append(res["communications"])



    #plt.show()
         