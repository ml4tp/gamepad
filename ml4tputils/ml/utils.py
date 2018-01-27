import gc
import json
import os
import psutil
import sys
# from time import time
import time
import datetime
import torch
import pandas as pd
import numpy as np

class ResultLogger(object):
    def __init__(self, path, *args, **kwargs):
        self.f_log = open(path, 'w')
        self.f_log.write(json.dumps(kwargs)+'\n')

    def log(self, **kwargs):
        self.f_log.write(json.dumps(kwargs)+'\n')
        self.f_log.flush()

    def close(self):
        self.f_log.close()


def cpuStats():
    print(sys.version)
    print(psutil.cpu_percent())
    print(psutil.virtual_memory())  # physical memory usage
    pid = os.getpid()
    py = psutil.Process(pid)
    memoryUse = py.memory_info()[0] / 2. ** 30  # memory use in GB...I think
    print('memory GB:', memoryUse)


class Timer(object):
    def __enter__(self):
        self.start = time.clock()
        return self

    def __exit__(self, *args):
        self.end = time.clock()
        self.interval = self.end - self.start

# current timestamp
def currTS():
	ts = datetime.datetime.now().isoformat()
	ts = ts.replace(":","")
	return ts


def torch_summarize_df(model, show_weights=True, show_parameters=True):
    """
    Summarizes torch model by showing trainable parameters and weights
    author: wassname
    url: https://gist.github.com/wassname/0fb8f95e4272e6bdd27bd7df386716b7
    license: MIT
    """

    def _torch_summarize(model,
                         parent_name='',
                         show_weights=True,
                         show_parameters=True,
                         level=0):
        data = []
        for key, module in model._modules.items():
            # if it contains layers let call it recursively to get params and weights
            is_container = type(module) in [
                torch.nn.modules.container.Container,
                torch.nn.modules.container.Sequential, torch.nn.Module
            ]
            parameters = sum([np.prod(p.size()) for p in module.parameters()])
            weights = list([tuple(p.size()) for p in module.parameters()])
            if is_container:
                data += _torch_summarize(
                    module,
                    parent_name=parent_name + '=>' + key if parent_name else key,
                    show_weights=show_weights,
                    show_parameters=show_parameters,
                    level=level + 1
                )

            else:
                data.append(
                    dict(
                        key=parent_name + '#' + key,
                        type=type(module).__name__,
                        layer_name=module.__repr__(),
                        parameters=parameters,
                        weights=weights
                    )
                )
        return data

    data = _torch_summarize(
        model,
        parent_name=type(model).__name__,
        show_weights=show_weights,
        show_parameters=show_parameters,
        level=0)
    df = pd.DataFrame(data)
    df = df[['key', 'type', 'parameters', 'weights', 'layer_name']]
    df.index.name = 'layer'
    return df

def flatten(lst):
    return [e for l in lst for e in l]