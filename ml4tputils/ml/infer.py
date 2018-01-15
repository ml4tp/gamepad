# Inference
import pickle 
from tacst_prep import PosEvalPt

import torch

from ml.poseval.fold_model import PosEvalModel
from ml.poseval.fold_train import PosEvalTrainer, PosEvalInfer

print("Loading tactrs ...")
with open("tactr.pickle", 'rb') as f:
    tactrs = pickle.load(f)

print("Loading poseval dataset ...")
with open("poseval.pickle", 'rb') as f:
    poseval_dataset, tokens_to_idx = pickle.load(f)

# Inference
modelName = "mllogs/model-2018-01-14T181649.869923.params"
model_infer = PosEvalModel(*tokens_to_idx)
model_infer.load_state_dict(torch.load(modelName))
infer = PosEvalInfer(tactrs, model_infer)
infer.infer(poseval_dataset)
