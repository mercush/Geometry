#!/bin/bash
source venv/bin/activate
python Conjecturing/eval.py \
	--n_trials 50 \
	--tensor_parallel_size 1 \
	--model_type featherless \
	--model_name "AI-MO/Kimina-Prover-72B" \
	--project_dir "." \
	--with_cot False \
	--max_tokens 250
deactivate
