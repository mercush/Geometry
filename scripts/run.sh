#!bash
source venv/bin/activate
python Conjecturing/eval.py \
	-n 1 \
	-t 8 \
	--model_type gemini \
	-m "gemini-2.0-flash" \
	-p "."

