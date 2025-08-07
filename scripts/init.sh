#!bash
cd ../..
conda deactivate
uv venv venv
source venv/bin/activate
uv pip install -e .
uv sync
cd src/Geometry
