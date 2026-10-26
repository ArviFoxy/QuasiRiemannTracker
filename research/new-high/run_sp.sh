#!/bin/bash
cd "$(dirname "$0")"
SPS=0.058,0.059,0.06,0.061
python3 score_sp.py flows/orig.json $SPS > logs/sp_orig.log 2>&1
python3 score_sp.py flows/kL0.8.json $SPS > logs/sp_kl080.log 2>&1
python3 score_sp.py flows/cI1.8.json $SPS > logs/sp_ci18.log 2>&1
python3 score_sp.py flows/dxi0.05x.json 0.058,0.06,0.062,0.063 0.039 > logs/sp_ceiling.log 2>&1
echo DONE >> logs/sp_ceiling.log
