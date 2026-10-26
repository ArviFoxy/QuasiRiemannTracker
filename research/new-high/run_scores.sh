#!/bin/bash
# source-only (default return) and combined (source flow + modified return count lines)
cd "$(dirname "$0")"
python3 score2.py flows/orig.json flows/kL0.82.json flows/cI1.8.json flows/dxi0.05x.json > logs/score_src.log 2>&1
QRH_KL=0.8 QRH_TMAX=3/2 python3 score3.py flows/kL0.8.json > logs/score_comb_kl080.log 2>&1
QRH_KL=0.82 QRH_TMAX=3/2 python3 score3.py flows/kL0.82.json > logs/score_comb_kl082.log 2>&1
QRH_CI=1.8 QRH_TMAX=3/2 python3 score3.py flows/cI1.8.json > logs/score_comb_ci18.log 2>&1
echo DONE >> logs/score_comb_ci18.log
