#!/bin/bash
cd "$(dirname "$0")"
QRH_CI=1.8 QRH_TMAX=3/2 python3 score_h.py flows/cI1.8.json 0.800,0.802,0.806,0.808 > logs/h_comb_ci18.log 2>&1
QRH_KL=0.8 QRH_TMAX=3/2 python3 score_h.py flows/kL0.8.json 0.800,0.802,0.806,0.808 > logs/h_comb_kl080.log 2>&1
python3 score_h.py flows/dxi0.05x.json 0.802,0.806 0.063 > logs/h_ceiling.log 2>&1
echo DONE >> logs/h_ceiling.log
