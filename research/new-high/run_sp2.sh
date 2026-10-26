#!/bin/bash
cd "$(dirname "$0")"
QRH_KL=0.8 QRH_TMAX=3/2 python3 score_sp.py flows/kL0.8.json 0.058,0.059,0.06 > logs/sp_comb_kl080.log 2>&1
QRH_CI=1.8 QRH_TMAX=3/2 python3 score_sp.py flows/cI1.8.json 0.058,0.059,0.06 > logs/sp_comb_ci18.log 2>&1
echo DONE >> logs/sp_comb_ci18.log
