#!/bin/bash
export PATH=/home/user/leanbuild/lean-4.34.1-linux/bin:$PATH
export LEAN_NUM_THREADS=4
cd /home/user/leanbuild/project
echo "start $(date)"
lake build $(cat ../oai_targets.txt | tr '\n' ' ') 2>&1 | tail -n 200 > ../build_oai.out
echo "rc=${PIPESTATUS[0]} end $(date)"
