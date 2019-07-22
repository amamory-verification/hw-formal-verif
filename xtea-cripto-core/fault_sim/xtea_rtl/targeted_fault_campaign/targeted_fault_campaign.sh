# !/bin/bash

module load genus
module load xcelium/183

xrun -clean
rm -rf xrun.* waves.shm simvision* logs/ fault_db/

xrun -V93 -fault_work fault_db -fault_overwrite -fault_file fault.lst -l logs/fault_elab.log \
-input run_sim.tcl -top tb xtea.vhd xtea_tb.vhd

xrun -R -fault_good_run -fault_tw 7000ns:10000ns -fault_seed 123 -fault_num_nodes 1 \
-fault_work fault_db -input run_good_sim.tcl -l logs/xrun_good.log

xrun -R -fault_sim_run -fault_work fault_db \
-input run_fault_sim.tcl -fault_timeout 2ms -l logs/ncsim_fault.log

xfr -fault_work fault_db -logfile rpt.log
