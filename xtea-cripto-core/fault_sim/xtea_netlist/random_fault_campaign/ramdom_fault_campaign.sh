# !/bin/bash

module load genus
module load xcelium/183

xrun -clean
rm -rf xrun.* waves.shm simvision* logs/ fault_db/

xrun -f file_list.f

fault_type="SA1"
xrun -R -fault_good_run -fault_type ${fault_type} -fault_tw 7000ns:10000ns -fault_seed 123 -fault_num_nodes 2 \
-fault_work fault_db -input run_good_sim.tcl -l logs/xrun_good.log

n_fault=10
for (( i=1; i<=${n_fault}; i++ ))
do
	xrun -R -input run_fault_sim.tcl -fault_sim_run -fault_timeout 2ms \
	-fault_random_id $i -fault_work fault_db -l logs/xrun_fault_$i.log
done

xfr -fault_work fault_db -logfile rpt.log
