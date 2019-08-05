# ----------------------------------------
#  Copyright (c) 2017 Cadence Design Systems, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright 
#  laws of the United States.
# ----------------------------------------

clear -all

# Analyze design under verification files
set SPEC_RTL_PATH /home/leonardo/Rep/vsfd2/hw-formal-verif/xtea-cripto-core/rtl
set IMP_RTL_PATH /home/leonardo/Rep/vsfd2/hw-formal-verif/xtea-cripto-core/rtl/pipeline_version
	  
check_sec -setup \
		  -spec_top xtea \
		  -spec_analyze { -vhdl ${SPEC_RTL_PATH}/xtea.vhd } \
		  -spec_elaborate_opts { -vhdl } \
		  -imp_top xtea_top \
		  -imp_analyze { -vhdl ${IMP_RTL_PATH}/flop.vhd \
			  			       ${IMP_RTL_PATH}/inner_round_stage.vhd \
			  			       ${IMP_RTL_PATH}/halfround_1.vhd \
			  			       ${IMP_RTL_PATH}/halfround_2.vhd \
							   ${IMP_RTL_PATH}/kernel_round.vhd \
							   ${IMP_RTL_PATH}/pipeline_stage.vhd \
							   ${IMP_RTL_PATH}/xtea_pipeline.vhd \
							   ${IMP_RTL_PATH}/xtea.vhd } \
		  -imp_elaborate_opts { -vhdl } 

# Define clocks 
clock clock

# Define reset
reset reset

# Instruct SEC to automatically map uninitialized registers
check_sec -auto_map_reset_x_values on

# Check for mapping issues
check_sec -interface

# SEC App automatically generates mapping pairs and provides flexibility to
# allows users to manipulate mapping relationships explicitly.
check_sec -map -auto -respect_connections_during_reset -global 
#check_sec -map -spec {{output(63 DOWNTO 0)}} -imp {{xtea_imp.output(63 DOWNTO 0)}} -global -speculative on -spec_delay 0 -imp_delay 50 -spec_condition {output(63 DOWNTO 0)} -spec_condition_delay 0 -imp_condition {output(63 DOWNTO 0) = xtea_imp.output(63 DOWNTO 0)} -imp_condition_delay 50 
 
# Generate verification environment
check_sec -gen

set_prove_time_limit 30s; #A very small prove time limit is used here for quick demo purpose.
check_sec -prove

# Run SignOff
check_sec -signoff

