# ----------------------------------------
#  Copyright (c) 2017 Cadence Design Systems, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright 
#  laws of the United States.
# ----------------------------------------

clear -all

# Analyze design under verification files
set SPEC_RTL_PATH ../rtl/v1
set IMP_RTL_PATH ../rtl/v2
	  
check_sec -setup \
		  -spec_top sanduba \
		  -spec_analyze { -vhdl ${SPEC_RTL_PATH}/sanduba.vhd } \
		  -spec_elaborate_opts { -vhdl } \
		  -imp_top sanduba \
		  -imp_analyze { -vhdl ${IMP_RTL_PATH}/sanduiche.vhd } \
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
 
# Generate verification environment
check_sec -gen

set_prove_time_limit 30s; #A very small prove time limit is used here for quick demo purpose.
check_sec -prove

# Run SignOff
check_sec -signoff

