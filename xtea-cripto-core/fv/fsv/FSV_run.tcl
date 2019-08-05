# ----------------------------------------
#  Copyright (c) 2018 Cadence Design Systems, Inc. All Rights
#  Reserved.  Unpublished -- rights reserved under the copyright 
#  laws of the United States.
# ----------------------------------------

# Initialize FSV app
check_fsv -init

# FSV utilities
source fsv_utils.tcl

# Read in HDL files
set RTL_PATH ./

analyze -vhdl /home/leonardo/Rep/vsfd2/hw-formal-verif/xtea-cripto-core/rtl/xtea.vhd

# Elaborate and synthesize design
elaborate

# Initialize design
clock -infer
reset reset

# FSV specific settings
set_fsv_clock_cycle_time 200ns
set_fsv_engine_mode {Bm Ht Hp Tri}
set_fsv_regs_mapping_optimization on
set_fsv_strobe_optimization on

# Specify custom fault target list (all flops with SEU fault, all signals with other faults)
set out [get_design_info -instance xtea -list signal -silent]
check_fsv -fault -add [get_design_info -instance xtea -list signal -silent] -type SA0+SA1
check_fsv -fault -add [get_design_info -instance xtea -list flop -silent]   -type SEU -time_window 0:$
check_fsv -fault -add [get_design_info -instance xtea -list signal -silent] -type SET -time_window 0:$ -set_hold_time 500ns

# Specify the custom strobe list (all checker signals except for can_counter)
check_fsv -strobe -add [get_design_info -instance xtea -list output -include_hier_path -silent] -functional

# structural FSV analysis
check_fsv -structural

# generate FSV properties
check_fsv -generate

# prove FSV properties
check_fsv -prove -time_limit 1m

# Report FSV results
check_fsv -report -class dangerous
check_fsv -report -force -text ./fsv.rpt

# FSV Summary
fsv_summary
