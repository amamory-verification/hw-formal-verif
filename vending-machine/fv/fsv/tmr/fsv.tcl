clear -all

set DESIGN sanduiche_tmr2

# Initialize FSV app
check_fsv -init

# FSV utilities
source fsv_utils.tcl

# Read in HDL files
#set RTL_PATH ../designs/fsv_design

analyze -vhdl ./sanduiche.vhd ./sanduiche_tmr2.vhd

# Elaborate and synthesize design
elaborate

# Set up Clocks and Resets
clock clock -factor 1 -phase 1
reset -expression {reset};

# FSV specific settings
set_fsv_clock_cycle_time 200ns
set_fsv_engine_mode {Bm Ht Hp Tri}
# only FO
set_fsv_structural_propagation_analysis fo
set_fsv_structural_constant_propagation_analysis fo

set_fsv_regs_mapping_optimization on
set_fsv_strobe_optimization on

# Specify all internal signals for SA0 and SA1, expecpt for the primary I/O
check_fsv -fault -add [get_design_info -instance $DESIGN -list signal -silent] -type SA0+SA1
# remove faults in the primary inputs/outputs. name is case sensitive
check_fsv -fault -remove -node DEV
check_fsv -fault -remove -node M100
check_fsv -fault -remove -node R_atum
check_fsv -fault -remove -node R_bacon
check_fsv -fault -remove -node R_green
check_fsv -fault -remove -node clock
check_fsv -fault -remove -node reset
check_fsv -fault -remove -node busy
check_fsv -fault -remove -node D100
check_fsv -fault -remove -node GREEN
check_fsv -fault -remove -node ATUM
check_fsv -fault -remove -node BACON
# Specify SEU for all flops
check_fsv -fault -add [get_design_info -instance $DESIGN -list flop -silent] -type SEU

# Specify custom fault target list (all flops with SEU fault, all signals with other faults)
#set out [get_design_info -instance $DESIGN -list signal -silent]
#check_fsv -fault -add [get_design_info -instance $DESIGN -list signal -silent] -type SA0+SA1
#check_fsv -fault -add [get_design_info -instance $DESIGN -list signal -silent] -type SA0+SA1
#check_fsv -fault -add [get_design_info -instance $DESIGN -list flop -silent]   -type SEU -time_window 0:$
#check_fsv -fault -add [get_design_info -instance $DESIGN -list signal -silent] -type SET -time_window 0:$ -set_hold_time 500ns

# Specify the custom strobe list (all checker signals except for can_counter)
#check_fsv -strobe -add [get_design_info -instance $DESIGN -list output -include_hier_path -silent] -functional
#check_fsv -strobe -add [get_design_info -instance $DESIGN -list output -silent] -functional

# Specify the strobe, i.e., where the faults are checked. In this case, only the primary outputs
check_fsv -strobe -add {atum bacon green d100 busy} -functional
#check_fsv -strobe -add {fault} -checker

# structural FSV analysis
check_fsv -structural

# generate FSV properties
check_fsv -generate

# prove FSV properties
#check_fsv -prove -time_limit 1m
check_fsv -prove

# Report FSV results
check_fsv -report -class dangerous
check_fsv -report -force -text ./fsv.rpt

#---[ <DESIGN INFORMATION> ]--------------------------------------------------------------------------------------------------------------------------------------------
#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
# Num  | Flops                         | Latches | Gates      | Nets | Ports | RTL Lines | RTL Instances | Embedded Assumptions | Embedded Assertions | Embedded Covers 
#-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
#[1]     6 (24) (0 property flop bits)   0 (0)     311 (1346)   364    12      220         4               0                      0                     0



#---[ <FAULTS CLASSIFICATION SUMMARY> ]------------------------
#--------------------------------------------------------------
# Num  | Fault Type | Unprocessed | Safe | Dangerous | Unknown 
#--------------------------------------------------------------
#[1]     SA0          0             87     0           0
#[2]     SA1          0             87     0           0
#[3]     SEU          0             24     0           0
#[4]     SET          0             0      0           0
#[5]     MULTI        0             0      0           0
#[6]     Total        0             198    0           0


# FSV Summary
fsv_summary
#
#Total:          198
#Safe:           198 	[ 100% ]
#  COI:            12
#  Constant:       3
#  Unactivatable:  0
#  Unpropagatable: 183
#Dangerous:      0 	[ 0% ]
#Unknown:        0 	[ 0% ]
#Unprocessed:    0 	[ 0% ]

# prove strategy
#fsv_prove_strategy

