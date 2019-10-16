
clear -all


#set DESIGN RouterInfected

# analyze the design
analyze -vhdl  ../../rtl/HeMPS_defaults.vhd 
analyze -vhdl  ../../rtl/Hermes_buffer.vhd 
analyze -vhdl  ../../rtl/Hermes_crossbar.vhd 
analyze -vhdl  ../../rtl/Hermes_switchcontrol.vhd 
analyze -vhdl  ../../rtl/RouterCC.vhd
analyze -vhdl  ../../rtl/RouterCC_wrapper.vhd

# Analyze property files
analyze -sva bindings.sv hermes_prop.sv 

#set_evaluate_properties_on_formal_reset off
#set_analyze_libunboundsearch true

# elaborate the design, point to the design top level
elaborate -vhdl -top {RouterCC_wrapper}

#connect -list

# Set up Clocks and Resets
# Hermes' SwitchControl module uses both clock edges !!! it requires -both_edges
clock clock -both_edges -factor 1 -phase 1
reset -expression {reset = 1};
#get_reset_info

sanity_check -verbose -analyze all

# get designs statistics
get_design_info


# Prove properties
# 1st pass: Quick validation of properties with default engines
#set_max_trace_length 150
#set_engine_mode {Hp Ht Bm J Q3 U L R B N}
prove -all

#check_assumptions -minimize -conflict -task <embedded>

# Report proof results
report



