clear -all

# analyze the design
analyze -vhdl ../../../rtl/corrected/paulo/sanduba.vhd ;
# Analyze property files
analyze -sva bindings.sva sanduba_assertions_merge.sv ;

#set_evaluate_properties_on_formal_reset off

# elaborate the design, point to the design top level
elaborate -vhdl -top {sanduba_paulo}

# Set up Clocks and Resets
clock clock -factor 1 -phase 1
reset -expression {reset = '1'};
# clock -clear
# clock clock
# reset -clear
# reset reset

# get designs statistics
get_design_info

# this command might be useful for more complex designs
#set_max_trace_length 150
#set_engine_mode {D B3}
prove -all

# Report proof results
report
