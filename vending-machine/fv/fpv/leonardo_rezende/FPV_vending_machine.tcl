# Clear enviroment
clear -all

# analyze the design
analyze -vhdl ../../../rtl/corrected/leonardo/sanduiche.vhd ;

# Analyze property files
analyze -sva bindings.sva sanduiche_PropMod.sv ;

# elaborate the design, point to the design top level
elaborate -vhdl -top {sanduiche}

# Set up Clocks and Resets
clock clock -factor 1 -phase 1
reset -expression {reset = '1'};

# get designs statistics
get_design_info
prove -all

# Report proof results
report 
