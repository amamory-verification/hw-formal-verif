clear -all

check_sec -setup \
        -spec_top sanduiche \
        -spec_analyze_opts { -vhdl ../../../rtl/corrected/leonardo/sanduiche.vhd } \
        -spec_elaborate_opts { -vhdl } \
        -imp_top sanduba \
        -imp_analyze_opts { -vhdl ../../../rtl/corrected/anderson/sanduba.vhd } \
        -imp_elaborate_opts { -vhdl } \
        
# Set up Clocks and Resets
clock clock -factor 1 -phase 1
reset -expression {reset = '1'};

# Instruct SEC to automatically map uninitialized registers
check_sec -auto_map_reset_x_values on

# Map the relevant internal signals for FEV
check_sec -map -spec {{ea(2 DOWNTO 0)}}    -imp {{sanduba_imp.ea(2 DOWNTO 0)}}    
check_sec -map -spec {{grana(2 DOWNTO 0)}} -imp {{sanduba_imp.count(2 DOWNTO 0)}} 

# Define assumptions 

# Check for mapping issues
check_sec -interface

# Generate verification environment
check_sec -gen

#A very small prove time limit is used here for quick demo purpose.
#set_prove_time_limit 30s; 
check_sec -prove


# Run SignOff
check_sec -signoff
