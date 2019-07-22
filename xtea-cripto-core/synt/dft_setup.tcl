##########################################################################################
# 1) TOP LEVEL DFT SETUP (DFT design attributes & scan_chain, test clock definition ...) #
##########################################################################################

## Set the DFT scan FF style for scan replacement {muxed_scan|clocked_lssd_scan}. Muxed scan is the most commonly used
set_db dft_scan_style muxed_scan 

## Prefix is added to name of DFT logic that is inserted
# prefix of the scan chain names, otherwise the pattern 'DFT_sdi_<X>' and 'DFT_sdo_<X>' is adopted, where X is 1 to N-number of scan chains
#set_attribute dft_prefix scan_
set_db dft_prefix chip_ 

## This attribute tells RC to trace clock lines to automatically find the top-level clocks
## and automatically assign them as test clocks
set_db dft_identify_top_level_test_clocks true
## This attribute tells RC to trace async set/reset pins of FF's back to top-level pins
## and automatically assign them as test signals
set_db dft_identify_test_signals true

## This attribute tell RC whether to treat outputs of clock gating elements as different
## test clock domains as the clock that fed the gating.
set_db dft_identify_internal_test_clocks false
## This attribute controls mapping of non-scan flops to scan FF's for functional purposes
set_db use_scan_seqs_for_non_dft false

# Specify whether to allow mixing of rising and falling edge-triggered scan flip-flops from the same test-clock domain in the same scan chain:
# By default, the scan configuration engine creates a different scan chain for scan flip-flops triggered by the rising and falling edges of the same test clock
#set_attribute dft_mix_clock_edges_in_scan_chain {true | false} top_design
set_db [get_design ${DESIGN_TOP}] .dft_mix_clock_edges_in_scan_chains false

## Definition of a DFT pin used for Scan Shift. It is also possible to share test and functional pins in order to reduce the pin count
## define_dft shift_enable -name <shiftEnableObject> -active <high|low> <portOrpin> [-create_port]
define_dft shift_enable -name se -create_port -active high chip_scan_se

## Definition of a DFT pin used as a Test Mode control
## define_dft test_mode -name <testModeObject> -active <high|low> <portOrpin> [-create_port] [-shared_in]
define_dft test_mode -name tm -create_port -active high chip_scan_tm


#######################################################################################################
## 2) CREATING SCAN CHAINS
## scan chains can be created automatically using '-auto_create_chains' or manually 
#######################################################################################################
check_dft_rules

#########################################
#### automatic scan generation mode #####
# replace normal flip-flops by scan flip-flops
replace_scan
# check scan insertion before actually insert it into your design
connect_scan_chains -auto_create_chains -preview -pack
# perform scan insertion
connect_scan_chains -auto_create_chains

#######################################################################################################
## 3) INCREMENTAL SYNTHESIS
#######################################################################################################
puts "###############################################################"
puts "################ Incremental Synthesis (Post DfT) #############"
puts "###############################################################"
synthesize -to_mapped -eff high -incr

#####################################################################################################
## 4) REPORTING AND EXPORTING TEST RELATED INFO
#####################################################################################################
puts "########### Reporting and Exporting Test Info ###########"
## Check DFT rules again
check_dft_rules -advanced

## Report out the scan chains
report dft_chains > ${OUTPUTS_PATH}/dft/${DESIGN_TOP}_dft_chains.rpt
report dft_setup > ${OUTPUTS_PATH}/dft/${DESIGN_TOP}_dft_setup.rpt

puts "############ Exporting the Design to Encounter Test ###########"

# scan chain info
write_scandef > ${OUTPUTS_PATH}/dft/${DESIGN_TOP}.scandef

# Creating an Interface File for ATPG Tool
write_atpg -stil > ${OUTPUTS_PATH}/dft/${DESIGN_TOP}_atpg.stil

# these steps are required to perform further verification using incisive simulator for scan chains and test patterns verification
write_et_atpg -library ${LIB_FILES} -directory ${OUTPUTS_PATH}/dft/et_atpg -ncsim_library ${LIB_FILES}

# after synthesis, run the following commands to verify the DfT insertion
# $ et -c outputs/dft/et_atpg/runet.atpg
# $ outputs/dft/et_atpg/run_fullscan_sim
