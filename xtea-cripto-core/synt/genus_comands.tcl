##############################################################
##              Logical synthesis commands                  ##
##                   GAPH/FACIN/PUCRS                       ##
##############################################################

## 1) load synthesis configuration, read description and elaborate design 
include load_genus.tcl
read_hdl -vhdl ${DESIGN_TOP}.vhd
elaborate ${DESIGN_TOP}

## 2) read constraints
read_sdc ./constraints.sdc

## 3) synthesize to mapped
synthesize -to_mapped -eff high -no_incr
syn_opt

## 4) build physical synthesis environment
write_design -encounter -basename ${OUTPUTS_PATH}/layout/${DESIGN_TOP}

# Generate sdc pos synthesis
write_sdc > ${OUTPUTS_PATH}/${DESIGN_TOP}.sdc
						
# Generate sdf pos synthesis
write_sdf > ${OUTPUTS_PATH}/${DESIGN_TOP}.sdf

## 5) post synthesis reports
report area   > ${REPORTS_PATH}/${DESIGN_TOP}_area.txt
report timing > ${REPORTS_PATH}/${DESIGN_TOP}_timing.txt
report power  > ${REPORTS_PATH}/${DESIGN_TOP}_power.txt
report nets   > ${REPORTS_PATH}/${DESIGN_TOP}_nets.txt

## 6) dft
source dft_setup.tcl


