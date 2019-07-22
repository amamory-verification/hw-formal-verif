##############################################################
## Logical / Physical synthesis constraints ##
## GAPH/FACIN/PUCRS ##
##############################################################

## DEFINE VARS
set sdc_version 2.0
set_units -capacitance pF -time ns

create_clock -name {clock} -period 0.8 [get_ports {clock}]

## OUTPUTS
set_load 0.000570 [all_outputs]
