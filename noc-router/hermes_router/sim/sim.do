if {[file  isdirectory work]} {vdel -all -lib work}
vlib work
vmap work work

vcom -work work ./HeMPS_defaults.vhd 
vcom -work work ./Hermes_buffer.vhd 
vcom -work work ./Hermes_crossbar.vhd 
vcom -work work ./Hermes_switchcontrol.vhd 
vcom -work work ./RouterCC.vhd

vcom -work work ./tb.vhd

vsim -novopt work.tb

do wave.do

run 10 us
