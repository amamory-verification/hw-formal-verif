if {[file  isdirectory work]} {vdel -all -lib work}
vlib work
vmap work work

vcom -work work ../rtl/HeMPS_defaults.vhd 
vcom -work work ../rtl/Hermes_buffer.vhd 
vcom -work work ../rtl/Hermes_crossbar.vhd 
vcom -work work ../rtl/Hermes_switchcontrol.vhd 
vcom -work work ../rtl/RouterCC.vhd

vcom -work work ./tb.vhd

vsim -novopt work.tb

do wave.do
do shutup.do

run 10 us
