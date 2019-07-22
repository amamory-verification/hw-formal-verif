if {[file isdirectory work]} { vdel -all -lib work }
vlib work
vmap work work

vcom -work work t4.vhd
vcom -work work ../../sim/tb.vhd

vsim -voptargs=+acc=lprn -t ns work.tb

set StdArithNoWarnings 1
set StdVitalGlitchNoWarnings 1

add wave -position insertpoint sim:/tb/sandwich/*

run 545 ns
