if {[file  isdirectory work]} {vdel -all -lib work}
vlib work
vmap work work

vcom -work work sanduiche.vhd
vcom -work work tb.vhd

vsim -novopt work.tb

add wave -position insertpoint sim:/tb/sandwich/*

run 545 ns
