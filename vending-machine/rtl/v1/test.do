vcom -work work sanduba.vhd
vcom -work work sanduba_tb.vhd
vsim -novopt work.sanduba_tb
add wave -position insertpoint sim:/sanduba_tb/sanduba/*
run 545 ns
