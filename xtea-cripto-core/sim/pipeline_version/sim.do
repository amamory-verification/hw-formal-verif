if {[file  isdirectory work]} {vdel -all -lib work}
vlib work
vmap work work

vcom -work work ../../rtl/xtea.vhd

vcom -work work ../../rtl/pipeline_version/flop.vhd 
vcom -work work ../../rtl/pipeline_version/inner_round_stage.vhd 
vcom -work work ../../rtl/pipeline_version/halfround_1.vhd 
vcom -work work ../../rtl/pipeline_version/halfround_2.vhd 
vcom -work work ../../rtl/pipeline_version/kernel_round.vhd
vcom -work work ../../rtl/pipeline_version/pipeline_stage.vhd
vcom -work work ../../rtl/pipeline_version/xtea_pipeline.vhd
vcom -work work ../../rtl/pipeline_version/xtea.vhd

vcom -work work ../../sim/xtea_pipeline_tb.vhd

vsim -novopt work.tb

add wave -position insertpoint sim:/tb/*

run 500 us
