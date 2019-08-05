-top tb -smartorder -v93 -relax -libverbose 
-work work -access +cwr -timescale 1ns/1ps
-gui
../../rtl/xtea.vhd
../../rtl/pipeline_version/flop.vhd 
../../rtl/pipeline_version/inner_round_stage.vhd 
../../rtl/pipeline_version/halfround_1.vhd 
../../rtl/pipeline_version/halfround_2.vhd 
../../rtl/pipeline_version/kernel_round.vhd
../../rtl/pipeline_version/pipeline_stage.vhd
../../rtl/pipeline_version/xtea_pipeline.vhd
../../rtl/pipeline_version/xtea.vhd
../../sim/xtea_pipeline_tb.vhd
