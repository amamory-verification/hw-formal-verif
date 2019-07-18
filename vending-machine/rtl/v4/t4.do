if {[file isdirectory work]} { vdel -all -lib work }
vlib work
vmap work work

vcom -work work t4.vhd
vcom -work work tb_t4.vhd

vsim -voptargs=+acc=lprn -t ns work.tb

set StdArithNoWarnings 1
set StdVitalGlitchNoWarnings 1

do wave.do

run 75 ns

