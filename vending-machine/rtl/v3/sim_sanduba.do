if {[file  isdirectory work]} {vdel -all -lib work}
vlib work
vmap work work

vcom -work work sanduba.vhd
vcom -work work tb_sanduba.vhd

vsim -voptargs=+acc=1prn -t ns work.tb

set StdArithNoWarnings 1
set StdVitalGlitchNoWarnings 1

do wavesandy.do
run 1600 ns

