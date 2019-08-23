onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/reset
add wave -noupdate /tb/clock
add wave -noupdate -divider Input
add wave -noupdate /tb/rx(1)
add wave -noupdate /tb/credit_o(1)
add wave -noupdate /tb/data_in(1)
add wave -noupdate -divider Output
add wave -noupdate /tb/credit_i(2)
add wave -noupdate /tb/tx(2)
add wave -noupdate /tb/data_out(2)
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {40 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {1328 ns}
