onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/sandwich/M100
add wave -noupdate /tb/sandwich/R_bacon
add wave -noupdate /tb/sandwich/R_atum
add wave -noupdate /tb/sandwich/R_green
add wave -noupdate /tb/sandwich/clock
add wave -noupdate /tb/sandwich/reset
add wave -noupdate /tb/sandwich/devo
add wave -noupdate /tb/sandwich/D100
add wave -noupdate /tb/sandwich/Bacon
add wave -noupdate /tb/sandwich/Atum
add wave -noupdate /tb/sandwich/Green
add wave -noupdate /tb/sandwich/Busy
add wave -noupdate /tb/sandwich/EA
add wave -noupdate /tb/sandwich/PE
add wave -noupdate /tb/sandwich/erro
add wave -noupdate /tb/sandwich/count
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {675 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
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
WaveRestoreZoom {0 ns} {1575 ns}
