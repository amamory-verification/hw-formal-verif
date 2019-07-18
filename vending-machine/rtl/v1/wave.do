onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sanduba_tb/sanduba/clock
add wave -noupdate /sanduba_tb/sanduba/reset
add wave -noupdate /sanduba_tb/sanduba/M100
add wave -noupdate /sanduba_tb/sanduba/DEV
add wave -noupdate /sanduba_tb/sanduba/R_bacon
add wave -noupdate /sanduba_tb/sanduba/R_atum
add wave -noupdate /sanduba_tb/sanduba/R_green
add wave -noupdate /sanduba_tb/sanduba/busy
add wave -noupdate /sanduba_tb/sanduba/D100
add wave -noupdate /sanduba_tb/sanduba/BACON
add wave -noupdate /sanduba_tb/sanduba/ATUM
add wave -noupdate /sanduba_tb/sanduba/GREEN
add wave -noupdate /sanduba_tb/sanduba/EA
add wave -noupdate /sanduba_tb/sanduba/PE
add wave -noupdate -radix unsigned /sanduba_tb/sanduba/credito
add wave -noupdate /sanduba_tb/sanduba/erro
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {164847 ps} 0}
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
WaveRestoreZoom {0 ps} {635250 ps}
