#Stuck-at faults
fault -inject -time 7000ns -type sa0 tb.core.output[63]
fault -inject -time 8000ns -type sa0 tb.core.v0[0]
fault -inject -time 8000ns -type sa0 tb.core.v0[1]
fault -inject -time 8000ns -type sa0 tb.core.v0[2]
fault -inject -time 8000ns -type sa0 tb.core.v0[3]
fault -inject -time 8000ns -type sa1 tb.core.output[63]
fault -inject -time 9000ns -type sa1 tb.core.v0[0]
fault -inject -time 9000ns -type sa1 tb.core.v0[1]
fault -inject -time 9000ns -type sa1 tb.core.v0[2]
fault -inject -time 9000ns -type sa1 tb.core.v0[3]

#SEU faults
fault -inject -time 7000ns -type seu tb.core.output[62]
fault -inject -time 8000ns -type seu tb.core.v1[0]
fault -inject -time 8000ns -type seu tb.core.v1[1]
fault -inject -time 8000ns -type seu tb.core.v1[2]
fault -inject -time 8000ns -type seu tb.core.v1[3]
fault -inject -time 8000ns -type seu tb.core.output[61]
fault -inject -time 9000ns -type seu tb.core.v1[4]
fault -inject -time 9000ns -type seu tb.core.v1[5]
fault -inject -time 9000ns -type seu tb.core.v1[6]
fault -inject -time 9000ns -type seu tb.core.v1[7]


#SET
fault -inject -time 7000ns -type set+10ns tb.core.output[60]
fault -inject -time 8000ns -type set+10ns tb.core.v0[4]
fault -inject -time 8000ns -type set+10ns tb.core.v0[5]
fault -inject -time 8000ns -type set+10ns tb.core.v0[6]
fault -inject -time 8000ns -type set+10ns tb.core.v0[7]
fault -inject -time 8000ns -type set+10ns tb.core.output[59]
fault -inject -time 9000ns -type set+10ns tb.core.v1[8]
fault -inject -time 9000ns -type set+10ns tb.core.v1[9]
fault -inject -time 9000ns -type set+10ns tb.core.v1[10]
fault -inject -time 9000ns -type set+10ns tb.core.v1[11]

#Run simulation until all faults be injected
fault -stop_severity 2
run

exit
