set HelpText "\nLoaded JasperGold FSV Utility functions\n"

set HelpText "$HelpText\n  fsv_summary                         - Print FSV results summary (A, P, D)"
proc fsv_summary {{criteria default}} {
	
	set HAS_CHECKER [llength [check_fsv -strobe -list -type c -silent]]
	
	set ALL      [llength [check_fsv -fault -list -silent]]
	set SAFE     [llength [check_fsv -fault -list -class safe -silent]]
	set DANGER   [llength [check_fsv -fault -list -class dangerous -silent]]
	set UNKNOWN  [llength [check_fsv -fault -list -class unknown -silent]]
	set UNPROC   [llength [check_fsv -fault -list -class unprocessed -silent]]
	set OOCOI_FO [llength [check_fsv -fault -list -coi_fo out -silent]]
	set OOCOI_CO [llength [check_fsv -fault -list -coi_co out -silent]]
	set CONST_FO [llength [check_fsv -fault -list -coi_fo {in unprocessed unknown} -constant unactivatable -silent]]
	set CONST_CO [llength [check_fsv -fault -list -coi_co {in unprocessed unknown} -constant unactivatable -silent]]
	set UNACT_FO [llength [check_fsv -fault -list -coi_fo {in unprocessed unknown} -constant {activated unprocessed unknown} -activatability unactivatable -silent]]
	set UNACT_CO [llength [check_fsv -fault -list -coi_co {in unprocessed unknown} -constant {activated unprocessed unknown} -activatability unactivatable -silent]]
	set UNP_FO   [llength [check_fsv -fault -list -coi_fo {in unprocessed unknown} -constant {activated unprocessed unknown} -activatability {activated unprocessed unknown} -propagatability unpropagatable -silent]]
	set UND_CO   [llength [check_fsv -fault -list -coi_co {in unprocessed unknown} -constant {activated unprocessed unknown} -activatability {activated unprocessed unknown} -detectability undetectable -silent]]
	set ADET     [llength [check_fsv -fault -list -coi_fo {in unprocessed unknown} -constant {activated unprocessed unknown} -activatability {activated unprocessed unknown} -propagatability {propagated unknown unprocessed} -always_detected always_detected -silent]]
	set PADET    [llength [check_fsv -fault -list -coi_fo {in unprocessed unknown} -constant {activated unprocessed unknown} -activatability {activated unprocessed unknown} -propagatability {propagated unknown unprocessed} -always_detected {not_always_detected unknown unprocessed} -propagated_always_detected propagated_always_detected -silent]]
		
	switch -glob $criteria {
		A* {
			puts "Unactivatable:  [llength [check_fsv -fault -list -activatability unactivatable -silent]]"
			puts "  Constant:       [llength [check_fsv -fault -list -constant unactivatable -silent]]"
			puts "  Unactivatable:  [llength [check_fsv -fault -list -constant {activated unprocessed unknown} -activatability unactivatable -silent]]"
			puts "Activated:      [llength [check_fsv -fault -list -activatability activated -silent]]"
			puts "Unknown:        [llength [check_fsv -fault -list -activatability unknown -silent]]"
			puts "Unprocessed:    [llength [check_fsv -fault -list -activatability unprocessed -silent]]"
			puts "Total:          $ALL"
		}
		P* {
			puts "Unpropagatable: [llength [check_fsv -fault -list -propagatability unpropagatable -silent]]"
			puts "  COI:            $OOCOI_FO"
			puts "  Constant:       $CONST_FO"
			puts "  Unactivatable:  $UNACT_FO"
			puts "  Unpropagatable: $UNP_FO"
			puts "Propagated:     [llength [check_fsv -fault -list -propagatability propagated -silent]]"
			puts "Unknown:        [llength [check_fsv -fault -list -propagatability unknown -silent]]"
			puts "Unprocessed:    [llength [check_fsv -fault -list -propagatability unprocessed -silent]]"
			puts "Total:          $ALL"
		}
		D* {
			puts "Detected:       [llength [check_fsv -fault -list -detectability detected -silent]]"
			puts "Undetectable:   [llength [check_fsv -fault -list -detectability undetectable -silent]]"
			puts "  COI:            $OOCOI_CO"
			puts "  Constant:       $CONST_CO"
			puts "  Unactivatable:  $UNACT_CO"
			puts "  Unpropagatable: $UNP_FO"
			puts "Unknown:        [llength [check_fsv -fault -list -detectability unknown -silent]]"
			puts "Unprocessed:    [llength [check_fsv -fault -list -detectability unprocessed -silent]]"
			puts "Total:          [llength [check_fsv -fault -list -silent]]"
			puts "\[DC\]: [expr 100 * [llength [check_fsv -fault -list -detectability detected -silent]] / [llength [check_fsv -fault -list -silent]] ]%"
		}
		default {
			puts "Total:          $ALL"
			puts "Safe:           $SAFE \t\[ [expr 100 * $SAFE / $ALL ]% \]"
			puts "  COI:            $OOCOI_FO"
			puts "  Constant:       $CONST_FO"
			puts "  Unactivatable:  $UNACT_FO"
			puts "  Unpropagatable: $UNP_FO"
			if {$HAS_CHECKER} { 
				puts "  Always detect:  $ADET"
				puts "  Prop always d:  $PADET"
			}
			puts "Dangerous:      $DANGER \t\[ [expr 100 * $DANGER/ $ALL ]% \]"
			puts "Unknown:        $UNKNOWN \t\[ [expr 100 * $UNKNOWN/ $ALL ]% \]"
			puts "Unprocessed:    $UNPROC \t\[ [expr 100 * $UNPROC/ $ALL ]% \]"
		}
	}
}


#### Run all faults with FSV prove strategy
set HelpText "$HelpText\n  fsv_prove_strategy                  - Run all faults with FSV prove strategy"
proc fsv_prove_strategy { } {

    puts "Running FSV Proof Strategy"
	 
	set fsv_act     [get_fsv_generate_activatability]
	set fsv_adet    [get_fsv_generate_always_detected]
	set fsv_aprop   [get_fsv_generate_always_propagated] 
	set fsv_det     [get_fsv_generate_detectability] 
	set fsv_prop    [get_fsv_generate_propagatability]
	set fsv_pad     [get_fsv_generate_propagated_always_detected]
	set fsv_engine  [get_fsv_engine_mode]
	
 	set_fsv_generate_activatability off
	set_fsv_generate_always_detected off
	set_fsv_generate_always_propagated off 
	set_fsv_generate_detectability off 
	set_fsv_generate_propagatability off
	set_fsv_generate_propagated_always_detected off

	set_per_property_simplification on
	set_fsv_engine_mode	{Bm Ht Hp Tri}
	
	interrupt -enable {
	
		# 0. activatability checks
		if {$fsv_act == "on"} {
			set fault_list [check_fsv -fault -list -class {unknown unprocessed} -activatability {unknown unprocessed} -silent];
			puts "\nRunning Activatability Checks on [llength $fault_list] faults"
			if {[llength $fault_list]} {
				check_fsv -prove -task [check_fsv -generate -activatability on -regs_mapping_optimization off -max_faults_per_task 0 -id $fault_list]
				interrupt -check
				fsv_summary
			}
		}
	
		# 1. propagatability checks
		
		if {$fsv_prop == "on"} {
			set fault_list [check_fsv -fault -list -class {unknown unprocessed} -propagatability {unknown unprocessed} -silent]; 
			puts "\nRunning Propagatability Checks on [llength $fault_list] faults"
			if {[llength $fault_list]} {
				set task_list [check_fsv -generate -propagatability on -id $fault_list]
				interrupt -check
				check_fsv -prove -task $task_list
				interrupt -check
				fsv_summary
			}
		}
	
		# 2. detectability checks
		if {$fsv_det == "on"} {
			set fault_list [check_fsv -fault -list -class {unknown unprocessed} -detectability {unknown unprocessed} -silent]; 
			puts "\nRunning Detectability Checks on [llength $fault_list] faults"
			if {[llength $fault_list]} {
				set task_list [check_fsv -generate -detectability on -id $fault_list]
				interrupt -check
				check_fsv -prove -task $task_list
				interrupt -check
				fsv_summary
			}
		}
	
		# 3. always detected checks
		if {$fsv_adet == "on"} {
			set fault_list [check_fsv -fault -list -class {unknown unprocessed} -always_detected {unknown unprocessed} -silent]; 
			puts "\nRunning Always-Detected Checks on [llength $fault_list] faults"
			if {[llength $fault_list]} {
				set task_list [check_fsv -generate -always_detected on -id $fault_list]
				interrupt -check
				check_fsv -prove -task $task_list
				interrupt -check
				fsv_summary
			}
		}
	
		# 4. propagated always detected checks
		if {$fsv_pad == "on"} {
			set fault_list [check_fsv -fault -list -class {unknown unprocessed} -propagated_always_detected {unknown unprocessed} -primary -silent]; 
			if {[llength $fault_list]} {
				puts "\nRunning Propagated-Always-Detected Checks on [llength $fault_list] faults"
				set task_list [check_fsv -generate -propagated_always_detected on -id $fault_list]
				interrupt -check
				check_fsv -prove -task $task_list
				interrupt -check
				fsv_summary
			}
		}
		
		# 5. always propagating checks
		if {$fsv_aprop == "on"} {
			set fault_list [check_fsv -fault -list -class {unknown unprocessed} -always_propagated {unknown unprocessed} -silent]; 
			puts "\nRunning Always-Propagated Checks on [llength $fault_list] faults"
			if {[llength $fault_list]} {
				set task_list [check_fsv -generate -always_propagated on -id $fault_list]
				interrupt -check
				check_fsv -prove -task $task_list
				interrupt -check
				fsv_summary
			}
		}
		
	}
	
	set_fsv_generate_activatability             $fsv_act
	set_fsv_generate_always_detected            $fsv_adet
	set_fsv_generate_always_propagated          $fsv_aprop
	set_fsv_generate_detectability              $fsv_det
	set_fsv_generate_propagatability            $fsv_prop
	set_fsv_generate_propagated_always_detected $fsv_pad
	set_fsv_engine_mode  						$fsv_engine
	
	puts "\nFinished FSV Proof Strategy"
	fsv_summary
	
}


set HelpText "$HelpText\n  fsv_sample                          - Return sampled fault list (args: size, seed)"
proc fsv_sample {{size 1} {seed 1} {fault_list ""}} {
	if {$fault_list == ""} {
		set fault_list [check_fsv -fault -list -silent]
	}
	set len [llength $fault_list]
	expr srand($seed)
	set i 0
	set sample ""
	while {$i != $size} {
		lappend sample [lindex $fault_list [expr int(rand()*$len)]]
		incr i
	}
	return $sample
}

puts "$HelpText\n\n"

