module v_sanduiche (
	clock, 
	reset,
	R_green,
	R_atum,
	R_bacon,
	erro,
	EA,
	PE,
	grana,
	D100,
	busy,
	DEV,
	M100,
	ATUM,
	GREEN,
	BACON,
	overflow
);

	input clock, reset, R_green, R_atum, R_bacon, erro, D100, busy, DEV, M100, ATUM, GREEN, BACON, overflow;
	input [2:0] EA, PE;
	input [2:0] grana;

	typedef enum {Action, SOMA, Sb, Sa, Sg, NULO, DEVOL} state_type;
	state_type state;

	assign state = state_type'(EA);

	default clocking @(posedge clock); endclocking
	default disable iff reset;

	`define single_input(in) ($onehot({R_green, R_atum, R_bacon, DEV, M100, busy}) && in)

	// No input during busy assumption
	property busy_block_verification;
		$rose(busy) |-> (R_bacon == 0) and (R_atum == 0) and (R_green == 0) and (M100 == 0) and (DEV == 0);
	endproperty
	assumption_busy_block: assume property (busy_block_verification);

	//Error condition verification
	property multiple_sandwiches_error;
		((R_green==1 && R_atum==1) || (R_green==1 && R_bacon==1) || (R_bacon==1 && R_atum==1)) |-> erro;
	endproperty
	a_multiple_sandwiches_error: assert property (multiple_sandwiches_error);
	c_multiple_sandwiches_error: cover property (multiple_sandwiches_error);

	//Busy condition verification
	property busy_verification;
		(R_green or R_atum or R_bacon or DEV or M100) and (EA!=Action) |-> busy;
	endproperty
	a_busy_verification: assert property (busy_verification);
	c_busy_verification:  cover property (busy_verification);

	//busy complement condition verification
	property not_busy_verification;
		(EA==Action) |-> !busy;
	endproperty;
	a_not_busy_verification: assert property (not_busy_verification);
	c_not_busy_verification:  cover property (not_busy_verification);

	//All money devolution verification
	property devolution_all_money_verification;
		DEV and (R_bacon==0) and (R_atum==0) and (R_green==0) and (EA==Action) and (grana > 0) |=> ##[1:$](grana==0);
	endproperty
	a_devolution_all_money_verification: assert property (devolution_all_money_verification);
	c_devolution_all_money_verification: cover property (devolution_all_money_verification);       

	//All coin devolution verification
	property devolution_all_coins;
		(EA==DEVOL) && (grana > 1) |=> (grana == ($past(grana) - 1)) and (D100==1);
	endproperty
	a_devolution_all_coins: assert property (devolution_all_coins);
	c_devolution_all_coins: cover property (devolution_all_coins);

	//Last coin devolution verification
	property devolution_last_coin;
		(EA==DEVOL) && (grana == 1) |=> (grana == ($past(grana) - 1)) and (D100==0);
	endproperty
	a_devolution_last_coin: assert property (devolution_last_coin);
	c_devolution_last_coin: cover property (devolution_last_coin);

	//Grana counter verification
	property grana_verification;
		(EA==SOMA) and (overflow==0) and (grana<7) |-> ##1 (grana == ($past(grana) + 1));
	endproperty
	a_grana_verification: assert property (grana_verification);
	c_grana_verification:  cover property (grana_verification);

	//Grana overflow_verification
	property overflow_verification;
		(overflow==1) |-> (grana==$past(grana));
	endproperty
	a_overflow_verification: assert property (overflow_verification);
	c_overflow_verification:  cover property (overflow_verification);

	//Overflow devolution condition verification
	property overflow_devolution_verification;
		(overflow==1) |-> ##1 (D100==1);
	endproperty
	a_overflow_devolution_verification: assert property (overflow_devolution_verification);

	//ATUM output verification
	property atum_verification;
		(grana >= 3 and EA==Action and R_atum and !erro and !M100 and !DEV  and !overflow) |=> ATUM;
	endproperty
	a_atum_verification: assert property (atum_verification);
	c_atum_verification:  cover property (atum_verification);

	//GREEN output verification
	property green_verification;
		(grana >= 2 and EA==Action and R_green and !erro and !M100 and !DEV  and !overflow) |=>  GREEN;
	endproperty
	a_green_verification: assert property (green_verification);
	c_green_verification:  cover property (green_verification);

	//BACON output verification
	property bacon_verification;
		(grana >= 4 and EA==Action and R_bacon and !erro and !M100 and !DEV  and !overflow) |=> BACON;
	endproperty
	a_bacon_verification: assert property (bacon_verification);
	c_bacon_verification:  cover property (bacon_verification);

	//State machine verification
	property action2nulo_transition_verification;
		(DEV==1 and erro==1 and overflow==1 and EA==Action) |-> (PE==NULO) ##1 (EA==NULO);
	endproperty
	a_action2nulo_transition_verification: assert property (action2nulo_transition_verification);
	c_action2nulo_transition_verification:  cover property (action2nulo_transition_verification);

	property action2soma_transition_verification;
		(DEV==0 and erro==0 and overflow==0 and M100==1 and EA==Action) |-> (PE==SOMA) ##1 (EA==SOMA);
	endproperty
	a_action2soma_transition_verification: assert property (action2soma_transition_verification);
	c_action2soma_transition_verification:  cover property (action2soma_transition_verification);

	property action2sb_transition_verification;
		(DEV==0 and erro==0 and overflow==0 and M100==0 and R_bacon==1 and grana >=4 and EA==Action) |-> (PE==Sb) ##1 (EA==Sb);
	endproperty
	a_action2sb_transition_verification: assert property (action2sb_transition_verification);
	c_action2sb_transition_verification:  cover property (action2sb_transition_verification);

	property action2sa_transition_verification;
		(DEV==0 and erro==0 and overflow==0 and M100==0 and R_atum==1 and grana >=3 and EA==Action) |-> (PE==Sa) ##1 (EA==Sa);
	endproperty
	a_action2sa_transition_verification: assert property (action2sa_transition_verification);
	c_action2sa_transition_verification:  cover property (action2sa_transition_verification);

	property action2sg_transition_verification;
		(DEV==0 and erro==0 and overflow==0 and M100==0 and R_green==1 and grana >=2 and EA==Action) |-> (PE==Sg) ##1 (EA==Sg);
	endproperty
	a_action2sg_transition_verification: assert property (action2sg_transition_verification);
	c_action2sg_transition_verification:  cover property (action2sg_transition_verification);

	property soma2action_transition_verification;
		(EA==SOMA) |-> (PE==Action) ##1 (EA==Action);
	endproperty
	a_soma2action_transition_verification: assert property (soma2action_transition_verification);
	c_soma2action_transition_verification:  cover property (soma2action_transition_verification);

	property s2nulo_transition_verification (state_type state);
		(EA==state) |-> (PE==NULO) ##1 (EA==NULO);
	endproperty
	a_sb2nulo_transition_verification: assert property (s2nulo_transition_verification(Sb));
	c_sb2nulo_transition_verification:  cover property (s2nulo_transition_verification(Sb));
	a_sg2nulo_transition_verification: assert property (s2nulo_transition_verification(Sg));
	c_sg2nulo_transition_verification:  cover property (s2nulo_transition_verification(Sg));
	a_sa2nulo_transition_verification: assert property (s2nulo_transition_verification(Sa));
	c_sa2nulo_transition_verification:  cover property (s2nulo_transition_verification(Sa));

	property nulo2action_transition_verification;
		(EA==NULO) and (grana==0) |-> (PE==Action) ##1 (EA==Action);
	endproperty
	a_nulo2action_transition_verification: assert property (nulo2action_transition_verification);
	c_nulo2action_transition_verification:  cover property (nulo2action_transition_verification);

	property nulo2devol_transition_verification;
		(EA==NULO) and (grana>0) |-> (PE==DEVOL) ##1 (EA==DEVOL);
	endproperty
	a_nulo2devol_transition_verification: assert property (nulo2devol_transition_verification);
	c_nulo2devol_transition_verification:  cover property (nulo2devol_transition_verification);

	property devol2nulo_transition_verification;
		(EA==DEVOL) |-> (PE==NULO) ##1 (EA==NULO);
	endproperty
	a_devol2nulo_transition_verification: assert property (devol2nulo_transition_verification);
	c_devol2nulo_transition_verification:  cover property (devol2nulo_transition_verification);

	//Grana decrement verification
	property bacon_decrement_verification;
		(EA==Sb) and (overflow==0) |-> ##1 (grana == ($past(grana) - 4));
	endproperty
	a_bacon_decrement_verification: assert property (bacon_decrement_verification);
	c_bacon_decrement_verification:  cover property (bacon_decrement_verification);

	property atum_decrement_verification;
		(EA==Sa) and (overflow==0) |-> ##1 (grana == ($past(grana) - 3));
	endproperty
	a_atum_decrement_verification: assert property (atum_decrement_verification);
	c_atum_decrement_verification:  cover property (atum_decrement_verification);

	property green_decrement_verification;
		(EA==Sg) and (overflow==0) |-> ##1 (grana == ($past(grana) - 2));
	endproperty
	a_green_decrement_verification: assert property (green_decrement_verification);
	c_green_decrement_verification:  cover property (green_decrement_verification);

	//Changes verification
	property bacon_change_verification;
		(EA==Sb) and (grana > 4) and (overflow==0) |-> ##[1:$](grana==0);
	endproperty
	a_bacon_change_verification: assert property (bacon_change_verification);
	c_bacon_change_verification:  cover property (bacon_change_verification);

	property atum_change_verification;
		(EA==Sa) and (grana > 3) and (overflow==0) |-> ##[1:$](grana==0);
	endproperty
	a_atum_change_verification: assert property (atum_change_verification);
	c_atum_change_verification:  cover property (atum_change_verification);

	property green_change_verification;
		(EA==Sg) and (grana > 2) and (overflow==0) |-> ##[1:$](grana==0);
	endproperty
	a_green_change_verification: assert property (green_change_verification);
	c_green_change_verification:  cover property (green_change_verification);

	// Only one output verification
	property single_output_verification;
		$onehot0({GREEN, ATUM, BACON, D100});
	endproperty; 
	single_output_chk : assert property (single_output_verification);
	a_single_output_verification: assert property (single_output_verification);
	c_single_output_verification:  cover property (single_output_verification);

	// Decrement to a negative value verification
	property invalidTransition;
		(grana == 0) |=> not(grana == 31);
	endproperty 

	// Return money if the value is smaller than the price verification
	property no_money_green_verification;
		`single_input(R_green) && (grana < 2) |=> ##[1:$](grana==0);
	endproperty; 
	a_no_money_green_verification: assert property (no_money_green_verification);
	c_no_money_green_verification:  cover property (no_money_green_verification);

	property no_money_atum_verification;
	   `single_input(R_atum) && (grana < 3) |=> ##[1:$](grana==0);
	endproperty; 
	a_no_money_atum_verification: assert property (no_money_atum_verification);
	c_no_money_atum_verification:  cover property (no_money_atum_verification);

	property no_money_bacon_verification;
		`single_input(R_bacon) && (grana < 4) |=> ##[1:$](grana==0);
	endproperty;
	a_no_money_bacon_verification: assert property (no_money_bacon_verification);
	c_no_money_bacon_verification:  cover property (no_money_bacon_verification);

	// Functional coverage points
	c_R_green:  	   			   cover property (@(posedge clock) (R_green));
	c_R_atum:  	   			   cover property (@(posedge clock) (R_atum));
	c_R_bacon:  	   			   cover property (@(posedge clock) (R_bacon));
	c_erro:  	   			   	   cover property (@(posedge clock) (erro));
	c_grana:  	   			   cover property (@(posedge clock) (grana));
	c_EA:  	   			   	   cover property (@(posedge clock) (EA));
	c_PE:  	   			   	   cover property (@(posedge clock) (PE));
	c_M100:  	   			   	   cover property (@(posedge clock) (M100));
	c_D100:  	   			   	   cover property (@(posedge clock) (D100));
	c_ATUM:  	   			   	   cover property (@(posedge clock) (ATUM));
	c_GREEN: 	   			   	   cover property (@(posedge clock) (GREEN));
	c_BACON: 	   			   	   cover property (@(posedge clock) (BACON));
	c_DEV: 	   			   	   cover property (@(posedge clock) (DEV));
	c_busy: 	   			   	   cover property (@(posedge clock) (busy));
	c_overflow: 	   			   cover property (@(posedge clock) (overflow));

	// State cover 
	property cover_state_action; 
		(EA == Action);
	endproperty;
	c_cover_state_action : cover property (cover_state_action);

	property cover_state_soma; 
		(EA == SOMA);
	endproperty;
	c_cover_state_soma : cover property (cover_state_soma);

	property cover_state_bacon; 
		(EA == Sb);
	endproperty;
	c_cover_state_bacon : cover property (cover_state_bacon);

	property cover_state_atum; 
		(EA == Sa);
	endproperty;
	c_cover_state_atum : cover property (cover_state_atum);

	property cover_state_green; 
		(EA == Sg);
	endproperty;
	c_cover_state_green : cover property (cover_state_green);

	property cover_state_nulo; 
		(EA == NULO);
	endproperty;
	c_cover_state_nulo : cover property (cover_state_nulo); 

	property cover_state_devol; 
		(EA == DEVOL);
	endproperty;
	c_cover_state_devol : cover property (cover_state_devol); 

endmodule // v_sanduiche
