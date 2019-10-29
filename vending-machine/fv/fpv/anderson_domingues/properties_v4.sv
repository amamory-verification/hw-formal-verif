//sandwiches macroses
`define GREEN_PRICE 2
`define ATUM_PRICE  3
`define BACON_PRICE 4

//TODO: find corresponded 'length for system verilog
//optionally 2**5
//optionally "11111"
//optionally 21
`define MAX_COUNT 3'h7
`define FSM_TRANSITION_DELAY ##[0:2]

//enumeration for the state machine
typedef enum logic [0:2] { 
	action   = 0, 
	soma     = 1, 
	s_green  = 2,
	s_atum   = 3,
	s_bacon  = 4,
	nulo     = 5,
	devolve  = 6,
	devolve2 = 7} state;

//module interface (entity)
module sanduba_prop(

  //interface
  clock,   reset,
  r_green, green,
  r_atum,  atum,
  r_bacon, bacon,
  dev,     busy,
  m100,    d100,

  //internals
  count, //<<-- number of coins in
  ea,    //<<-- previous state
  pe     //<<-- next state
);

//return true iff the given signal is the only risen among the available input
function int onehot_i (input logic i);
	onehot_i = ($onehot({r_green, r_atum, r_bacon, dev, m100}) && i);
endfunction

//module inputs (:in)
input m100, dev, r_green, r_atum, r_bacon, clock, reset;

//module outputs (:out)
//output d100, green, atum, bacon, busy;
input d100, green, atum, bacon, busy;

//internal signals
input logic [0:2] count;
input state ea, pe;

default clocking @(posedge clock); endclocking //defaults all assertions to posedge
default disable iff reset; //disable everything when reset is risen

//We assume that if device is busy, there can be no input. The device is busy
//when not at the action state. Thus, all input signals are lowered for these
//states.
property p_input;
	@(posedge clock) (ea != action) |-> 
		$countones(r_bacon & r_atum & r_green & dev & m100) == 0;
endproperty
a_p_input : assume property (p_input);

//Check whether the busy signals is risen for all states but action. 
property p_busy; //busy raises when any user input is given
	@(posedge clock) (ea != action) |-> busy;
endproperty;
a_p_busy: assert property (p_busy);

//Check whether the busy signal is NOT risen (lowered) for action state 
property p_busy_compl;
	@(posedge clock) (ea == action) |-> !busy;
endproperty;
a_p_busy_compl : assert property (p_busy_compl);

//Checks whether two or more sandwichs are requested at the same time
property p_bad_input; 
	@(posedge clock) ((ea == action) and (r_bacon + r_green + r_atum) > 1) 
		|=> busy and (ea == nulo);
endproperty;
a_p_bad_input: assert property (p_bad_input);

//Coins must be accounted unless the internal counter have reached their maximum capacity
property p_cred;
	@(posedge clock) (ea == action) and onehot_i(m100) and count < `MAX_COUNT |=>
		`FSM_TRANSITION_DELAY (count == $past(count) + 1) 
		`FSM_TRANSITION_DELAY (ea == action);
endproperty;
a_p_cred : assert property (p_cred);

//If at their maximum capacity, the internal must NOT increment, and exactly one coin must be returned
property p_cred_max;
	@(posedge clock) (ea == action) and onehot_i(m100) and count == `MAX_COUNT |=> 			`FSM_TRANSITION_DELAY (count == $past(count)) 
		`FSM_TRANSITION_DELAY (ea == action);
endproperty;
a_p_cred_max : assert property (p_cred_max);

//When the last coin is to be returned, the next state must be action
property p_dev_eq0;
	@(posedge clock) (ea == devolve) and (count == 1) |-> d100 
		`FSM_TRANSITION_DELAY (count == 0) 
		`FSM_TRANSITION_DELAY (ea == action);
endproperty;
a_p_dev_eq0 : assert property (p_dev_eq0);

//When the counter has more than one coins, these coins must be returned one-by-one,
//always coming back to the devolve state. Also, signal d100 must be risen for each of
//the coins.
property p_dev_gt1;
	@(posedge clock) (ea == devolve) and (count > 1) and (count < `MAX_COUNT) |-> d100
		`FSM_TRANSITION_DELAY (count == $past(count) -1)
		`FSM_TRANSITION_DELAY (ea == devolve);
endproperty;
a_p_dev_gt1 : assert property (p_dev_gt1);

//When the internal has reach its maximum capacity, the next coin must be returned,
//and the internal counter must stay at MAX_COUNT. This is the only available 
//transition from devolve2
property p_dev_max;
	@(posedge clock) (ea == devolve2) and (count == `MAX_COUNT)
		|-> d100 `FSM_TRANSITION_DELAY (ea == action) and (count == `MAX_COUNT);
endproperty;
a_p_dev_max : assert property (p_dev_max);

//Check whether the coin counter is correctly decremented after a sandwich request AND
//the sandwich is properly delivered. Also makes sure the machine goes to the right state
//after delivering the sandwitch, thus not requiring change checking
property p_green_price;
	@(posedge clock) (ea == action) and onehot_i(r_green) and (count >= `GREEN_PRICE) |=> 
		`FSM_TRANSITION_DELAY (ea == s_green)
		`FSM_TRANSITION_DELAY (green) 
		`FSM_TRANSITION_DELAY (count == ($past(count) - `GREEN_PRICE))
		`FSM_TRANSITION_DELAY (count == 0) ? (ea == action) : (ea == devolve);
endproperty
a_p_green_price : assert property (p_green_price);

property p_atum_price;
	@(posedge clock) (ea == action) and onehot_i(r_atum) and (count >= `ATUM_PRICE) |=> 
		`FSM_TRANSITION_DELAY (ea == s_atum)
		`FSM_TRANSITION_DELAY (atum) 
		`FSM_TRANSITION_DELAY (count == ($past(count) - `ATUM_PRICE))
		`FSM_TRANSITION_DELAY (count == 0) ? (ea == action) : (ea == devolve);
endproperty
a_p_atum_price : assert property (p_atum_price);

property p_bacon_price;
	@(posedge clock) (ea == action) and onehot_i(r_bacon) and (count >= `BACON_PRICE) |=> 
		`FSM_TRANSITION_DELAY (ea == s_bacon)
		`FSM_TRANSITION_DELAY (bacon) 
		`FSM_TRANSITION_DELAY (count == ($past(count) - `BACON_PRICE))
		`FSM_TRANSITION_DELAY (count == 0) ? (ea == action) : (ea == devolve);
endproperty
a_p_bacon_price : assert property (p_bacon_price);

//Check whether the machine always proceed to the next state
property p_next_state;
	@(posedge clock) $past(reset) == 0 |-> ea == $past(pe);
endproperty;
a_p_next_state : assert property (p_next_state);

//Check whether the state machine is robust: (1) assert possible next states and (ii) assert
//possible previous states
property p_transition_action; //action never goes to action, and comes from soma, devolve2,
                              //or nulo. MUST skip the first cycle, as $past(ea) cannot be
                              //evaluated there.
	@(posedge clock) ea == action and $past(reset) == 0 |-> 
		pe != action and ( 
			$past(ea) == soma or
			$past(ea) == devolve2 or
			$past(ea) == nulo);
endproperty;
a_p_transition_action : assert property (p_transition_action);

property p_transition_soma; //comes from and goes to action
	@(posedge clock) ea == soma |-> (pe == action and $past(ea) == action);
endproperty;
a_p_transition_soma : assert property (p_transition_soma);

property p_transition_s_green;
	@(posedge clock) ea == s_green |-> (pe == nulo and $past(ea) == action);
endproperty;
a_p_transition_s_green : assert property (p_transition_s_green);

property p_transition_s_atum; //comes from action, goes to nulo
	@(posedge clock) ea == s_atum |-> (pe == nulo and $past(ea) == action);
endproperty;
a_p_transition_s_atum : assert property (p_transition_s_atum);

property p_transition_s_bacon;
	@(posedge clock) ea == s_bacon |-> (pe == nulo and $past(ea) == action);
endproperty;
a_p_transition_s_bacon : assert property (p_transition_s_bacon);

property p_transition_nulo; //comes goes to action or devolve, comes from 
                            //any sandwitch or action
	@(posedge clock) ea == nulo |-> 
		(pe == action or pe == devolve) and (
		$past(ea) == s_atum or
		$past(ea) == s_bacon or 
		$past(ea) == s_green or
		$past(ea) == action or 
		$past(ea) == devolve);
endproperty;
a_p_transition_nulo : assert property (p_transition_nulo);

property p_transition_devolve; //comes from and goes to nulo
	@(posedge clock) ea == devolve |-> 
		(pe == nulo) and ($past(ea) == nulo or $past(ea) == action);
endproperty;
a_p_transition_devolve : assert property (p_transition_devolve);

property p_transition_devolve2; //comes from and goes to soma
	@(posedge clock) ea == devolve2 |-> (pe == action and $past(ea) == action);
endproperty;
a_p_transition_devolve2 : assert property (p_transition_devolve2);

//state cover (defaults to posedge)
`define FIRST_STATE action
`define LAST_STATE devolve2

genvar s;
generate for (s = action; s <= devolve2; s++) begin
	c_ea : cover property (ea == s);
	c_pe : cover property (pe == s);
end endgenerate

//input covers (defaults to posedge)
c_input_r_green  : cover property (r_green);
c_input_r_atum   : cover property (r_atum);
c_input_r_bacon  : cover property (r_bacon);
c_input_dev      : cover property (dev);
c_input_m100     : cover property (m100);

//output covers (defaults to posedge)
c_output_green   : cover property (green);
c_output_atum    : cover property (atum);
c_output_bacon   : cover property (bacon);
c_output_busy    : cover property (busy);
c_output_d100    : cover property (d100);

//count cover (defaults to posedge)
genvar i;
generate for (i = 0; i <= `MAX_COUNT; i++) begin
	c_count : cover property (count == i);
end endgenerate

endmodule /* sanduba_prop */


