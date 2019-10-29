//sandwich costs
`define G_COST 2
`define A_COST 3
`define B_COST 4

//time-to-deliver sandwichs (limit of cycles)
`define G_TTD 10
`define A_TTD 10
`define B_TTD 10

`define MAX_COUNT 3'h7
`define FSM_TRANSITION_DELAY ##[0:2]

module sanduba_fsm(	clock_a, reset_a, R_green_a, R_atum_a, R_bacon_a, erro_a, M100_a, DEV_a, D100_a, BACON_a, ATUM_a, GREEN_a, busy_a, EA_a, credito_a);

input clock_a, reset_a, R_green_a, R_atum_a, R_bacon_a, M100_a, DEV_a;
input erro_a;
input [2:0] EA_a;
input [2:0] credito_a;
input D100_a, BACON_a, ATUM_a, GREEN_a, busy_a;

// default disable iff reset_a;
typedef enum {ACTION, SOMA, NULO, SDEV, Sbacon, Satum, Sgreen, DEV_ONE} state_type;

state_type state;

assign state = state_type'(EA_a);

// Check if system gives only a single output at a time:
property singleOutput;
   @(posedge clock_a) $onehot0({GREEN_a, ATUM_a, BACON_a, D100_a});
endproperty;
single_output_chk : assert property (singleOutput);

// If any two or more inputs signals are up the error signal rises:
property erroSignal;
  @(posedge clock_a) (R_bacon_a + R_atum_a + R_green_a + M100_a + DEV_a > 1) |-> (erro_a == 1'b1);
endproperty
erroS: assert property (erroSignal);

// Assume that when busy signal is up, no inputs can be processed:
property busyBlock;
  @(posedge clock_a) (busy_a) |-> (R_bacon_a == 0) and (R_atum_a == 0) and (R_green_a == 0) and (M100_a == 0) and (DEV_a == 0);
endproperty
assume property (busyBlock);

// Assume that a transition from credito_a == 0 to credito_a == 31 is invalid:
property invalidTransition;
  @(posedge clock_a) (credito_a == 0) |=> not(credito_a == `MAX_COUNT);
endproperty
assume property (invalidTransition);

// When a new coin is added to the system, with the right conditions, the machine must go to SOMA state,
// add 1 unit to the credito_a signal and back to ACTION:
property putCOIN;
  @(posedge clock_a) (M100_a == 1'b1) and (EA_a == ACTION) and erro_a == 1'b0 and DEV_a == 1'b0 and (credito_a < `MAX_COUNT) |=> (EA_a == SOMA)
                     and `FSM_TRANSITION_DELAY (credito_a == $past(credito_a) + 1) and `FSM_TRANSITION_DELAY (EA_a == ACTION);
endproperty
pcoin: assert property (putCOIN);

// In properties (chooseATUM, chooseGREEN, chooseBACON), is asserted that with the right conditions,
// when chosen a sandwich the machine must rise the apropriate signal and later decrease credito_a by the value of the sandwich:
property chooseATUM;
  @(posedge clock_a) (EA_a == ACTION) and (R_atum_a) and (credito_a >= `A_COST) and (erro_a == 1'b0) and (DEV_a == 1'b0) and (M100_a == 1'b0) |=>
        `FSM_TRANSITION_DELAY ((EA_a == Satum) and (ATUM_a == 1'b1))
        `FSM_TRANSITION_DELAY ((credito_a == ($past(credito_a) - `A_COST)));
endproperty
catum: assert property (chooseATUM);

property chooseGREEN;
  @(posedge clock_a) (EA_a == ACTION) and (R_green_a) and (credito_a >= `G_COST) and (erro_a == 1'b0) and (DEV_a == 1'b0) and (M100_a == 1'b0) |=>
        `FSM_TRANSITION_DELAY ((EA_a == Sgreen) and (GREEN_a == 1'b1))
        `FSM_TRANSITION_DELAY ((credito_a == ($past(credito_a) - `G_COST)));
endproperty
cgreen: assert property (chooseGREEN);

property chooseBACON;
  @(posedge clock_a) (EA_a == ACTION) and (R_bacon_a) and (credito_a >= `B_COST) and (erro_a == 1'b0) and (DEV_a == 1'b0) and (M100_a == 1'b0) |=>
        `FSM_TRANSITION_DELAY ((EA_a == Sbacon) and (BACON_a == 1'b1))
        `FSM_TRANSITION_DELAY ((credito_a == ($past(credito_a) - `B_COST)));
endproperty
cbacon: assert property (chooseBACON);

// In property moneyOverflow, is asserted that when credito_a is maxed out,  in the next coin input the machine must return a single
// coin and go back to ACTION (ONLY WORKS ON: "sanduba_corrections.vhd", SINCE MUST USE A NEW STATE: DEV_ONE!!!!!!!):
property moneyOverflow;
  @(posedge clock_a) (EA_a == ACTION) and (credito_a >= `MAX_COUNT) and ($rose(M100_a)) and (erro_a == 1'b0) |=> (EA_a == DEV_ONE) and ##1 (EA_a == ACTION);
endproperty
moneyOver: assert property (moneyOverflow);

// In properties (overPriceAtum, overPriceBacon, overPriceGreen), is asserted that when a sandwich is bought and the credit is over the sandwiches price
// the machine must give back the remainig money one coin at a time:
property overPriceAtum;
  @(posedge clock_a) (EA_a == Satum) and (credito_a > `A_COST) |=> ##[0:$] (credito_a == 0);
endproperty
oPriceatum: assert property (overPriceAtum);

property overPriceBacon;
  @(posedge clock_a) (EA_a == Sbacon) and (credito_a > `B_COST) |=> ##[0:$] (credito_a == 0);
endproperty
oPricebacon: assert property (overPriceBacon);

property overPriceGreen;
  @(posedge clock_a) (EA_a == Sgreen) and (credito_a > `A_COST) |=> ##[0:$] (credito_a == 0);
endproperty
oPricegreen: assert property (overPriceGreen);

// Assert that after the sandwich states (Sbacon, Satum and Sgreen) with the right conditions, the next state must be NULO:
property goToNulofromS;
  @(posedge clock_a) (EA_a == Satum) or (EA_a == Sgreen) or (EA_a == Sbacon) and (erro_a == 1'b0) and (DEV_a == 1'b0)
                and  (M100_a == 1'b0) |=> `FSM_TRANSITION_DELAY (EA_a == NULO);
endproperty
gonuloS: assert property (goToNulofromS);

// Assert that the transition from ACTION to NULO occurs only with the right conditions:
property actionToNulo;
  @(posedge clock_a) (EA_a == ACTION) and ((DEV_a == 1'b1) or erro_a == 1'b1) and (M100_a == 1'b0)|=> `FSM_TRANSITION_DELAY (EA_a == NULO);
endproperty
actiontonuloT: assert property (actionToNulo);

// Assert that the transition from NULO to SDEV occurs only with the right conditions and that credito_a is decreased:
property nuloToDEV;
  @(posedge clock_a) (EA_a == NULO) and (credito_a > 0) |=> `FSM_TRANSITION_DELAY (EA_a == SDEV) and ##1(credito_a == ($past(credito_a) - 1));
endproperty
nulotodevT: assert property (nuloToDEV);

// Assert that the transition from SDEV to NULO occurs only with the right conditions:
property DEVToNulo;
  @(posedge clock_a) (EA_a == SDEV) |=> `FSM_TRANSITION_DELAY (EA_a == NULO);
endproperty
devtonuloT: assert property (DEVToNulo);

// Assert that the transition from NULO to ACTION occurs only with the right conditions:
property nuloToAction;
  @(posedge clock_a) (EA_a == NULO) and (credito_a == 0) |=> `FSM_TRANSITION_DELAY (EA_a == ACTION);
endproperty

// In properties (noMoneyATUM, noMoneyGREEN, noMoneyBACON), is asserted that when there is not enough money for a sandwich
// but it is requested anyway, the machine must go to NULO state:
property noMoneyATUM;
  @(posedge clock_a) (EA_a == ACTION) and (R_atum_a) and (credito_a < `A_COST) and (erro_a == 1'b0) and (DEV_a == 1'b0)
                and  (M100_a == 1'b0) |=> `FSM_TRANSITION_DELAY ((EA_a == NULO) and (ATUM_a == 1'b0));
endproperty
noMoneyA: assert property (noMoneyATUM);

property noMoneyGREEN;
  @(posedge clock_a) (EA_a == ACTION) and (R_green_a) and (credito_a < `G_COST) and (erro_a == 1'b0) and (DEV_a == 1'b0)
                and  (M100_a == 1'b0) |=> `FSM_TRANSITION_DELAY ((EA_a == NULO) and (GREEN_a == 1'b0));
endproperty
noMoneyG: assert property (noMoneyGREEN);

property noMoneyBACON;
  @(posedge clock_a) (EA_a == ACTION) and (R_bacon_a) and (credito_a < `B_COST) and (erro_a == 1'b0) and (DEV_a == 1'b0)
                and  (M100_a == 1'b0) |=> `FSM_TRANSITION_DELAY ((EA_a == NULO) and (BACON_a == 1'b0));
endproperty
noMoneyB: assert property (noMoneyBACON);

// Check if In ACTION state occurs a wrong transition (This cover must not pass!!!!):
property wrongTransitionInAction;
  @(posedge clock_a) ((EA_a == ACTION) and ((R_bacon_a == 1'b1) or (R_bacon_a == 1'b0)) and (credito_a < 4) |=> (`FSM_TRANSITION_DELAY EA_a == Sbacon)) or
                     ((EA_a == ACTION) and ((R_atum_a == 1'b1) or (R_atum_a == 1'b0)) and (credito_a < 3) |=> (`FSM_TRANSITION_DELAY EA_a == Satum)) or
                     ((EA_a == ACTION) and ((R_green_a == 1'b1) or (R_green_a == 1'b0)) and (credito_a < 2) |=> (`FSM_TRANSITION_DELAY EA_a == Sgreen));
endproperty
wrong: cover property (wrongTransitionInAction);

// When the machine is in any state other then ACTION, busy is up:
property busyStateONE;
  @(posedge clock_a) (busy_a == 1'b1) |-> not(EA_a == ACTION);
endproperty
bStateO: assert property (busyStateONE);

// When the machine is in ACTION, busy is down:
property busyStateZERO;
  @(posedge clock_a) (busy_a == 1'b0) |-> (EA_a == ACTION);
endproperty
bStateZ: assert property (busyStateZERO);

// All money devolution verification when dev button is pressed:
property PressDEV;
  @(posedge clock_a) (EA_a == ACTION) and (DEV_a) |=> ##[1:$](credito_a == 0);
endproperty
pressDevo: assert property (PressDEV);

//Coin devolution signal verification:
property devCoinVerif;
  @(posedge clock_a) DEV_a and (EA_a == ACTION) && (credito_a > 0) |=> `FSM_TRANSITION_DELAY (EA_a == NULO) and (D100_a == 1);
endproperty
coinVerif: assert property (devCoinVerif);

//Last coin devolution signal verification:
property lastCoinVerif;
  @(posedge clock_a) (EA_a == SDEV) and (credito_a == 1) |=> (credito_a == ($past(credito_a) - 1)) and (D100_a == 0);
endproperty
lastCoin: assert property (lastCoinVerif);


//Coverage of each one of the states (ACTION, SOMA, Sgreen, Satum, Sbacon, NULO, SDEV, DEV_ONE):
property stateCoverage(state_type st);
	@(posedge clock_a) (EA_a == st);
endproperty;
stateCoverageAct : cover property (stateCoverage(ACTION));
stateCoverageSoma : cover property (stateCoverage(SOMA));
stateCoverageGreen : cover property (stateCoverage(Sgreen));
stateCoverageAtum : cover property (stateCoverage(Satum));
stateCoverageBacon : cover property (stateCoverage(Sbacon));
stateCoverageNulo : cover property (stateCoverage(NULO));
stateCoverageSdev : cover property (stateCoverage(SDEV));
stateCoverageDevOne : cover property (stateCoverage(DEV_ONE));

// Functional coverage points:
c_R_green:  	   			   cover property (@(posedge clock_a) (R_green_a));
c_R_atum:  	   			   cover property (@(posedge clock_a) (R_atum_a));
c_R_bacon:  	   			   cover property (@(posedge clock_a) (R_bacon_a));
c_erro:  	   			   	   cover property (@(posedge clock_a) (erro_a));
c_grana:  	   			   cover property (@(posedge clock_a) (credito_a));
c_EA:  	   			   	   cover property (@(posedge clock_a) (EA_a));
c_M100:  	   			   	   cover property (@(posedge clock_a) (M100_a));
c_D100:  	   			   	   cover property (@(posedge clock_a) (D100_a));
c_ATUM:  	   			   	   cover property (@(posedge clock_a) (ATUM_a));
c_GREEN: 	   			   	   cover property (@(posedge clock_a) (GREEN_a));
c_BACON: 	   			   	   cover property (@(posedge clock_a) (BACON_a));
c_busy: 	   			   	   cover property (@(posedge clock_a) (busy_a));


endmodule
