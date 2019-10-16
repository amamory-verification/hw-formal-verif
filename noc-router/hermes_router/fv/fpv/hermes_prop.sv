
module hermes_prop (clock, reset, 
	clock_rx, rx, credit_o, data_in,
	clock_tx, tx, credit_i, data_out,
	S_EA, N_EA, E_EA, W_EA, L_EA );

input logic clock, reset; 
input logic [4:0] clock_rx, rx, credit_o;
input  [15:0] data_in[4:0];
input logic [4:0] clock_tx, tx, credit_i;
input logic [15:0] data_out[4:0];
// internal signal - state in int
input [2:0] S_EA,N_EA, E_EA, W_EA, L_EA; 

localparam EAST  = 0;
localparam WEST  = 1;
localparam NORTH = 2;
localparam SOUTH = 3;
localparam LOCAL = 4;

// FIFO FSMs
typedef enum {S_INIT, S_HEADER, S_SENDHEADER, S_PAYLOAD, S_END} fifo_fsm_type;

fifo_fsm_type fifo_fsm[4:0];

assign fifo_fsm[EAST] = fifo_fsm_type'(E_EA);
assign fifo_fsm[WEST] = fifo_fsm_type'(W_EA);
assign fifo_fsm[NORTH] = fifo_fsm_type'(N_EA);
assign fifo_fsm[SOUTH] = fifo_fsm_type'(S_EA);
assign fifo_fsm[LOCAL] = fifo_fsm_type'(L_EA);

// Properties for this module
default clocking @(posedge clock); endclocking
default disable iff reset;

//********************
// ASSUMPTIONS
//********************

// all output ports can receive data
assume_credit_i: assume property (credit_i == 5'b11111);

// implement the input credit assumption, i.e., if there is no credit, rx==0 and data does not change
genvar i;

generate for (i=0; i<=4; i++) begin :g1
    assume_stable_datain: assume property (
	credit_o[i] == 0 |-> ($stable(data_in[i]) && !rx[i])
	);
    assume_rx: assume property (
	credit_o[i] == 0 |-> !rx[i]
	);
end
endgenerate

// assume that only two ports can send data simultaneously
// comment/uncomment these five assumptions accordingly to change the number of parallel data transfers
assume_Erx: assume property (rx[EAST] == 0 );
assume_Wrx: assume property (rx[WEST] == 0 );
assume_Nrx_: assume property (rx[NORTH] == 0 );
//assume_Srx: assume property (rx[SOUTH] == 0 );
//assume_Lrx: assume property (rx[LOCAL] == 0 );

//********************
// COVERPOINTS
//********************

// a cover to check whether the router can send a simple packet.
// in this example the packet has only 3 flits [0x0012, 0x0001, 0x0002] and is sent from local port
cover_prot: cover property (
	##0 credit_o[LOCAL] [->1]
	##1 rx[LOCAL] && data_in[LOCAL] == 16'h0012 ##0 credit_o[LOCAL] [->1] // header
	##1 rx[LOCAL] && data_in[LOCAL] == 16'h0001 ##0 credit_o[LOCAL] [->1] // size
	##1 rx[LOCAL] && data_in[LOCAL] == 16'h0002  // data

);

// check whether the router has sent at least one flit
cover_tx: cover property (tx!=0);
// check, for each port, whether it has sent at least one flit
cover_Etx: cover property (tx[EAST]==1);
cover_Wtx: cover property (tx[WEST]==1);
cover_Ntx: cover property (tx[NORTH]==1);
cover_Stx: cover property (tx[SOUTH]==1);
cover_Ltx: cover property (tx[LOCAL]==1);

// check whether the local input port has received 4 flits
cover_rx4: cover property ((rx[LOCAL] &&  credit_o[LOCAL])[=4]);

// check all states can be reached
genvar j;

generate for (j=0; j<=4; j++) 
begin :cov_fsm
	// does not work :/
	//for(j=S_INIT; j<S_END; j=j+1)
    //begin 
    //  cover_state:  cover property (fifo_fsm[i] == j);
    //end  
    cover_state_init   : cover property (fifo_fsm[j] == S_INIT);
    cover_state_header : cover property (fifo_fsm[j] == S_HEADER);
    cover_state_sendh  : cover property (fifo_fsm[j] == S_SENDHEADER);
    cover_state_payload: cover property (fifo_fsm[j] == S_PAYLOAD);
    cover_state_end    : cover property (fifo_fsm[j] == S_END);
end
endgenerate


//********************
// ASSERTS
//********************

// those two actually detect the trojan, but they take a looong time in the normal router
//cover_show_trojan: cover property (($countones(tx) > 2) [->5]);
//assert_show_trojan: assert property ($countones(tx) <= 2 );


/*
assert_prot: assert property (
	W_fifo_fsm == S_INIT and E_fifo_fsm == S_INIT and N_fifo_fsm == S_INIT and S_fifo_fsm == S_INIT and L_fifo_fsm == S_INIT 
	##1 rx[LOCAL] && data_in[LOCAL] == 16'h0012 ##0 credit_o[LOCAL] [->1] // header
	##1 rx[LOCAL] && data_in[LOCAL] == 16'h0001 ##0 credit_o[LOCAL] [->1] // size
	##1 rx[LOCAL] && data_in[LOCAL] == 16'h0002  // data
	|=> ## 6  // arbitration time
	tx[NORTH] && data_in[NORTH] == 16'h0012 // header
	##1 tx[NORTH] && data_in[NORTH] == 16'h0001 // size
	##1 tx[NORTH] && data_in[NORTH] == 16'h0002 // data
	);
*/

endmodule // hermes_prop
