//
// Traffic FSM demo
// Created to demo Design Exercise FPV, not claiming to be a good RTL design!
//
// Controllers for a set of traffic lights.  Rules:
// - Exactly one should be non-red at a time
// - Yield to light to your right if no cars at yours & req is in
// - Change to yellow for a time unit before turning red
// - Automatically turn green if 'emergency' signal triggered
//




typedef enum {BOGUS,RED,YELLOW,GREEN,GREEN_EMERGENCY} t_state;
typedef enum {L_RED,L_YELLOW,L_GREEN} t_light;

`ifdef AFTER_SECOND_FIX
parameter t_state RESET_STATE[3:0] = {GREEN,RED,RED,RED};
`endif

module light_fsm(input int index, 
                 input logic clk,rst,
                             cars_waiting, emergency,
                             request_in,global_emergency,yield_in,
                 output logic request_out,yield_out,
                 output t_light light);

t_state cur_state, next_state;

// State transition
`ifndef AFTER_FIRST_FIX
always @(posedge clk) begin
       cur_state <= next_state;
end
`else
`ifndef AFTER_SECOND_FIX
always @(posedge clk or posedge rst) begin
       if (rst) begin
          cur_state <= RED;
       end else begin
          cur_state <= next_state;
       end
end
`else
always @(posedge clk or posedge rst) begin
       if (rst) begin
          cur_state <= RESET_STATE[index];
       end else begin
          cur_state <= next_state;
       end
end
`endif
`endif

// Compute next state
always_comb begin
    // non-emergency case
    case (cur_state) 
        RED   :  next_state = (yield_in) ? GREEN : RED; 
        GREEN :  next_state = (!cars_waiting && request_in) ? YELLOW : GREEN;
        YELLOW:  next_state = RED;
        default: next_state = BOGUS;
    endcase

    // emergency overrides
    if (emergency) begin
        next_state = GREEN_EMERGENCY;
    end else if (cur_state == GREEN_EMERGENCY) begin
        next_state = GREEN;
    end else if (global_emergency) begin
        if (cur_state == GREEN)
           next_state = YELLOW;
    end     
end

// Assign outputs
always_comb begin
    request_out = (cur_state == RED) && cars_waiting;
    yield_out = (cur_state == YELLOW);
    light = (cur_state == RED) ? L_RED :
            (cur_state == YELLOW) ? L_YELLOW :
            L_GREEN;
end


// Properties for this module
default clocking @(posedge clk); endclocking
default disable iff rst;

genvar i;

generate for (i=RED; i<=GREEN_EMERGENCY; i++) begin :g1
    Page131_state1:  cover property (cur_state == i);
end
endgenerate

Page132_a1: assert property (cur_state != BOGUS);

generate for (i=L_RED; i<=L_GREEN; i++) begin :g2
    light1: cover property (light == i);
end
endgenerate

Page132_emergency1:  assert property (emergency |-> ##2 (light==L_GREEN));


`ifdef AFTER_THIRD_FIX
Page141_cover_interesting1:  cover property ((cur_state==GREEN) ##1 (cur_state!=GREEN) ##[1:$] (cur_state==GREEN)); 
Page141_cover_interesting2:  cover property ((cur_state==RED)[*20]);
`endif

`ifdef AFTER_FOURTH_FIX
Page144_liveness1: assert property (((cur_state==RED) && cars_waiting) |-> s_eventually(cur_state==GREEN));
`endif

`ifdef AFTER_FIFTH_FIX
Page142_no_vanishing_cars:  assume property ((cars_waiting && (cur_state == RED)) |=> cars_waiting);
`endif

`ifdef AFTER_SIXTH_FIX
Page146_traffic_gap1: assume property (cars_waiting |=> s_eventually (!cars_waiting));
Page146_traffic_gap2: assume property (!cars_waiting |=> s_eventually (cars_waiting));
`endif

endmodule


module traffic (input logic clk, rst,        
                input logic [3:0] cars_waiting, emergency,
                output t_light lights[3:0]);

logic [3:0] request_out, emergency_out, yield_out;

logic global_emergency;

assign global_emergency = |emergency;

genvar i;
generate for (i=0; i<4; i++) begin : light_inst_loop
    // compiler seems fussy about % op here
    int prev = (i==0) ? 3 : (i-1);
    int next = (i==3) ? 0 : (i+1);
    light_fsm light_inst(i,clk,rst,cars_waiting[i],emergency[i],
                request_out[prev],global_emergency,yield_out[next],
                request_out[i],yield_out[i],
                lights[i]);
end
endgenerate
    
// global properties
default clocking @(posedge clk); endclocking
default disable iff (rst);

`ifndef AFTER_SEVENTH_FIX
Page144_fv_overconstrain_emergency:  assume property (global_emergency == 0);
`endif


int num_greens, num_yellows;
always_comb begin
   num_greens = 0;
   num_yellows = 0;
   for (int i=0;i<4;i++) begin
       if (lights[i] == L_GREEN) num_greens++;
       if (lights[i] == L_YELLOW) num_yellows++;
   end
end

Page132_safety1: assert property ((num_greens + num_yellows) == 1);

Page131_cover_wave: cover property ((lights[3] == L_GREEN) ##[1:4]
                            (lights[2] == L_GREEN) ##[1:4]
                            (lights[1] == L_GREEN) ##[1:4]
                            (lights[0] == L_GREEN));

endmodule

 















