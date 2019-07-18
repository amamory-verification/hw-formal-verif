///////////////////////////////////////////////////////////////
//
// Arbiter example for formal verification book, ch. 3.
//
///////////////////////////////////////////////////////////////


typedef enum logic[2:0] {NOP,FORCE0,FORCE1,FORCE2,FORCE3,ACCESS_OFF,ACCESS_ON} t_opcode;

module arbiter(
	input logic [3:0] req,
	input t_opcode opcode,
	input logic clk, rst,
	output logic [3:0] gnt,
	output logic op_error
);

// Actual RTL code.   
// Creating simplistic & wrong implementation here, so we can view real
// failures when experimenting with FPV tool.
always @(posedge clk or posedge rst) begin
    if (rst) begin
        gnt <= 4'b0;
        op_error <= 0;
    end else begin
        // give everybody who asked a grant
        gnt <= req;   
    end   
end


//
// Validation code, the real point of this chapter!
// 
default clocking @(posedge clk); endclocking
default disable iff (rst);

//
// Simple one-line properties sprinkled throughout chapter
//

Page52_cover_all_at_once: cover property (req[0]&&req[1]&&req[2]&&req[3]);
// cover case where agent 0 req gets granted in 1 cycle
Page70_c1:  cover property (req[0] ##1 gnt[0]);
// cover case where agent 0 req waits >5 cycles
Page70_c2: cover property ((req[0] && !gnt[0])[*5:$] ##1 gnt[0]);
// cover case where we see a FORCE1 arrive sometime while req0 is waiting
Page70_c3: cover property ((opcode==FORCE1) within ((req[0] && !gnt[0])[*1:$]));


Page51_good_opcode: assume property (opcode inside {FORCE0,FORCE1,FORCE2,FORCE3,ACCESS_OFF,ACCESS_ON}) else $error("Illegal opcode.");


safety1:  assert property ($onehot0(gnt)) else $error("Grant to multiple agents!");

// assume after gnt 0, req 0 falls within 5 cycles
Page73_req0_fall_within_5: assume property ($rose(gnt[0]) |=> ##[1:5] $fell(req[0]));

Page51_check_grant:  assert property (!(gnt[0] && !req[0])) 
              else $error("Grant without request for agent 0!");

Page54_gnt_falls: assert property(req[0] ##2 gnt[0] |-> ##1 !gnt[0]);

Page64_good_assert:  assert property (@(posedge clk)
              disable iff (rst)
              (($countones(req)>0) || ($countones(gnt)==0)));

// assert that any request0 is granted within 20 cycles
Page73_gnt0_within_20: assert property  ($rose(req[0]) |-> ##[1:20] gnt[0]);
// assert that any grant on 0 is eventually withdrawn
Page74_gnt0_fall: assert property ($rose(gnt[0]) |-> s_eventually (!gnt[0]));


//
// More complex properties from final sections of chapter
//

parameter t_opcode fv_forces[3:0] = {FORCE3,FORCE2,FORCE1,FORCE0};
genvar i;
generate for (i=0; i<=3;i++) begin: g1
Page80_forcei:  assert property ((opcode == fv_forces[i]) |=>
               (gnt[i] == 1) && ($onehot(gnt))) else
               $error("Force op broken.");
   cover_forcei:  cover property ((opcode==fv_forces[i]) && (gnt[i]==1));
   end
endgenerate

Page80_accessoff: assert property ((opcode == ACCESS_OFF) |=> 
                  (|gnt == 0)) else
                  $error("Incorrect grant: ACCESS_OFF.");

logic fv_validop;
assign fv_validop = (opcode inside  
         {NOP,FORCE0,FORCE1,FORCE2,FORCE3,ACCESS_OFF,ACCESS_ON});
Page80_error0:  assert property (fv_validop |=> !op_error);
Page80_error1:  assert property (!fv_validop |=> op_error);
Page80_cover_nognt: cover property (|gnt == 0);
Page80_cover_err:  cover property (!fv_validop ##1 !op_error);


// Return which bit of a one-hot grant is on
function int fv_which_bit(logic [3:0] gnt);
    assert_some_owner:  assert final ($onehot(gnt));
    for (int i=0; i<4; i++) begin
        if (gnt[i] == 1) begin
            fv_which_bit = i;
        end
    end
endfunction

// Compute next grant for round-robin scheme
function logic [3:0] fv_rr_next(logic [3:0] req,logic [3:0] gnt);
    fv_rr_next = 0;
    for (int i=1; (i<4); i++) begin
        if (req[(fv_which_bit(gnt)+i)%4]) begin
          fv_rr_next[(fv_which_bit(gnt)+i)%4] = 1;
          break;
        end
    end
endfunction

// If nobody has the current grant, treat as if agent 3 had it 
// (so agent 0,1,2 are next in priority).
Page81_rr_nobody: assert property (((opcode == NOP) && 
    (|gnt == 0) && (|req == 1)) |=> (gnt == fv_rr_next(req,4'b1000)))
    else $error("Wrong priority for first grant.");

// If ANDing req and gnt vector gives 0, req is ended.
Page81_rr_next:  assert property (((opcode == NOP) && 
    (|gnt == 1) && (|req == 1) && (|(req&gnt)==4'b0)) |=> (gnt == fv_rr_next(req,gnt))) 
    else $error("Violation of round robin grant policy.");



endmodule







