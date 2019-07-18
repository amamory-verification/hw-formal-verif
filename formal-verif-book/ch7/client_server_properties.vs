module client_server_properties(
      input logic clk, rst,
      input logic req_valid,
      input logic [7:0] req_opcode,
      input logic [7:0] req_data,
      input logic rsp_valid,
      input logic [7:0] rsp_data);

parameter SERVER_DELAY = 1;

default clocking @(posedge clk); endclocking
default disable iff (rst);


// Infrastructure to enable choosing property directions 
// We default to self-checking mode.
parameter CLIENT_IS_DUT = 0;
parameter SERVER_IS_DUT = 0;
parameter SYSTEM_IS_DUT = 0;
parameter THIS_IS_DUT = 1;
`define CLIENT_ASSERT(name, prop, msg) \
    generate if (CLIENT_IS_DUT | SYSTEM_IS_DUT) begin \
      name: assert property (prop) else $display(msg); \
    end else begin \
      name: assume property (prop) else $display (msg); \
    end \
    endgenerate
`define SERVER_ASSERT(name, prop, msg) \
    generate if (SERVER_IS_DUT | SYSTEM_IS_DUT) begin \
      name: assert property (prop) else $display(msg); \
    end else begin \
      name: assume property (prop) else $display (msg); \
    end \
    endgenerate

// Example properties
`CLIENT_ASSERT(rule_1, req_valid |-> req_opcode != 0,
                  "opcode changed too soon");

`CLIENT_ASSERT(rule_2a, ($rose(req_valid) |=> ( 
          ($stable(req_valid)) [*SERVER_DELAY])), 
          "request changed too soon");
`CLIENT_ASSERT(rule_2b, $rose(req_valid) |=> (
          ($stable(req_opcode))[*SERVER_DELAY]), 
           "request changed too soon");
`CLIENT_ASSERT(rule_2c, $rose(req_valid) |=> (
          ($stable(req_data))[*SERVER_DELAY]), 
          "request changed too soon");
`SERVER_ASSERT(rule_3, $rose(req_valid) |=> ##SERVER_DELAY rsp_valid, "rsp_valid failed to rise");
`SERVER_ASSERT(rule_4, $rose(rsp_valid) |=> $fell(rsp_valid), "rsp_valid held too long.");
`CLIENT_ASSERT(rule_5, $rose(rsp_valid) |=> $fell(req_valid), "req_valid held too long.");

Page195_req_possible: cover property (##1 $rose(req_valid));
Page195_rsp_possible: cover property (##1 $rose(rsp_valid));
Page195_req_done: cover property (##1 $fell(req_valid));

Page196_full_req_with_data: cover property (($rose(req_valid) && (req_data != 0 ) ##SERVER_DELAY $rose(rsp_valid) ##1 $fell(req_valid)));

generate if (THIS_IS_DUT) begin
   self_check1: assert property ($changed(req_opcode) |-> !$past(req_valid));
end endgenerate


endmodule
