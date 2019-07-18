

typedef enum {READ,WRITE} t_op;

module mem_abstract (input logic[11:0] addr, input logic [63:0] din, 
                     input t_op op,
                     input logic clk,rst, output logic [63:0] dout );

default clocking @(posedge clk); endclocking
default disable iff (rst);

// Make sure inputs valid
valid_op: assume property ((op==WRITE)||(op==READ));

// Full memory, which may create fv complexity!
`ifdef USE_FULL_MEM
    logic [63:0] real_mem[4096:0];

    always @(posedge clk) begin 
           if (op == READ) begin
              dout <= real_mem[addr];
           end else begin
              real_mem[addr] <= din;
              dout <= 0;
           end
    end
`endif

`ifdef USE_ABSTRACT_MEM
// free variables, will define as cut points in FV tool commands
logic [11:0] fv_active_addr[3:0];  // rigid vars for active address
logic [63:0] fv_garbage_data;     // totally free, supplies random data
logic garbage;  // 1 if outputting garbage 

// The abstracted memory
logic [63:0] ABSTRACT_MEM[3:0];

// Keep active_addrs constant during any given run
active_addr_rigid:  assume property (##1 !$changed(fv_active_addr));

always @(posedge clk) begin
    int i;
	for (i=0; i<4; i++) begin
           if ((op==WRITE) && (addr == fv_active_addr[i])) 
		      ABSTRACT_MEM[i] <= din;
	       if ((op==READ) && (addr == fv_active_addr[i]))
               dout <= ABSTRACT_MEM[i];
        end
    if ((op==READ) && (addr != fv_active_addr[0]) 
               && (addr != fv_active_addr[1])
               && (addr != fv_active_addr[2])
               && (addr != fv_active_addr[3])
       ) begin
            dout <= fv_garbage_data;
            garbage <= 1;
         end else begin
            garbage <= 0;
         end
end

// Force use of valid values in proofs
// Be careful, this prevents cases of >4 different mem cells accessed,
// so is somewhat overconstraining.   
Page318_no_garbage:  assume property (garbage == 0);
`endif


// Remember last write op for assertion checks
logic [63:0] last_data;
logic [11:0] last_addr;
always @(posedge clk or posedge rst) begin
       if (rst) begin
          last_data <= 0;
          last_addr <= 0;
       end else begin
          if (op==WRITE) begin
              last_data <= din;
              last_addr <= addr;
          end
       end
end

a1: assert property (((op==READ) && (addr == last_addr) && (addr != 0)) |=> 
                                (dout==last_data));
       
     
endmodule



