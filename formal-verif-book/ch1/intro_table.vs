

module intro_table (input logic a,b,c,d,clk,rst, output logic o1,o2);
logic o1_next, o2_next, o1_ff, o2_ff;

always_comb begin
    case ({a,b,c,d}) 
        4'b0000: {o1_next,o2_next} = 2'b00;
        4'b0001: {o1_next,o2_next} = 2'b01;
        4'b0010: {o1_next,o2_next} = 2'b01;
        4'b0011: {o1_next,o2_next} = 2'b00;
        4'b0100: {o1_next,o2_next} = 2'b01;
        4'b0101: {o1_next,o2_next} = 2'b10;
        4'b0110: {o1_next,o2_next} = 2'b10;
        4'b0111: {o1_next,o2_next} = 2'b10;
        4'b1000: {o1_next,o2_next} = 2'b01;
        4'b1001: {o1_next,o2_next} = 2'b00;
        4'b1010: {o1_next,o2_next} = 2'b00;
        4'b1011: {o1_next,o2_next} = 2'b00;
        4'b1100: {o1_next,o2_next} = 2'b10;
        4'b1101: {o1_next,o2_next} = 2'b10;  // oops, sch is wrong!
        4'b1110: {o1_next,o2_next} = 2'b00;
        4'b1111: {o1_next,o2_next} = 2'b10;
    endcase    
end        

always @(posedge clk) begin
   o1_ff <= o1_next;
   o1 <= o1_ff;
   o2_ff <= o2_next;
   o2 <= o2_ff;
end

endmodule
