

module intro_sch (input logic a,b,c,d,clk,rst, output logic o1,o2);

logic [7:0] n1;

always_comb begin
   n1[0] = a ^ b;
   n1[1] = d | c;
   n1[2] = (a & b) | (c & d);
   n1[3] = b ^ c ^ d;
end

always @(posedge clk) begin  
   n1[4] <= n1[0] ^ n1[1];
   n1[5] <= n1[2] ^ n1[3];
   n1[6] <= n1[1] | n1[3];
   n1[7] <= n1[0] | ~n1[2];
   o1 <= n1[5] ^ n1[6];
   o2 <= n1[4] & n1[7];
end  



default clocking @(posedge clk); endclocking
default disable iff (rst);
genvar i,j,k,l;
generate for (i=0; i<=1; i++) begin :g1 
for (j=0; j<=1; j++) begin :g2 
for (k=0; k<=1; k++) begin :g3 
for (l=0; l<=1; l++) begin :g4 
    // | is cheap way to convert int 1/0 to bit
    c1: cover property ({a,b,c,d} == {|i,|j,|k,|l});
end
end
end
end
endgenerate

endmodule





