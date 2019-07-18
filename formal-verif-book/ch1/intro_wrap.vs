

module intro_wrap (input logic a,b,c,d,clk,rst);

logic o1_1,o2_1,o1_2,o2_2;

intro_sch mod1(a,b,c,d,clk,rst,o1_1,o2_1);
intro_table mod2(a,b,c,d,clk,rst,o1_2,o2_2);

default clocking @(posedge clk); endclocking
default disable iff (rst);

Page6_a1: assert property (o1_1 == o1_2);
Page6_a2: assert property (o2_1 == o2_2);

endmodule
