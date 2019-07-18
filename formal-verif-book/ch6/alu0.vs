//
// Sample ALU for demonstrating STE
//

`include "macros.vs"

typedef bit node;

// uopcode definitions
parameter OPAND = 5'b00000;
parameter OPOR  = 5'b00001;
parameter OPXOR = 5'b00010;
//
parameter OPADD = 5'b01000;
parameter OPSUB = 5'b01001;
parameter OPMUL = 5'b01010;
parameter OPCMP = 5'b01011;
//

parameter DSIZE08 = 2'b00;
parameter DSIZE16 = 2'b01;
parameter DSIZE32 = 2'b10;

module decode (opcode,valid_logop, valid_arithop);
input [4:0] opcode;
output valid_logop;
output valid_arithop;
node valid_logop;
node valid_arithop;
  always_comb valid_logop = ( opcode == OPAND
                | opcode == OPOR
                | opcode == OPXOR
               );
  always_comb valid_arithop = ( opcode == OPADD
                  | opcode == OPSUB
                  | opcode == OPMUL
                  | opcode == OPCMP
                  );
endmodule
// Mask a 32-bit vector according to dsize
//
function node [31:0] f_dsize_mask( node [2:0] dsize, node [31:0] data );
   casex ( dsize )
      3'b1xx  : f_dsize_mask = data;
      3'b01x  : f_dsize_mask = ( data & 32'h0000FFFF );
      default : f_dsize_mask = ( data & 32'h000000FF );
   endcase // casex( dsize )
endfunction // dsize_mask
module logical (
             CkLog,
             isloguop,
             uopv,
             uopcode,
             uopsize,
             src1,
             src2,
             logresultv,
             logresult
             );

input CkLog;
input isloguop;
input uopv;
input uopcode;
input uopsize;
input src1;
input src2;
output logresultv;
output logresult;

//
// Interface nodes
//

node Clk;

node uopv;
node isloguop;
node [4:0] uopcode;
node [1:0] uopsize;

node [31:0] src1;
node [31:0] src2;

// output
node        logresultv;
node [31:0] logresult;
node loguopv02;
`MSFF( loguopv02, uopv & isloguop , CkLog )

node [4:0] uopcode02;
`MSFF( uopcode02, uopcode, CkLog )

node [1:0] uopsize02;
`MSFF( uopsize02, uopsize, CkLog )

node opand, opor, opxor;
node [2:0] dsize;
always_comb begin

   opand = ( uopcode02 == OPAND );
   opor  = ( uopcode02 == OPOR  );
   opxor = ( uopcode02 == OPXOR );

   dsize[0] = ( uopsize02 == DSIZE08 );
   dsize[1] = ( uopsize02 == DSIZE16 );
   dsize[2] = ( uopsize02 == DSIZE32 );
   
end

//
// Stage 4
//

node loguopv03;
`MSFF( loguopv03, loguopv02, CkLog )

node [31:0] src1_03;
node [31:0] src2_03;
node [31:0] src1mask03;
node [31:0] src2mask03;
node [31:0] result03;

`MSFF( src1_03, src1, CkLog )
`MSFF( src2_03, src2, CkLog )

node opand03, opor03, opxor03;
`MSFF( opand03, opand, CkLog )
`MSFF( opor03,  opor,  CkLog )
`MSFF( opxor03, opxor, CkLog )
   
node [2:0] dsize03;
`MSFF( dsize03, dsize, CkLog )

always_comb begin

   src1mask03 = f_dsize_mask( dsize03, src1_03 );
   src2mask03 = f_dsize_mask( dsize03, src2_03 );

   unique casex ( 1'b1 )
      opand03 : result03 = src1mask03 & src2mask03;
      opor03  : result03 = src1mask03 | src2mask03;
      opxor03 : result03 = src1mask03 ^ src2mask03;
   endcase
            
end;

//
// Stage 05
//

`MSFF( logresultv, loguopv03, CkLog )
`MSFF( logresult, result03, CkLog )
endmodule

//
// Logic operations module
//
module logical_subunit (
             Clk,
             uopv,
             uopcode,
             uopsize,
             src1,
             src2,
             logresultv,
             logresult,
             //
             dfts1ovrd,
             dftdata
             );

input Clk;
input uopv;
input uopcode;
input uopsize;
input src1;
input src2;
input dfts1ovrd;
input dftdata;
output logresultv;
output logresult;

//
// Interface nodes
//

node Clk;

node uopv;
node [4:0] uopcode;
node [1:0] uopsize;

node        dfts1ovrd;
node [31:0] dftdata;
node [31:0] src1;
node [31:0] src2;

// output
node        logresultv;
node [31:0] logresult;

//
// Internal nodes
//

node CkLog;

always_comb CkLog = Clk;
// DFT feature: an override can be applied to src1
node [31:0] src1_d;
always_comb begin
src1_d = dfts1ovrd ? dftdata : src1;
end

//
// Stage 2
//

node isloguop;
decode decode (.opcode(uopcode), .valid_logop(isloguop));

//
// Stage 3
//
logical logical_unit( .CkLog(CkLog) , .isloguop(isloguop) , .uopv(uopv), .uopcode(uopcode), .uopsize(uopsize), .src1(src1_d) , .src2(src2) , .logresultv(logresultv), .logresult(logresult));



endmodule // logical_subunit

// 


//
// Adder operations module
//
module arithmetic (CkAddg,CkAdd,
              uopv,
              uopcode,
              uopsize,
              src1,
              src2,
              isadduop02,
              arithresultv,
              arithresult);
input CkAddg;
input CkAdd;
input uopv;
input uopcode;
input uopsize;
input src1;
input src2;
input isadduop02;
output arithresultv;
output arithresult;
node uopv;
node [4:0] uopcode;
node [1:0] uopsize;
node isadduop02;
node [31:0] src1;
node [31:0] src2;

// output
node        arithresultv;
node [31:0] arithresult;


node adduopv03;
`MSFF( adduopv03, uopv & isadduop02 , CkAddg )

node [4:0] uopcode03;
`MSFF( uopcode03, uopcode, CkAddg )

node [1:0] uopsize03;
`MSFF( uopsize03, uopsize, CkAddg )

node opadd03, opsub03, opmul03, opcmp03;
node [2:0] dsize;
always_comb begin

   opadd03 = ( uopcode03 == OPADD );
   opsub03 = ( uopcode03 == OPSUB );
   opmul03 = ( uopcode03 == OPMUL );
   opcmp03 = ( uopcode03 == OPCMP );

   dsize[0] = ( uopsize03 == DSIZE08 );
   dsize[1] = ( uopsize03 == DSIZE16 );
   dsize[2] = ( uopsize03 == DSIZE32 );
   
end

//
// Stage M304
//

node adduopv04;
`MSFF( adduopv04, adduopv03, CkAddg )

node [31:0] src104;
node [31:0] d_src1;
node [31:0] src204;
node [31:0] src1mask04;
node [31:0] src2mask04;
node [31:0] src2inv04;
node        cin04;
node        dummyout04;
node [31:0] result04;
node [31:0] cmpresult04;

`MSFF( src104, src1, CkAdd )
`MSFF( src204, src2, CkAddg )

node opadd04, opsub04, opmul04, opmul05, opcmp04;
`MSFF( opadd04, opadd03, CkAdd )
`MSFF( opsub04, opsub03, CkAdd )
`MSFF( opmul04, opmul03, CkAdd )
`MSFF( opmul05, opmul04, CkAdd )
`MSFF( opcmp04, opcmp03, CkAdd )
   
node [2:0] dsize04;
`MSFF( dsize04, dsize, CkAdd )

always_comb begin

   src1mask04 = f_dsize_mask( dsize04, src104 );
   src2mask04 = f_dsize_mask( dsize04, src204 );

   src2inv04 = src2mask04;
   if ( opsub04 ) src2mask04 = ~src2mask04;
   
   unique casex ( 1'b1 )
      opadd04 : cin04 = 1'b0;
      opsub04 : cin04 = 1'b1;
   endcase // casex( 1'b1 )
   
   cmpresult04 = (src1mask04 > src2mask04 ) ? src1mask04 : src2mask04;

   { result04, dummyout04 } = opcmp04 ? cmpresult04 : opmul04 ? (src1mask04 * src2mask04) : { src1mask04, cin04 } + { src2inv04, cin04 };
            
end;

//
// Stage 05
//

`MSFF( arithresultv, adduopv04, CkAddg )
`MSFF( arithresult, result04, CkAddg )

endmodule // arithmetic

module arithmetic_subunit (
              Clk,
              uopv,
              uopcode,
              uopsize,
              src1,
              src2,
              arithresultv,
              arithresult,
             //
             dfts1ovrd,
             dftdata,
             defeature_addck
              );

input Clk;
input uopv;
input uopcode;
input defeature_addck;
input uopsize;
input src1;
input src2;
input dfts1ovrd;
input dftdata;
output arithresultv;
output arithresult;

//
// Interface nodes
//

node Clk;

node        defeature_addck;
node uopv;
node [4:0] uopcode;
node [1:0] uopsize;

node [31:0] src1;
node [31:0] src2;
node        dfts1ovrd;
node [31:0] dftdata;

// output
node        arithresultv;
node [31:0] arithresult;

//
// Internal nodes
//

node CkAdd;

always_comb CkAdd = Clk;

node defeature_addckL;
`LATCH( defeature_addckL, defeature_addck, CkAdd )
node defeature_addckH;
`LATCH( defeature_addckH, defeature_addckL, CkAdd )
//
// Stage M302
//
node s2zero, s2zeroL;
always_comb s2zero = ( src2 == 32'd0 );
`LATCH ( s2zeroL, s2zero, CkAdd)

node CkAddg;
always_comb CkAddg = CkAdd & (defeature_addckL | ~s2zeroL); ;
node isadduop02;
//always_comb isadduop02 = valid_adderop(uopcode);
decode decode (.opcode(uopcode), .valid_arithop(isadduop02));

//
// Stage M303
//
arithmetic arithmetic_unit (.CkAddg(CkAddg), .CkAdd(CkAdd), .isadduop02(isadduop02), .uopv(uopv) , .uopcode(uopcode) , .uopsize(uopsize) , .src1(src1) , .src2(src2) , .arithresultv(arithresultv) , .arithresult(arithresult) ); 
endmodule// arithmetic
//
// Top-level wrapper module
//
module alu0(
            Clk,
            uopv,
            uopcode,
            uopsize,
            src1,
            src2,
            resultv,
            result,
            defeature_addck,
            dfts1ovrd,
            dftdata,
            defeature_addck
            );

input Clk;
input uopv;
input uopcode;
input uopsize;
input src1;
input src2;
input dfts1ovrd;
input defeature_addck;
input dftdata;
output resultv;
output result;

node Clk;

node        dfts1ovrd;
node        defeature_addck;
node [31:0] dftdata;
node uopv;
node [4:0] uopcode;
node [1:0] uopsize;

node [31:0] src1;
node [31:0] src2;

// outputs
node        resultv;
node [31:0] result;

//
// Internal nodes
//

node        logresultv;
node [31:0] logresult;
node        arithresultv;
node [31:0] arithresult;

logical_subunit logical_subunit (
                 .Clk ( Clk ),
                 .uopv ( uopv ),
                 .uopcode ( uopcode ),
                 .uopsize ( uopsize ),
                 .src1 ( src1 ),
                 .src2 ( src2 ),
                 .logresultv ( logresultv ),
                 .logresult ( logresult ),
                 .dftdata (dftdata),
                 .dfts1ovrd(dfts1ovrd)
                 );

arithmetic_subunit arithmetic_subunit (
                 .Clk ( Clk ),
                 .uopv ( uopv ),
                 .uopcode ( uopcode ),
                 .uopsize ( uopsize ),
                 .src1 ( src1 ),
                 .src2 ( src2 ),
                 .defeature_addck(defeature_addck),
                 .arithresultv ( arithresultv ),
                 .arithresult ( arithresult )
             );


always_comb begin

resultv = logresultv | arithresultv;
   
`MUX2_1( result,logresultv, logresult,arithresultv, arithresult )

end
function node valid_logical_op( node[4:0] opcode );
  valid_logical_op = ( opcode == OPAND
                | opcode == OPOR
                | opcode == OPXOR
                );
endfunction // 
function node valid_arithmetic_op( node[4:0] opcode );
  valid_arithmetic_op = ( opcode == OPADD
                  | opcode == OPSUB
                  | opcode == OPMUL
                  | opcode == OPCMP
                  );
endfunction // valid_adder
//
// ADD PROPERTIES HERE
//
genvar j;
generate for (j= OPADD;  j<= OPCMP; j++) begin: g2
   Page176_cover_arithmetic1: cover property (@(posedge Clk) ( uopcode == j |-> ##3 result ) );
   end
   endgenerate
Page164_assume : assume property (defeature_addck == 1'b1 );
Page176_cover_add08: cover property (( uopv & uopcode == OPADD & uopsize == DSIZE08 ) ##1 (src1 == 32'h8 & src2 ==32'h4) ##2 result == 32'hC );
Page181_assume: assume property (dfts1ovrd == 1'b1);
Page183_assert_Resultv_correct_wrt_uopv: assert property (uopv |-> ##8 resultv);
Page184_assume_legal_opcode : assume property (valid_arithmetic_op (uopcode) || valid_logical_op(uopcode));
Page185_assert_resultv_correct_sometime:assert property (uopv |-> s_eventually(resultv));
endmodule // alu0

