//
// Macros in the flavor of those commonly used by Intel RTL
//


// A basic Flip-Flop
`define MSFF(q,i,clock)       \
   always_ff @(posedge clock) \
      begin                   \
         q <= i;              \
      end

// A basic Latch
`define LATCH(q,i,clock)     \
   always_latch              \
      begin                  \
         if (clock) q <= i;  \
      end

// A 2-to-1 mux
`define MUX2_1(out,sa,a,sb,b)         \
   unique casex ( 1'b1 )              \
             sa : out = a;            \
             sb : out = b;            \
          endcase // casex( 1'b1 )

// A 3-to-1 mux
`define MUX3_1(out,sa,a,sb,b,sc,c)    \
   unique casex ( 1'b1 )              \
             sa : out = a;            \
             sb : out = b;            \
             sc : out = c;            \
          endcase // casex( 1'b1 )

// A clock with a power enable condition and an override
`define MAKE_CLK_PEN(clk,baseclk,pen,ovrd)  \
   always_comb clk = baseclk & ( pen | ovrd );
