
// Generated by Cadence Genus(TM) Synthesis Solution 18.14-s037_1
// Generated on: Jul 22 2019 17:15:05 BRT (Jul 22 2019 20:15:05 UTC)

// Verification Directory fv/sanduba 

module sanduba(m100, dev, r_green, r_atum, r_bacon, clock, reset, d100,
     green, atum, bacon, busy);
  input m100, dev, r_green, r_atum, r_bacon, clock, reset;
  output d100, green, atum, bacon, busy;
  wire m100, dev, r_green, r_atum, r_bacon, clock, reset;
  wire d100, green, atum, bacon, busy;
  wire [4:0] count;
  wire [2:0] pe;
  wire [2:0] ea;
  wire n_1, n_2, n_3, n_4, n_5, n_6, n_7, n_8;
  wire n_9, n_10, n_11, n_12, n_13, n_14, n_15, n_16;
  wire n_18, n_19, n_20, n_21, n_22, n_23, n_24, n_25;
  wire n_26, n_28, n_29, n_30, n_31, n_32, n_33, n_34;
  wire n_35, n_36, n_37, n_38, n_39, n_41, n_42, n_43;
  wire n_44, n_45, n_47, n_48, n_49, n_50, n_51, n_53;
  wire n_54, n_55, n_56, n_57, n_58, n_59, n_60, n_61;
  wire n_62, n_63, n_64, n_65, n_66, n_67, n_68, n_69;
  wire n_70;
  C12T28SOI_LR_DFPRQX17_P0 \count_reg[4] (.RN (n_70), .CP (clock), .D
       (n_69), .Q (count[4]));
  C12T28SOI_LR_DFPRQX17_P0 \count_reg[3] (.RN (n_70), .CP (clock), .D
       (n_68), .Q (count[3]));
  C12T28SOI_LR_AO222X8_P0 g2225(.A (n_7), .B (n_67), .C (count[4]), .D
       (n_66), .E (n_63), .F (n_26), .Z (n_69));
  C12T28SOI_LR_DFPRQNX17_P0 \count_reg[1] (.RN (n_70), .CP (clock), .D
       (n_64), .QN (count[1]));
  C12T28SOI_LR_AO222X8_P0 g2224(.A (n_65), .B (n_67), .C (count[3]), .D
       (n_61), .E (n_50), .F (n_15), .Z (n_68));
  C12T28SOI_LR_DFPRQX17_P0 \count_reg[2] (.RN (n_70), .CP (clock), .D
       (n_62), .Q (count[2]));
  C12T28SOI_LR_DFPRQNX17_P0 \ea_reg[2] (.RN (n_70), .CP (clock), .D
       (pe[2]), .QN (ea[2]));
  C12T28SOI_LR_OAI211X5_P0 g2235(.A (n_65), .B (n_32), .C (n_16), .D
       (n_57), .Z (n_66));
  C12T28SOI_LR_AO222X8_P0 g2236(.A (n_28), .B (n_58), .C (n_39), .D
       (n_53), .E (n_9), .F (n_63), .Z (n_64));
  C12T28SOI_LRS_XNOR2X6_P0 g2230(.A (count[2]), .B (n_54), .Z (n_62));
  C12T28SOI_LR_DFPRQNX17_P0 \count_reg[0] (.RN (n_70), .CP (clock), .D
       (n_59), .QN (count[0]));
  C12T28SOI_LR_DFPRQNX17_P0 \ea_reg[1] (.RN (n_70), .CP (clock), .D
       (pe[1]), .QN (ea[1]));
  C12T28SOI_LR_DFPRQX17_P0 \ea_reg[0] (.RN (n_70), .CP (clock), .D
       (pe[0]), .Q (ea[0]));
  C12T28SOI_LR_LDHQX8_P0 \pe_reg[2] (.G (n_60), .D (n_55), .Q (pe[2]));
  C12T28SOI_LR_AO12X8_P0 g2234(.A (count[2]), .B (n_24), .C (n_56), .Z
       (n_61));
  C12T28SOI_LR_LDHQX8_P0 \pe_reg[0] (.G (n_60), .D (n_47), .Q (pe[0]));
  C12T28SOI_LR_AO12X8_P0 g2242(.A (n_41), .B (n_58), .C (n_42), .Z
       (n_59));
  C12T28SOI_LR_LDHQX8_P0 \pe_reg[1] (.G (n_60), .D (n_44), .Q (pe[1]));
  C12T28SOI_LR_IVX8_P0 g2237(.A (n_56), .Z (n_57));
  C12T28SOI_LR_NAND3ABX7_P0 g2229(.A (n_25), .B (n_36), .C (n_45), .Z
       (n_55));
  C12T28SOI_LR_OAI211X5_P0 g2243(.A (n_21), .B (n_51), .C (n_49), .D
       (n_48), .Z (n_54));
  C12T28SOI_LR_XOR3X8_P0 g2248(.A (count[1]), .B (d100), .C (n_30), .Z
       (n_53));
  C12T28SOI_LR_OAI211X5_P0 g2239(.A (n_51), .B (n_50), .C (n_49), .D
       (n_48), .Z (n_56));
  C12T28SOI_LR_OAI21X5_P0 g2231(.A (n_35), .B (busy), .C (n_45), .Z
       (n_47));
  C12T28SOI_LR_NAND4ABX6_P0 g2232(.A (n_43), .B (n_63), .C (n_34), .D
       (n_6), .Z (n_60));
  C12T28SOI_LR_OAI21X5_P0 g2241(.A (n_43), .B (busy), .C (n_37), .Z
       (n_44));
  C12T28SOI_LR_OAI22X5_P0 g2247(.A (n_19), .B (n_31), .C (n_41), .D
       (n_51), .Z (n_42));
  C12T28SOI_LR_NAND2AX7_P0 g2251(.A (bacon), .B (n_49), .Z (n_58));
  C12T28SOI_LR_AO12X8_P0 g2238(.A (n_39), .B (n_38), .C (bacon), .Z
       (n_67));
  C12T28SOI_LR_NOR3X6_P0 g2240(.A (n_29), .B (n_5), .C (n_18), .Z
       (n_45));
  C12T28SOI_LR_NAND2AX7_P0 g2245(.A (n_38), .B (n_39), .Z (n_48));
  C12T28SOI_LR_IVX4_P0 g2244(.A (n_36), .Z (n_37));
  C12T28SOI_LR_NOR2AX3_P0 g2249(.A (n_33), .B (m100), .Z (n_35));
  C12T28SOI_LR_AND2X8_P0 g2250(.A (n_13), .B (n_33), .Z (n_34));
  C12T28SOI_LR_NAND2X7_P0 g2257(.A (n_51), .B (n_32), .Z (n_49));
  C12T28SOI_LR_HA1X8_P0 g2255(.A0 (n_8), .B0 (count[0]), .CO (n_30),
       .S0 (n_31));
  C12T28SOI_LR_NOR3X6_P0 g2252(.A (m100), .B (n_22), .C (busy), .Z
       (n_29));
  C12T28SOI_LR_NOR4ABX6_P0 g2246(.A (ea[0]), .B (ea[1]), .C (ea[2]), .D
       (n_11), .Z (n_36));
  C12T28SOI_LR_AOI21X6_P0 g2253(.A (n_28), .B (green), .C (n_14), .Z
       (n_38));
  C12T28SOI_LR_NOR3AX6_P0 g2259(.A (count[3]), .B (n_20), .C
       (count[4]), .Z (n_26));
  C12T28SOI_LR_NOR3X6_P0 g2258(.A (m100), .B (n_23), .C (busy), .Z
       (n_25));
  C12T28SOI_LR_IVX8_P0 g2266(.A (n_32), .Z (n_24));
  C12T28SOI_LR_NAND3AX6_P0 g2254(.A (m100), .B (n_23), .C (n_22), .Z
       (n_43));
  C12T28SOI_LR_OAI21X5_P0 g2260(.A (n_21), .B (n_12), .C (r_atum), .Z
       (n_33));
  C12T28SOI_LR_IVX8_P0 g2261(.A (n_20), .Z (n_50));
  C12T28SOI_LR_IVX8_P0 g2262(.A (n_19), .Z (n_39));
  C12T28SOI_LR_NOR3X6_P0 g2269(.A (n_18), .B (atum), .C (green), .Z
       (n_32));
  C12T28SOI_LR_IVX8_P0 g2270(.A (n_15), .Z (n_16));
  C12T28SOI_LR_AO12X8_P0 g2256(.A (n_10), .B (d100), .C (n_21), .Z
       (n_14));
  C12T28SOI_LR_OAI21X5_P0 g2267(.A (n_28), .B (n_12), .C (r_green), .Z
       (n_13));
  C12T28SOI_LR_NOR3X6_P0 g2265(.A (atum), .B (green), .C (d100), .Z
       (n_19));
  C12T28SOI_LR_NAND2X7_P0 g2264(.A (count[2]), .B (n_21), .Z (n_20));
  C12T28SOI_LR_NOR2X7_P0 g2272(.A (count[3]), .B (n_51), .Z (n_15));
  C12T28SOI_LR_NAND2X3_P0 g2273(.A (r_bacon), .B (n_12), .Z (n_23));
  C12T28SOI_LR_NOR2X3_P0 g2263(.A (n_10), .B (n_12), .Z (n_11));
  C12T28SOI_LR_AOI211X4_P0 g2268(.A (r_atum), .B (r_green), .C (dev),
       .D (n_2), .Z (n_22));
  C12T28SOI_LR_HA1X8_P0 g2271(.A0 (n_28), .B0 (n_41), .CO (n_21), .S0
       (n_9));
  C12T28SOI_LR_IVX8_P0 g2274(.A (green), .Z (n_8));
  C12T28SOI_LR_NOR2X7_P0 g2275(.A (n_1), .B (n_4), .Z (atum));
  C12T28SOI_LR_IVX8_P0 g2279(.A (n_12), .Z (n_7));
  C12T28SOI_LR_IVX8_P0 g2280(.A (n_51), .Z (n_63));
  C12T28SOI_LR_AND2X8_P0 g2276(.A (ea[1]), .B (n_18), .Z (bacon));
  C12T28SOI_LR_NAND2AX3_P0 g2277(.A (ea[0]), .B (n_6), .Z (busy));
  C12T28SOI_LR_IVX4_P0 g2287(.A (n_4), .Z (n_5));
  C12T28SOI_LR_AND2X8_P0 g2283(.A (n_3), .B (n_18), .Z (d100));
  C12T28SOI_LR_NAND2AX7_P0 g2282(.A (count[4]), .B (n_65), .Z (n_12));
  C12T28SOI_LR_NAND2X7_P0 g2284(.A (ea[0]), .B (n_6), .Z (n_51));
  C12T28SOI_LR_NAND2X7_P0 g2289(.A (n_3), .B (ea[2]), .Z (n_4));
  C12T28SOI_LR_OA12X8_P0 g2281(.A (r_atum), .B (r_green), .C (r_bacon),
       .Z (n_2));
  C12T28SOI_LR_AND2X8_P0 g2290(.A (ea[1]), .B (ea[2]), .Z (n_6));
  C12T28SOI_LR_NOR2X7_P0 g2285(.A (count[2]), .B (count[3]), .Z (n_65));
  C12T28SOI_LR_NAND2X7_P0 g2288(.A (count[0]), .B (count[1]), .Z
       (n_10));
  C12T28SOI_LR_NOR2X7_P0 g2286(.A (ea[0]), .B (ea[2]), .Z (n_18));
  C12T28SOI_LR_IVX8_P0 g2295(.A (ea[0]), .Z (n_1));
  C12T28SOI_LR_IVX8_P0 g2296(.A (count[0]), .Z (n_41));
  C12T28SOI_LR_IVX8_P0 g2293(.A (count[1]), .Z (n_28));
  C12T28SOI_LR_IVX8_P0 g2291(.A (ea[1]), .Z (n_3));
  C12T28SOI_LR_IVX4_P0 g2292(.A (reset), .Z (n_70));
  C12T28SOI_LR_NOR3AX6_P0 g2(.A (ea[2]), .B (ea[0]), .C (ea[1]), .Z
       (green));
endmodule

