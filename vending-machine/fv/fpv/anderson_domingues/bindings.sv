module sanduba_bind_top;

	bind sanduba sanduba_prop sanduba_bind(
	  .clock(clock),       .reset(reset),
	  .r_green(r_green),   .green(green),
	  .r_atum(r_atum),     .atum(atum),
	  .r_bacon(r_bacon),   .bacon(bacon),
	  .dev(dev),           .busy(busy),
	  .m100(m100),         .d100(d100),

	  //outs >> d100, green, atum, bacon, busy;

	  //internals
	  .count(count),
	  .pe(pe),
	  .ea(ea)
	);

endmodule
