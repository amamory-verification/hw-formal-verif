
module bind_hermes_prop;

  bind RouterCC_wrapper hermes_prop Uprop (
  	.*,
    .S_EA (hermes.FSouth.EA),
    .E_EA (hermes.FEast.EA),
    .W_EA (hermes.FWest.EA),
    .N_EA (hermes.FNorth.EA),
    .L_EA (hermes.FLocal.EA)
  );

endmodule
