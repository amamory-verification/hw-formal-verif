library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.NUMERIC_STD.to_unsigned;

entity sanduiche_tmr2 is
    port (
           clock:   in STD_LOGIC;
           reset:   in STD_LOGIC;
           M100:    in STD_LOGIC;
           DEV:     in STD_LOGIC;
           R_green: in STD_LOGIC;
           R_atum:  in STD_LOGIC;
           R_bacon: in STD_LOGIC;

           busy:  out STD_LOGIC;
           D100:  out STD_LOGIC;
           GREEN: out STD_LOGIC;
           ATUM:  out STD_LOGIC;
           BACON: out STD_LOGIC
       );
end sanduiche_tmr2;

architecture sanduiche_tmr of sanduiche_tmr2 is

signal busy_s, d100_s, green_s, atum_s, bacon_s : std_logic_vector(2 downto 0);

begin    
 
 
    tmr: for I in 0 to 2 generate
		sandwich: entity work.sanduiche port map (clock=>clock, reset=>reset,
				  M100=>M100, DEV=>DEV, R_green=>R_green, R_atum=>R_atum, R_bacon=>R_bacon,
				  busy => busy_s(i), d100 => d100_s(i), 
				  green => green_s(i), ATUM => ATUM_s(i), BACON => BACON_s(i)
				  );
	end generate;

    -- a voter for each primary output (cone of influence)
    busy   <= busy_s(0) when busy_s(0) = busy_s(1) or busy_s(0) = busy_s(2)  else 
              busy_s(1) when busy_s(1) = busy_s(0) or busy_s(1) = busy_s(2) else 
              busy_s(2);
    d100   <= d100_s(0) when d100_s(0) = d100_s(1) or d100_s(0) = d100_s(2)  else 
              d100_s(1) when d100_s(1) = d100_s(0) or d100_s(1) = d100_s(2) else 
              d100_s(2);
    green  <= green_s(0) when green_s(0) = green_s(1) or green_s(0) = green_s(2)  else 
              green_s(1) when green_s(1) = green_s(0) or green_s(1) = green_s(2) else 
              green_s(2);
    atum   <= atum_s(0) when atum_s(0) = atum_s(1) or atum_s(0) = atum_s(2)  else 
              atum_s(1) when atum_s(1) = atum_s(0) or atum_s(1) = atum_s(2) else 
              atum_s(2);
    bacon  <= bacon_s(0) when bacon_s(0) = bacon_s(1) or bacon_s(0) = bacon_s(2)  else 
              bacon_s(1) when bacon_s(1) = bacon_s(0) or bacon_s(1) = bacon_s(2) else 
              bacon_s(2);
              
end sanduiche_tmr;

