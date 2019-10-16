library IEEE;
use IEEE.std_logic_1164.all; 
use work.HeMPS_defaults.all;

entity RouterCC_wrapper is
port(
	clock:     in  std_logic;
	reset:     in  std_logic;
	rx:        in  std_logic_vector(4 downto 0);
	data_in :  in  arrayNport_regflit;
	credit_o:  out std_logic_vector(4 downto 0);
	clock_tx:  out std_logic_vector(4 downto 0);
	tx:        out std_logic_vector(4 downto 0);
	data_out:  out arrayNport_regflit;
	credit_i:  in  std_logic_vector(4 downto 0)
	);
end RouterCC_wrapper;

architecture beh of RouterCC_wrapper is
	signal clock_rx: std_logic_vector(4 downto 0);
begin

	-- all the input clocks are connected to the main clock
	clock_rx(0) <= clock;
	clock_rx(1) <= clock;
	clock_rx(2) <= clock;
	clock_rx(3) <= clock;
	clock_rx(4) <= clock;


	hermes : entity work.RouterCC
	port map(
		clock    => clock,
		reset    => reset,    
		clock_rx => clock_rx,  
		rx       => rx, 
		data_in  => data_in,
		credit_o => credit_o,  
		clock_tx => clock_tx,  
		tx       => tx,   
		data_out => data_out,
		credit_i => credit_i 
	);	

end architecture;
