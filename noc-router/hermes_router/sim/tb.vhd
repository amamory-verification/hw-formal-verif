library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.HeMPS_defaults.all;

entity tb is
end tb;

architecture tb of tb is

	signal clock, reset : std_logic := '0';
	signal clock_rx : regNport;
	signal rx 	    : regNport;
	signal data_in  : arrayNport_regflit;
	signal credit_o : regNport;    
	signal clock_tx : regNport;
	signal tx		: regNport;
	signal data_out : arrayNport_regflit;
	signal credit_i : regNport;

begin

	clock_rx(0) <= clock;
	clock_rx(1) <= clock;
	clock_rx(2) <= clock;
	clock_rx(3) <= clock;
	clock_rx(4) <= clock;
	
	credit_i <= (others => '1');
	rx(EAST) <= '0';
	rx(WEST) <= '0';
	rx(NORTH) <= '0';
	rx(SOUTH) <= '0';

	reset <= '1', '0' after 10 ns;

	data_in(EAST) <= (others => '0');
	data_in(WEST) <= (others => '0');
	data_in(NORTH) <= (others => '0');
	data_in(SOUTH) <= (others => '0');

	process
	begin
		clock <= not clock;
		wait for 20 ns;
		clock <= not clock;
		wait for 20 ns;
	end process;

	process
	begin
	
		rx(LOCAL) <= '0';
		data_in(LOCAL) <= x"0000";
		wait until falling_edge(reset);
		
		-- Send target
		wait until rising_edge(clock);
		rx(LOCAL) <= '1';
		data_in(LOCAL) <= x"0012";
		
		-- Lenght
		wait until rising_edge(clock);
		wait for 1 ns;
		if credit_o(LOCAL) /= '1' then
  			wait until credit_o(LOCAL) = '1';
		end if;
		data_in(LOCAL) <= x"0003";
		rx(LOCAL) <= '1';
				
		-- Payload 1st flit
		wait until rising_edge(clock);
		wait for 1 ns;
		if credit_o(LOCAL) /= '1' then
  			wait until credit_o(LOCAL) = '1';
		end if;
		data_in(LOCAL) <= x"1001";
		rx(LOCAL) <= '1';
		
		-- Payload 2nd flit
		wait until rising_edge(clock);
		wait for 1 ns;
		if credit_o(LOCAL) /= '1' then
  			wait until credit_o(LOCAL) = '1';
		end if;
		data_in(LOCAL) <= x"2002";
		rx(LOCAL) <= '1';
		
		-- Payload 3rd flit
		wait until rising_edge(clock);
		wait for 1 ns;
		if credit_o(LOCAL) /= '1' then
  			wait until credit_o(LOCAL) = '1';
		end if;
		data_in(LOCAL) <= x"3003";
		rx(LOCAL) <= '1';
		wait until rising_edge(clock);
		rx(LOCAL) <= '0';
		data_in(LOCAL) <= x"0000";
				
		wait;
		
	end process;

	router: entity work.RouterCC
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
	
end tb;

