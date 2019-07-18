library ieee;
use ieee.std_logic_1164.all;

entity tb is
end tb;

architecture tb of tb is
	signal clock: std_logic := '0';
	signal reset, m100, dev, r_green, r_atum, r_bacon, d100, bacon, atum, green, busy: std_logic;
	begin 
	ab: entity work.t4
	port map(
	clock => clock, reset => reset, m100 => m100, dev => dev, r_green => r_green, r_atum => r_atum,
	r_bacon => r_bacon, d100 => d100, green => green, atum => atum, bacon => bacon, busy => busy
	);
	reset <= '1', '0' after 5 ns;
	clock <= not clock after 5 ns;
	
	m100 <= '0', '1' after 20 ns, '0' after 30 ns, '1' after 40 ns, '0' after 50 ns, '1' after 60 ns, '0' after 70 ns,
	'0' after 80 ns, '1' after 90 ns, '0' after 100 ns, '1' after 110 ns, '0' after 120 ns;
	--dev <= '0', '1' after 50 ns;
	dev <= '0';
	--r_green <= '0', '1' after 20 ns;
	r_green <= '0';
	--r_green <= '0', '1' after 70 ns;
	--r_atum <= '0', '1' after 110 ns;
	r_atum <= '0';
	r_bacon <= '0', '1' after 130 ns;
	--r_bacon <= '0';
end architecture tb;
