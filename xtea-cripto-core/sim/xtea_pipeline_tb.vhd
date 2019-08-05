library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_textio.all;
use ieee.std_logic_unsigned.all;

entity tb is
end tb;

architecture tb of tb is
	signal clock, reset, start, encrypt, ready, ready_pipe : std_logic := '0';
	signal key : std_logic_vector(127 downto 0);
	signal input, output, output_pipe : std_logic_vector(63 downto 0);	
begin

	reset <= '0', '1' after 5 ns, '0' after 500 ns;

	process						--25Mhz system clock
	begin
		clock <= not clock;
		wait for 20 ns;
		clock <= not clock;
		wait for 20 ns;
	end process;

	start <= '0', '1' after 1000 ns;
	encrypt <= '1';
	key <= x"f0e1d2c3b4a5968778695a4b3c2d1e0f";
	input <= x"1234567890123456";

	-- XTEA core
	core: entity work.xtea
	port map(	clock => clock,
			reset => reset,
			start => start,
			encrypt => encrypt,
			key => key,
			input => input,
			output => output,
			ready => ready
	);
	
	core_pipe: entity work.xtea_top
	port map(	clock => clock,
			reset => reset,
			start => start,
			encrypt => encrypt,
			key => key,
			input => input,
			output => output_pipe,
			ready =>  ready_pipe
	);

end tb;

