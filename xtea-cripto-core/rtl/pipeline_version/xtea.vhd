--! @file xtea.vhd
--! @brief
--! @author Leonardo Juracy, leonardo.juracy@acad.pucrs.br
--! @date 2016-08-10

-------------------------------------------------------------------------------
-- Libraries
-------------------------------------------------------------------------------
library ieee;
	use ieee.std_logic_1164.all;
	use ieee.std_logic_unsigned.all;
	use ieee.std_logic_arith.all;

-------------------------------------------------------------------------------
-- Entity
-------------------------------------------------------------------------------
entity xtea_top is
	generic (
		ROUNDS 			: integer := 32
	);
	port (
		clock			: in  std_logic;
		reset			: in  std_logic;
		start			: in  std_logic;
		encrypt			: in  std_logic;
		key				: in  std_logic_vector(127 downto 0);
		input			: in  std_logic_vector(63 downto 0);
		output			: out std_logic_vector(63 downto 0);
		ready			: out std_logic
	);
end xtea_top;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture xtea of xtea_top is

	-----------------------------------
	-- Types
	-----------------------------------


	-----------------------------------
	-- Constants
	-----------------------------------


	-----------------------------------
	-- Signal Declarations
	-----------------------------------
	--signal mode_o : std_logic;

begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------
	
	xtea_pipeline_i: entity work.xtea_pipeline
		generic map ( 
			ROUNDS 		=> 5
		)
		port map(	
			rst			=> reset,   	
			clk			=> clock,
			start_i		=> start,
			key_i		=> key,		
			data_i		=> input,
			mode_i		=> encrypt,
			mode_o		=> open,
			done_o		=> ready,	
			data_o		=> output
		);

	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------


	-----------------------------------
	-- Processes
	-----------------------------------

end xtea;
