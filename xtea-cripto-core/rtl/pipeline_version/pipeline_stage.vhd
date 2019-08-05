--! @file pipeline_stage.vhd
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
entity pipeline_stage is
	port (
		clk				: in  std_logic;
		rst				: in  std_logic;
		data_i			: in  std_logic_vector(63 downto 0);
		data_o			: out std_logic_vector(63 downto 0);
		sum_i 			: in  std_logic_vector(31 downto 0);
		sum_o 			: out std_logic_vector(31 downto 0);
		mode_i 			: in  std_logic;
		mode_o	 		: out std_logic;
		start_i 		: in  std_logic;
		start_o 		: out std_logic
	);
end pipeline_stage;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture pipeline_stage of pipeline_stage is

	-----------------------------------
	-- Types
	-----------------------------------
	
	
	-----------------------------------
	-- Constants
	-----------------------------------

	
	-----------------------------------
	-- Signal Declarations
	-----------------------------------
	
begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------

	start_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 1
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i(0)		=> start_i,
			data_o(0)		=> start_o
		);
	
	mode_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 1
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i(0)		=> mode_i,
			data_o(0)		=> mode_o
		);

	data_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 64
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> data_i,
			data_o			=> data_o
		);
	
	sum_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 32
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> sum_i,
			data_o			=> sum_o
		);

	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------			

	
	-----------------------------------
	-- Processes
	-----------------------------------	

end pipeline_stage;

