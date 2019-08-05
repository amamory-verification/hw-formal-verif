--! @file kernel_round.vhd
--! @brief Xtea kernel round
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
entity kernel_round is
	port (
		clk				: in  std_logic;
		rst				: in  std_logic;
		delta_i			: in  std_logic_vector(31 downto 0);
		key_i			: in  std_logic_vector(127 downto 0);
		start_i			: in  std_logic;
		start_o			: out std_logic;
		sum_i			: in  std_logic_vector(31 downto 0);
		sum_o 			: out std_logic_vector(31 downto 0);
		mode_i			: in  std_logic;
		mode_o			: out std_logic;
		data_i			: in  std_logic_vector(63 downto 0);
		data_o			: out std_logic_vector(63 downto 0)
	);
end kernel_round;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture kernel_round of kernel_round is

	-----------------------------------
	-- Types
	-----------------------------------


	-----------------------------------
	-- Constants
	-----------------------------------


	-----------------------------------
	-- Signal Declarations
	-----------------------------------

	signal mode_half1		: std_logic;	
	signal mode_half2		: std_logic;
	signal start_half1		: std_logic;	
	signal start_half2		: std_logic;		
	signal sum_half1		: std_logic_vector(31 downto 0);
	signal sum_half2		: std_logic_vector(31 downto 0);
	signal data_half1		: std_logic_vector(63 downto 0);
	signal data_half2		: std_logic_vector(63 downto 0);

begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------
	
	halfround_1_inst: entity work.halfround_1
		port map (
			delta_i			=> delta_i,
			key_i			=> key_i,
			sum_i			=> sum_i,
			sum_o 			=> sum_half1,
			mode_i			=> mode_i,
			mode_o			=> mode_half1,
			data_i			=> data_i,
			data_o			=> data_half1
		);
	
	inner_round_stage_inst: entity work.inner_round_stage
		port map(
			clk  			=> clk,
			rst   			=> rst,
			sum_i			=> sum_half1,
			sum_o			=> sum_half2,
			data_i			=> data_half1,
			data_o			=> data_half2,
			mode_i			=> mode_half1,
			mode_o			=> mode_half2,
			start_i			=> start_i,
			start_o	        => start_o			
		);

	halfround_2_inst: entity work.halfround_2
		port map (
			key_i			=> key_i,
			sum_i			=> sum_half2,
			sum_o			=> sum_o,
			mode_i			=> mode_half2,
			mode_o			=> mode_o,
			data_i			=> data_half2,
			data_o			=> data_o
		);
	
	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------


	-----------------------------------
	-- Processes
	-----------------------------------

end kernel_round;
