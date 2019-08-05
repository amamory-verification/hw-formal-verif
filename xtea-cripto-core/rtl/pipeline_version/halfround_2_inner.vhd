--! @file halfround_2.vhd
--! @brief Xtea halfround 2
--! @author Felipe Kuentzer, felipe.kuentzer@acad.pucrs.br
--! @date 2016-12-08

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
entity halfround_2 is
	port (
		clk				: in  std_logic;
		rst				: in  std_logic;
		key_i			: in  std_logic_vector(127 downto 0);
		sum_i			: in  std_logic_vector(31 downto 0);
		sum_o			: out std_logic_vector(31 downto 0);
		mode_i			: in  std_logic;
		mode_o			: out std_logic;
		start_i			: in  std_logic;
		start_o			: out std_logic;
		data_z_i		: in  std_logic_vector(31 downto 0);
		data_z_o		: out std_logic_vector(31 downto 0);
		data_y_i		: in  std_logic_vector(31 downto 0);
		data_y_o		: out std_logic_vector(31 downto 0)		
	);
end halfround_2;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture halfround_2 of halfround_2 is

	-----------------------------------
	-- Types
	-----------------------------------
	
	type pipe_type is array(0 to 2) of std_logic_vector(31 downto 0);

	-----------------------------------
	-- Constants
	-----------------------------------


	-----------------------------------
	-- Signal Declarations
	-----------------------------------

	signal start			: std_logic_vector(1 downto 0);
	signal mode				: std_logic_vector(1 downto 0);
	signal sum				: pipe_type;
	signal data_z			: pipe_type;
	signal data_y			: pipe_type;
	
	signal key_sel			: std_logic_vector(31 downto 0);
	signal key_sel_reg		: std_logic_vector(31 downto 0);
	
	signal subkey			: std_logic_vector(31 downto 0);
	signal subkey_reg		: std_logic_vector(31 downto 0);

	signal sftmix_1			: std_logic_vector(31 downto 0);
	signal sftmix_2			: std_logic_vector(31 downto 0);
	signal sftmix_3			: std_logic_vector(31 downto 0);
	signal sftmix_3_reg		: std_logic_vector(31 downto 0);
	signal sftmix			: std_logic_vector(31 downto 0);
	signal sftmix_reg		: std_logic_vector(31 downto 0);
	
	signal xor_result		: std_logic_vector(31 downto 0);
	signal xor_result_reg	: std_logic_vector(31 downto 0);

begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------
	
	inner_0_stage_inst: entity work.inner_round_stage
		port map(
			clk  			=> clk,
			rst   			=> rst,
			sum_i			=> sum_i,
			sum_o			=> sum(0),
			data_z_i		=> data_z_i,
			data_z_o		=> data_z(0),
			data_y_i		=> data_y_i,
			data_y_o		=> data_y(0),
			mode_i			=> mode_i,
			mode_o			=> mode(0),
			start_i			=> start_i,
			start_o	        => start(0)			
		);

	inner_1_stage_inst: entity work.inner_round_stage
		port map(
			clk  			=> clk,
			rst   			=> rst,
			sum_i			=> sum(0),
			sum_o			=> sum(1),
			data_z_i		=> data_z(0),
			data_z_o		=> data_z(1),
			data_y_i		=> data_y(0),
			data_y_o		=> data_y(1),
			mode_i			=> mode(0),
			mode_o			=> mode(1),
			start_i			=> start(0),
			start_o	        => start(1)			
		);
	
	inner_2_stage_inst: entity work.inner_round_stage
		port map(
			clk  			=> clk,
			rst   			=> rst,
			sum_i			=> sum(1),
			sum_o			=> sum(2),
			data_z_i		=> data_z(1),
			data_z_o		=> data_z(2),
			data_y_i		=> data_y(1),
			data_y_o		=> data_y(2),
			mode_i			=> mode(1),
			mode_o			=> mode_o,
			start_i			=> start(1),
			start_o	        => start_o			
		);

	
	keysel_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 32
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> key_sel,
			data_o			=> key_sel_reg
		);
	
	sftmix_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 32
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> sftmix,
			data_o			=> sftmix_reg
		);

	sftmix_3_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 32
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> sftmix_3,
			data_o			=> sftmix_3_reg
		);

	subkey_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 32
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> subkey,
			data_o			=> subkey_reg
		);
	
	xor_result_flop: entity work.flop
		generic map (
			DATA_WIDTH		=> 32
		)
		port map (
			rst				=> rst,
			clk				=> clk,
			data_i			=> xor_result,
			data_o			=> xor_result_reg
		);


	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------
	
	-- keygen step
	key_sel 	<= key_i(127 downto 96) when ((sum_i(12 downto 11) = "00" and mode_i = '0') or (sum_i(1 downto 0) = "00" and mode_i = '1')) else
				   key_i(95 downto 64) 	when ((sum_i(12 downto 11) = "01" and mode_i = '0') or (sum_i(1 downto 0) = "01" and mode_i = '1')) else
				   key_i(63 downto 32) when ((sum_i(12 downto 11) = "10" and mode_i = '0') or (sum_i(1 downto 0) = "10" and mode_i = '1')) else
				   key_i(31 downto 0);
	subkey		<= sum(0) + key_sel_reg;
	
	-- f step
	sftmix_1 	<= data_z_i(27 downto 0) & "0000";
	sftmix_2 	<= "00000" & data_z_i(31 downto 5);
	sftmix_3 	<= sftmix_1 xor sftmix_2;
	sftmix	 	<= sftmix_3_reg + data_z(0);

	xor_result 	<= sftmix_reg xor subkey_reg;
	
	data_z_o	<= (data_y(2) + xor_result_reg) when mode_i = '0' else (data_y(2) - xor_result_reg);
	data_y_o	<= data_z(2);
	
	sum_o		<= sum(2);

	-----------------------------------
	-- Processes
	-----------------------------------

end halfround_2;
