--! @file enc_xtea_pipeline.vhd
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
	use ieee.numeric_std.all;

-------------------------------------------------------------------------------
-- Entity
-------------------------------------------------------------------------------
entity xtea_pipeline is
	generic (
		ROUNDS 			: integer := 32
	);
	port (
		rst				: in  std_logic;
		clk				: in  std_logic;
		key_i			: in  std_logic_vector(127 downto 0);
		start_i			: in  std_logic;
		done_o			: out std_logic;
		mode_i			: in  std_logic;
		mode_o			: out std_logic;
		data_i			: in  std_logic_vector(63 downto 0);
		data_o			: out std_logic_vector(63 downto 0)
	);
end xtea_pipeline;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture xtea_pipeline of xtea_pipeline is

	-----------------------------------
	-- Types
	-----------------------------------

	type matrix_32 is array (0 to ROUNDS - 1) of std_logic_vector (31 downto 0);
	type matrix_64 is array (0 to ROUNDS - 1) of std_logic_vector (63 downto 0);

	-----------------------------------
	-- Constants
	-----------------------------------
	
	constant DELTA_C 	 : std_logic_vector(31 downto 0) := x"9e3779b9";
	constant SUM_C 		 : std_logic_vector(63 downto 0) := conv_std_logic_vector((conv_integer(DELTA_C)*ROUNDS),64);


	-----------------------------------
	-- Signal Declarations
	-----------------------------------

	signal sum_pipe  		: matrix_32;
	signal sum_kernel  		: matrix_32;
	signal data_pipe 		: matrix_64;
	signal data_kernel 		: matrix_64;
	signal mode_pipe  		: std_logic_vector(ROUNDS - 1 downto 0);
	signal mode_kernel		: std_logic_vector(ROUNDS - 1 downto 0);

	signal start_pipe		: std_logic_vector(ROUNDS - 1 downto 0);
	signal start_kernel		: std_logic_vector(ROUNDS - 1 downto 0);
	
	signal sum_reg 			: std_logic_vector (31 downto 0);
	signal xtea_input 		: std_logic_vector (63 downto 0);
	signal xtea_output 		: std_logic_vector (63 downto 0);
	signal mode_output 		: std_logic;
	
begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------

	dec_stages_gen : for i in 0 to ROUNDS generate
		first_stages : if i = 0 generate
			dec_stage_i: entity work.pipeline_stage
				port map(
					clk  		=> clk,
					rst   		=> rst,
					start_i		=> start_i,
					start_o 	=> start_pipe(i),
					sum_i		=> sum_reg,
					sum_o   	=> sum_pipe(i),
					mode_i		=> mode_i,
					mode_o		=> mode_pipe(i),
					data_i		=> xtea_input,
					data_o		=> data_pipe(i)
				);
		end generate first_stages;

		last_stages : if i = ROUNDS generate
			dec_stage_i: entity work.pipeline_stage
				port map(
					clk  		=> clk,
					rst   		=> rst,
					start_i		=> start_kernel(i-1),
					start_o 	=> done_o,
					sum_i		=> sum_kernel(i-1),
					sum_o   	=> open,
					mode_i		=> mode_kernel(i-1),
					mode_o		=> mode_output,
					data_i		=> data_kernel(i-1),
					data_o		=> xtea_output
				);
		end generate last_stages;

		other_stages : if i > 0 and i < ROUNDS generate
			dec_stage_i: entity work.pipeline_stage
				port map(
					clk  		=> clk,
					rst   		=> rst,
					start_i		=> start_kernel(i-1),
					start_o 	=> start_pipe(i),
					sum_i		=> sum_kernel(i-1),
					sum_o   	=> sum_pipe(i),
					mode_i		=> mode_kernel(i-1),
					mode_o 		=> mode_pipe(i),
					data_i		=> data_kernel(i-1),
					data_o		=> data_pipe(i)
				);
		end generate other_stages;
	end generate dec_stages_gen;

	dec_xtea_gen : for i in 0 to ROUNDS-1 generate
		dec_kernel_i: entity work.kernel_round
			port map(
				clk  		=> clk,
				rst   		=> rst,
				delta_i		=> DELTA_C,
				key_i		=> key_i,
				start_i		=> start_pipe(i),
				start_o		=> start_kernel(i),
				sum_i		=> sum_pipe(i),
				sum_o		=> sum_kernel(i),
				mode_i		=> mode_pipe(i),
				mode_o		=> mode_kernel(i),
				data_i		=> data_pipe(i),
				data_o		=> data_kernel(i)
			);
	end generate dec_xtea_gen;

	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------

	mode_o 		<= mode_output;

	xtea_input	<= data_i 				when mode_i = '0' else data_i(31 downto 0) & data_i(63 downto 32);
	data_o		<= xtea_output			when mode_output = '0' else xtea_output(31 downto 0) & xtea_output(63 downto 32);
	sum_reg 	<= SUM_C(31 downto 0)	when mode_i = '1' else (others=>'0');
	
	-----------------------------------
	-- Processes
	-----------------------------------

end xtea_pipeline;
