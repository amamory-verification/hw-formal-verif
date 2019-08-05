--! @file enc_kernel.vhd
--! @brief Xtea encrypt kernel
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
entity kernel is
	port (
		delta_i			: in  std_logic_vector(31 downto 0);
		key_i			: in  std_logic_vector(127 downto 0);
		sum_i			: in  std_logic_vector(31 downto 0);
		data_i			: in  std_logic_vector(63 downto 0);
		mode_i			: in std_logic;
		sum_o 			: out std_logic_vector(31 downto 0);
		mode_o			: out std_logic;
		data_o			: out std_logic_vector(63 downto 0)
	);
end kernel;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture kernel of kernel is

	-----------------------------------
	-- Types
	-----------------------------------


	-----------------------------------
	-- Constants
	-----------------------------------


	-----------------------------------
	-- Signal Declarations
	-----------------------------------

	signal v0			: std_logic_vector(31 downto 0);
	signal v0_result	: std_logic_vector(31 downto 0);
	signal v1			: std_logic_vector(31 downto 0);
	signal v1_result	: std_logic_vector(31 downto 0);
	signal v0_sum		: std_logic_vector(31 downto 0);
	signal v1_sum		: std_logic_vector(31 downto 0);
	signal v0_key_sel	: std_logic_vector(31 downto 0);
	signal v1_key_sel	: std_logic_vector(31 downto 0);

begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------


	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------

	v0 			<= data_i(63 downto 32);
	v1 			<= data_i(31 downto 0);

	v0_sum 		<= (v1_sum - delta_i) when mode_i = '1' else sum_i;
	v1_sum 		<= (v0_sum + delta_i) when mode_i = '0' else sum_i;
	
	v0_key_sel 	<= key_i(127 downto 96) when v0_sum(1 downto 0) = "00" else
				   key_i(95 downto 64) 	when v0_sum(1 downto 0) = "01" else
				   key_i(63 downto 32) 	when v0_sum(1 downto 0) = "10" else
				   key_i(31 downto 0);
				   
	v1_key_sel 	<= key_i(127 downto 96) when v1_sum(12 downto 11) = "00" else
				   key_i(95 downto 64) 	when v1_sum(12 downto 11) = "01" else
				   key_i(63 downto 32) 	when v1_sum(12 downto 11) = "10" else
				   key_i(31 downto 0);

	v0_result 	<= v0 + ((((v1(27 downto 0) & "0000") xor ("00000" & v1(31 downto 5))) + v1) xor (v0_sum + v0_key_sel)) when mode_i = '0' else
				   v0 - ((((v1_result(27 downto 0) & "0000") xor ("00000" & v1_result(31 downto 5))) + v1_result) xor (v0_sum + v0_key_sel));
				
	v1_result 	<= v1 + ((((v0_result(27 downto 0) & "0000") xor ("00000" & v0_result(31 downto 5))) + v0_result) xor (v1_sum + v1_key_sel)) when mode_i = '0' else
				   v1 - ((((v0(27 downto 0) & "0000") xor ("00000" & v0(31 downto 5))) + v0) xor (v1_sum + v1_key_sel));

	mode_o 		<= mode_i;
	sum_o		<= v1_sum when mode_i = '0' else v0_sum;
	
	data_o(63 downto 32) 	<= v0_result;
	data_o(31 downto 0)  	<= v1_result;

	-----------------------------------
	-- Processes
	-----------------------------------

end kernel;
