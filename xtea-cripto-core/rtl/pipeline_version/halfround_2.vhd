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
		key_i			: in  std_logic_vector(127 downto 0);
		sum_i			: in  std_logic_vector(31 downto 0);
		sum_o			: out std_logic_vector(31 downto 0);
		mode_i			: in  std_logic;
		mode_o			: out std_logic;
		data_i			: in  std_logic_vector(63 downto 0);
		data_o			: out std_logic_vector(63 downto 0)	
	);
end halfround_2;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture halfround_2 of halfround_2 is

	-----------------------------------
	-- Types
	-----------------------------------
	

	-----------------------------------
	-- Constants
	-----------------------------------


	-----------------------------------
	-- Signal Declarations
	-----------------------------------

	signal key_sel			: std_logic_vector(31 downto 0);
	signal subkey			: std_logic_vector(31 downto 0);

	signal sftmix_1			: std_logic_vector(31 downto 0);
	signal sftmix_2			: std_logic_vector(31 downto 0);
	signal sftmix_3			: std_logic_vector(31 downto 0);
	signal sftmix			: std_logic_vector(31 downto 0);
	signal v0				: std_logic_vector(31 downto 0);
	signal v1				: std_logic_vector(31 downto 0);
	signal xor_result		: std_logic_vector(31 downto 0);

begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------
	

	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------
	
	v0			<= data_i(63 downto 32);
	v1			<= data_i(31 downto 0);
	
	-- keygen step
	key_sel 	<= key_i(127 downto 96) when ((sum_i(12 downto 11) = "00" and mode_i = '0') or (sum_i(1 downto 0) = "00" and mode_i = '1')) else
				   key_i(95 downto 64) 	when ((sum_i(12 downto 11) = "01" and mode_i = '0') or (sum_i(1 downto 0) = "01" and mode_i = '1')) else
				   key_i(63 downto 32) when ((sum_i(12 downto 11) = "10" and mode_i = '0') or (sum_i(1 downto 0) = "10" and mode_i = '1')) else
				   key_i(31 downto 0);
	subkey		<= sum_i + key_sel;
	
	-- f step
	sftmix_1 	<= v0(27 downto 0) & "0000";
	sftmix_2 	<= "00000" & v0(31 downto 5);
	sftmix_3 	<= sftmix_1 xor sftmix_2;
	sftmix	 	<= sftmix_3 + v0;

	xor_result 	<= sftmix xor subkey;
	
	data_o(63 downto 32)	<= v0;
	data_o(31 downto 0)		<= (v1 + xor_result) when mode_i = '0' else (v1 - xor_result);
	
	sum_o		<= sum_i;

	mode_o		<= mode_i;

	-----------------------------------
	-- Processes
	-----------------------------------

end halfround_2;
