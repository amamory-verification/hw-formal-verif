--! @file flop.vhd
--! @brief A simple flip-flop
--! @author Felipe Kuentzer, felipe.kuentzer@acad.pucrs.br
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
entity flop is
	generic (
		DATA_WIDTH		: integer	:= 8;			-- Data Width
		RST_ACT_LEVEL	: std_logic	:= '1'			-- Reset active level
	);
	port (
		rst				: in  std_logic;
		clk				: in  std_logic;
		data_i			: in  std_logic_vector(DATA_WIDTH - 1 downto 0);
		data_o 			: out std_logic_vector(DATA_WIDTH - 1 downto 0)
	);
end flop;

-------------------------------------------------------------------------------
-- Architecture
-------------------------------------------------------------------------------
architecture flop of flop is

	-----------------------------------
	-- Types
	-----------------------------------
	
	
	-----------------------------------
	-- Constants
	-----------------------------------

	
	-----------------------------------
	-- Signal Declarations
	-----------------------------------
	
	signal data		: std_logic_vector(DATA_WIDTH - 1 downto 0);
	
begin

	-----------------------------------
	-- Port Mappings
	-----------------------------------


	-----------------------------------
	-- Asynchronous Assignments
	-----------------------------------			

	data_o	<= data;

	-----------------------------------
	-- Processes
	-----------------------------------
	
	process(rst, clk)
	begin
		if rst = RST_ACT_LEVEL then
			data	<= (others => '0');
		elsif clk'event and clk = '1' then
			data	<= data_i;
		end if;
	end process;
	
end flop;


