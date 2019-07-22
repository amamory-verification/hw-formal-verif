library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity sanduba is
	port(
		m100, dev, r_green, r_atum, r_bacon, clock, reset: in std_logic;
		d100, green, atum, bacon, busy: out std_logic 
	);
end entity;

architecture maquina of sanduba is
	type state is (action, soma, sgreen, satum, sbacon, nulo, devolve); 
	signal ea, pe: state;
	signal count: std_logic_vector(4 downto 0);
	begin
	process(clock, reset)
	begin
	if reset = '1' then ea <= action;
	elsif rising_edge(clock) then
	ea <= pe;
	end if;
	end process;
	process(ea, count, m100, dev, r_green, r_atum, r_bacon)
	begin
	case ea is
	when action => if m100 = '1' then
					pe <= soma;
					elsif dev = '1' or (r_bacon = '1' and r_atum = '1') or (r_bacon = '1' and r_green = '1') 
					or (r_atum = '1' and r_green = '1') then pe <= nulo;
					elsif r_bacon = '1' and count >= 4 then pe <= sbacon;
					elsif r_atum = '1' and count >= 3 then pe <= satum;
					elsif r_green = '1' and count >= 2 then pe <= sgreen;
					end if;
	when soma=> pe <= action;
	when sgreen => pe <= nulo;
	when satum => pe <= nulo;
	when sbacon => pe <= nulo;
	when nulo => if count > 0 then pe <= devolve; else pe <= action;
					end if;
	when devolve => pe <= nulo;
	end case;
	end process;
	busy <= '0' when ea = action else '1';
	process(reset, clock)
	begin
	if reset = '1' then 
	count <= "00000";
	elsif rising_edge(clock) then 
	if ea = soma then count <= count + 1;
	elsif ea = sgreen then count <= count - 2; 
	elsif ea = satum then count <= count - 3; 
	elsif ea = sbacon then count <= count - 4;  
	elsif ea = devolve then count <= count - 1; 
	end if;
	end if;
	end process;
	green <= '1' when ea = sgreen else '0';
	atum <= '1' when ea = satum else '0';
	bacon <= '1' when ea = sbacon else '0';
	d100 <= '1' when ea = devolve else '0';
end architecture maquina;	
