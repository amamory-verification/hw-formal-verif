Library IEEE;
Use IEEE.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
--  Gustavo e Nathalia
entity maqSanduiche is
	port( M100, R_bacon, R_atum, R_green, clock, reset,devo: in std_logic;
		  D100, Bacon, Atum, Green,Busy: out std_logic
		);
end entity;

architecture sandy of maqSanduiche is
	type state is (Action, Soma, Nulo, Dev, SBacon, SAtum, SGreen);
	signal EA, PE: state;
	signal erro: std_logic;
	signal count:  std_logic_vector(4 downto 0);
	
begin
	process(reset, clock)
	begin
		if reset = '1' then
			EA <= Action;
		elsif rising_edge(clock) then
			EA  <= PE;
		end if;
	end process;
	
	process (M100,EA,count,PE,devo,erro,R_bacon,R_atum,R_green)
	begin
		case EA is 
		when Action =>
			if M100 = '1' then
				PE <= Soma;
			elsif R_bacon = '1' and count >= "00100" then
				PE <= SBacon;
			elsif R_Atum = '1' and count >= "00011" then
				PE <= SAtum;
			elsif R_green = '1' and count >= "00010" then
				PE <= SGreen;
			elsif erro = '1' then 
				PE <= Nulo;
			elsif devo = '1' then 
			PE <= Nulo;
			else PE <= Action;
			end if;
		
		when Soma =>	
			PE <= Action;
			
		when Nulo =>
			if count = "00000" then
				PE <= Action;
			else PE <= Dev;
			end if;
			
		when Dev =>
			PE <= Nulo;
		
		when SBacon =>
			PE <= Nulo;
		
		when SAtum =>
			PE <= Nulo;
			
		when SGreen =>
			PE <= Nulo;
		end case;
		end process;
	erro <= (R_bacon and R_atum) or (R_bacon and R_green) or (R_atum and R_green);
	process(reset, clock, EA)
	begin
		if reset = '1' then
			count <= "00000";
		elsif rising_edge(clock) then		
		case EA is
		when Action =>
			count <= count;		
		when Soma =>
			count <= count + "00001";
			
		when Dev =>
			if count > "00000" then 
				count <= count - "00001";
			end if;
		when SBacon =>
			count <= count - "00110";
		
		when SAtum =>
			count <= count - "00011";
			
		when SGreen =>
			count <= count - "00010";
		when Nulo =>
			count <= count;	
		end case;
		end if;

	end process;
		D100 <= '1' when EA = Dev else '0';
		Bacon <= '1' when EA = SBacon else '0';
		Atum <= '1' when EA = SAtum else '0';
		Green <= '1' when EA = SGreen else '0';
		Busy <= '0' when EA = Action else '1';

end architecture;
