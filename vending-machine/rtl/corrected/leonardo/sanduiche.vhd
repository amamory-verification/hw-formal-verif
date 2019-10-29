library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all; 

entity sanduiche is
    port (
           clock:   in STD_LOGIC;
           reset:   in STD_LOGIC;
           m100:    in STD_LOGIC;
           dev:     in STD_LOGIC;
           r_green: in STD_LOGIC;
           r_atum:  in STD_LOGIC;
           r_bacon: in STD_LOGIC;

           busy:  out STD_LOGIC;
           d100:  out STD_LOGIC;
           green: out STD_LOGIC;
           atum: out STD_LOGIC;
           bacon: out STD_LOGIC
       );
end sanduiche;

architecture sanduiche of sanduiche is

        type STATES is (Action, SOMA, Sb, Sa, Sg, NULO, DEVOL); 
        signal ea, pe : STATES;   
    
        signal erro, overflow  :   std_logic;
        signal grana  :  std_logic_vector(2 downto 0);

begin    
 
    --
    --  tratamento de erro
    -- 
    erro <=  (R_bacon and R_atum) or (R_bacon and R_green) or (R_atum and R_green);
    --
    --  máquina de estados
    -- 
    process(reset,clock)
    begin
        if reset='1' then 
             EA <= Action;
        elsif rising_edge(clock) then
             EA <= PE;
        end  if;
     end process;

    process(EA, M100, DEV, R_bacon, R_green, R_atum, erro, grana, overflow)
    begin
       
          case EA is

             when Action =>  if DEV='1' or erro='1' or overflow='1' then
                                   PE <= NULO;
                             elsif  M100='1' then
                                  PE <= SOMA;
                            elsif R_bacon='1' and grana>=4 then
                                   PE <= Sb; 
                             elsif R_atum='1'  and grana>=3 then
                                   PE <= Sa; 
                             elsif R_green='1' and grana>=2 then
                                   PE <= Sg;       
                             elsif R_bacon='1' or R_atum='1' or R_green='1' then
                                  PE <= NULO;
                             else
                                  PE <= Action;
                             end if;

             when SOMA =>  PE <= Action;  
                                 
             when Sb | Sa | Sg  =>  PE<= NULO;
                                 
             when NULO =>  if grana=0 then
                                PE <= Action;  
                           else 
                                PE <= DEVOL; 
                          end if;
                                  
             when DEVOL =>  PE <= NULO; 
          end case;

    end process;

    --
    --  saídas dp circuito
    -- 
    GREEN <= '1'  when  EA=Sg     else '0';  
    ATUM  <= '1'  when  EA=Sa     else '0';  
    BACON <= '1'  when  EA=Sb     else '0';  
    busy  <= '0'  when  EA=Action else '1';  
    D100  <= '1'  when  EA=NULO and grana>0 else '0';  

    --
    --  contador do dinheiro acumulado
    --
    process (clock, reset)
      begin
        if reset ='1' then  
                 grana <= (others=>'0');
                 overflow <= '0';
        elsif rising_edge(clock) then 

			  if EA=SOMA then
				if grana /= "111" then
					grana <= grana + 1;
					overflow <= '0';
				else
					overflow <= '1';
				end if;
               elsif EA=Sg then
                  grana <= grana - 2;
               elsif EA=Sa then
                  grana <= grana - 3;
                elsif EA=Sb then
                  grana <= grana - 4;
                elsif EA=DEVOL then
                  if overflow = '0' then
					grana <= grana - 1;
				  else
				    overflow <= '0';
				  end if;
			    else
					overflow <= '0';
              end if;

        end if;
    end process;
              
end sanduiche;
