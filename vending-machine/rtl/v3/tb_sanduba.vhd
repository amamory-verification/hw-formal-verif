--
--  Gustavo e Nathalia
--
library IEEE;
use IEEE.std_logic_1164.all;

entity tb is
end tb;

architecture tb of tb is
 
  signal clock, reset, M100, DEV, R_green, R_atum, R_bacon: STD_LOGIC := '0' ;
  signal D100, Green, Atum, Bacon, busy,erro: STD_LOGIC;

  type input_data is array (natural range <>) of std_logic_vector(4 downto 0);
  constant program : input_data :=   --   M100  DEV  R_green R_atum R_bacon
         (
		   "00110",  -- R_green e R_atum
		   "00101",  -- R_green e R_Bacon
           "00000",    -- nada
           "01000",   -- devolucao sem saldo
		   "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100   
		   "10000",   -- M100    --   R$ 8 reais
		   "00010",   -- R-atum
           "10000",   -- M100
           "10000",   -- M100   
		   "10000",   -- M100    --  R$ 3 reais
           "01000",   -- devolucao
           "10000",   -- M100
           "10000",   -- M100    --  R$ 2 reas
           "00100",   -- R-green
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100    --   R$ 3 reais
           "00010",   -- R_atum
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100    
		   "10000",   -- M100    --   R$ 4 reais
           "00001",   -- R_bacon
           "10000",   -- M100
		   "10000",   -- M100 
		   "10000",   -- M100 
		   "10000",   -- M100 4 reais
           "00010",   -- R_Atum
		   "10000",   -- M100
		   "10000",   -- M100 
		   "10000",   -- M100 
		   "10000",   -- M100 4 reais
           "01000"   -- Devolucao  
		   

 

         );  
begin

   reset <= '1', '0' after 3 ns;         -- reset  
   clock <= not clock after 5 ns;        -- clock com periodo = 10ns
   
   sandwich: entity work.maqSanduiche port map (clock=>clock, reset=>reset,
              M100=>M100, devo=>DEV, R_green=>R_green, R_atum=>R_atum, R_bacon=>R_bacon,
              busy=>busy, D100=>D100, Green=>Green, Atum=>Atum, Bacon=>Bacon);  
             
    p1: process     --- LE a rom com estimulos
    begin
   
       wait for 10 ns;    -- delay inicio de operacoes
      
       for i in 0 to program'high loop   
                M100      <= program(i)(4);
                DEV     <= program(i)(3);
                R_green   <= program(i)(2);
                R_atum    <= program(i)(1);
                R_bacon   <= program(i)(0);
                wait for 5 ns;
                if program(i) /= "00000" then  -- trata entrada nula
                     wait until busy='0';
                end if;
                wait for 5 ns;
       end loop;

       wait for 20 ns;    --delay para finaliza as operacoes
          
     end process;
  
end tb;