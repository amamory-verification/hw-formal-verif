library IEEE;
use IEEE.std_logic_1164.all;

entity tb is
end tb;

architecture tb of tb is
 
  signal clock, reset, M100, DEV, R_green, R_atum, R_bacon: STD_LOGIC := '0' ;
  signal D100, GREEN, ATUM, BACON, busy: STD_LOGIC;

  type input_data is array (natural range <>) of std_logic_vector(4 downto 0);

  constant program : input_data :=   --   M100  DEV  R_green R_atum R_bacon
         ( "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100
           --   "00000" ,   -- nada

           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100    --   R$ 7 reais
           "00001",   -- R_bacon 
           "10000",   -- M100
           "10000",   -- M100    --  R$ 2 reas
           "00011",   -- R_atum R_bacon  -- erro
           "10000",   -- M100
           "10000",   -- M100    --  R$ 2 reas
           "01000",   -- devolução
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100    --   R$ 3 reais
           "00010",   -- R_atum
           "10000",   -- M100
           "10000",   -- M100
           "10000",   -- M100    --   R$ 3 reais
           "00100",   -- R_green
           "10000",   -- M100
           "00001",   -- R_bacon   -- pede bacon sem saldo
           "00000",    -- nada
           "00000",    -- nada
           "00000",    -- nada
           "11111"    -- nada
         );  
begin

   reset <= '1', '0' after 3 ns;         -- reset  
   clock <= not clock after 5 ns;        -- clock with a period = 10ns

   -- circuit under test
   sandwich: entity work.sanduba port map (clock=>clock, reset=>reset,
              M100=>M100, DEV=>DEV, R_green=>R_green, R_atum=>R_atum, R_bacon=>R_bacon,
              busy=>busy, D100=>D100, GREEN=>GREEN, ATUM=>ATUM, BACON=>BACON );  
             
    p1: process     --- read the  ROM  with the stimulus
    begin
   
       wait for 10 ns;    -- delay to start the operations
      
       for i in 0 to program'high loop   
                M100      <= program(i)(4);
                DEV       <= program(i)(3);
                R_green   <= program(i)(2);
                R_atum    <= program(i)(1);
                R_bacon   <= program(i)(0);
                wait for 5 ns;
                if program(i) /= "00000" then  -- trata entrada nula
                     wait until busy='0';
                end if;
                wait for 5 ns;
       end loop;

       wait for 20 ns;    -- delay to finish the operations

       assert false
            report "A SIMULACAO TERMINOU!"
            severity failure;
                 
     end process;
  
end tb;
