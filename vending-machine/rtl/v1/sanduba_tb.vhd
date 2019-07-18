library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity sanduba_tb is
end entity sanduba_tb;

architecture sanduba_tb of sanduba_tb is
  signal clock, reset: std_logic := '0';
  
  signal M100, DEV: std_logic := '0';
  signal R_bacon, R_atum, R_green: std_logic := '0';
  signal busy: std_logic;
  signal D100: std_logic;
  signal BACON, ATUM, GREEN: std_logic;

  type test_record is record
    M100, DEV: std_logic;
    R_bacon, R_atum, R_green: std_logic;
  end record test_record;

  type records is array(natural range <>) of test_record;

  constant patterns : records := (
    -- adiciona 3 moedas e pede um sanduíche green 5ns - 115ns
    -- dispensa o sanduíche e depois devolve a moeda restante
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '0', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '1'),
    
    -- adiciona 2 moedas e pede um sanduíche de bacon 135ns - 185ns
    -- não faz nada e mantém as duas moedas
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '0', DEV => '0', R_bacon => '1', R_atum => '0', R_green => '0'),
    
    -- pede para devolver as duas moedas 205ns - 265ns
    -- devolve as duas moedas
    (M100 => '0', DEV => '1', R_bacon => '0', R_atum => '0', R_green => '0'),
    
    -- adiciona 1 moeda e pede dois sanduíches diferentes 285ns - 345ns
    -- reconhece o erro e devolve a moeda
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '0', DEV => '0', R_bacon => '1', R_atum => '1', R_green => '0'),
    
    -- insere 3 moedas e pede para devolvê-las 365ns - 505ns
    -- devolve as três moedas
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '1', DEV => '0', R_bacon => '0', R_atum => '0', R_green => '0'),
    (M100 => '0', DEV => '1', R_bacon => '0', R_atum => '0', R_green => '0')
  );
begin
  sanduba: entity work.sanduba
    port map (
      clock => clock,
      reset => reset,
      M100 => M100,
      DEV => DEV,
      R_bacon => R_bacon,
      R_atum => R_atum,
      R_green => R_green,
      busy => busy,
      D100 => D100,
      BACON => BACON,
      ATUM => ATUM,
      GREEN => GREEN
    );

  reset <= '1', '0' after 5 ns;
  clock <= not clock after 5 ns;
  
  test: process
    begin
      wait for 5 ns;
      for i in 0 to patterns'high loop
        M100 <= patterns(i).M100;
        DEV <= patterns(i).DEV;
        R_bacon <= patterns(i).R_bacon;
        R_atum <= patterns(i).R_atum;
        R_green <= patterns(i).R_green;
        wait for 10 ns;
        if M100 = '1' or DEV = '1' or R_bacon = '1' or R_atum = '1' or R_green = '1' then
          M100 <= '0';
          DEV <= '0';
          R_bacon <= '0';
          R_atum <= '0';
          R_green <= '0';
        end if;
        wait on busy until busy = '0' for 100 ns;
      end loop;
      wait for 20 ns;
    end process test;
end architecture sanduba_tb;