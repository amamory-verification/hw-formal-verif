library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity sanduba is
  port (
    clock, reset: in std_logic;
    M100, DEV: in std_logic;
    R_bacon, R_atum, R_green: in std_logic;
    busy: out std_logic;
    D100: out std_logic;
    BACON, ATUM, GREEN: out std_logic
  );
end entity sanduba;

architecture sanduba of sanduba is
  type TE is (ACTION, SOMA, NULO, SDEV, Sbacon, Satum, Sgreen);
  signal EA, PE: TE;
  signal credito: std_logic_vector(4 downto 0);
  signal erro: std_logic;
begin
  process(reset, clock)
  begin
    if reset = '1' then
      EA <= ACTION;
    elsif rising_edge(clock) then
      EA <= PE;
    end if;
  end process;
  
  erro <= (R_bacon and R_atum) or (R_bacon and R_green) or (R_atum and R_green);
  
  process(EA, M100, DEV, R_bacon, R_atum, R_green, erro, credito)
  begin
    case EA is
    when ACTION =>
      if M100 = '1' then
        PE <= SOMA;
      elsif DEV = '1' or erro = '1' then
        PE <= NULO;
      elsif R_bacon = '1' and credito >= 4 then
        PE <= Sbacon;
      elsif R_atum = '1' and credito >= 3 then
        PE <= Satum;
      elsif R_green = '1' and credito >= 2 then
        PE <= Sgreen;
      end if;
    when SOMA =>
      PE <= ACTION;
    when NULO =>
      if credito > 0 then
        PE <= SDEV;
      else
        PE <= ACTION;
      end if;
    when SDEV =>
      PE <= NULO;
    when Sbacon =>
      PE <= NULO;
    when Satum =>
      PE <= NULO;
    when Sgreen =>
      PE <= NULO;
    when OTHERS =>
      PE <= ACTION;
    end case;
  end process;
  
  process(reset, clock, EA)
  begin
    if reset = '1' then
      credito <= "00000";
    elsif rising_edge(clock) then
      case EA is
      when SOMA =>
        credito <= credito + 1;
      when SDEV =>
        credito <= credito - 1;
      when Sbacon =>
        credito <= credito - 4;
      when Satum =>
        credito <= credito - 3;
      when Sgreen =>
        credito <= credito - 2;
      when OTHERS =>
        credito <= credito;
      end case;
    end if;
  end process;
  
  BACON <= '1' when EA = Sbacon else '0';
  ATUM <= '1' when EA = Satum else '0';
  GREEN <= '1' when EA = Sgreen else '0';
  D100 <= '1' when EA = SDEV else '0';
  
  busy <= '0' when EA = ACTION else '1';
end architecture sanduba;