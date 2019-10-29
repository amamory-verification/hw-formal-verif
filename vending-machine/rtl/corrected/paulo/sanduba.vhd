library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity sanduba_paulo is
  port (
    clock, reset: in std_logic;
    m100, dev: in std_logic;
    r_bacon, r_atum, r_green: in std_logic;
    busy: out std_logic;
    d100: out std_logic;
    bacon, atum, green: out std_logic
  );
end entity sanduba_paulo;

architecture sanduba of sanduba_paulo is
  type TE is (ACTION, SOMA, NULO, SDEV, Sbacon, Satum, Sgreen, DEV_ONE);
  signal ea, pe: TE;
  signal credito: std_logic_vector(2 downto 0);
  signal erro: std_logic;
  signal sum: std_logic_vector(2 downto 0);
  signal aux: std_logic_vector(4 downto 0);

begin
  process(reset, clock)
  begin
    if reset = '1' then
      EA <= ACTION;
    elsif rising_edge(clock) then
      EA <= PE;
    end if;
  end process;

  aux <= R_bacon & R_atum & R_green & DEV & M100;
  sum <= ("00"&aux(0)) + ("00"&aux(1)) + ("00"&aux(2)) + ("00"&aux(3)) + ("00"&aux(4));
  erro <= '1' when sum >= 2  else '0';


  process(EA, M100, DEV, R_bacon, R_atum, R_green, erro, credito)
  begin
    case EA is
    when ACTION =>
      if DEV = '1' or erro = '1' then
        PE <= NULO;
      elsif M100 = '1' then
        if credito < 7 then
          PE <= SOMA;
        else
          PE <= DEV_ONE;
        end if;
      elsif R_bacon = '1' and credito >= 4 then
        PE <= Sbacon;
      elsif R_atum = '1' and credito >= 3 then
        PE <= Satum;
      elsif R_green = '1' and credito >= 2 then
        PE <= Sgreen;
      elsif R_green = '1' and credito < 2 then
        PE <= NULO;
      elsif R_bacon = '1' and credito < 4 then
        PE <= NULO;
      elsif R_atum = '1' and credito < 3 then
        PE <= NULO;
      else
        PE <= ACTION;
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
    when DEV_ONE =>
      PE <= ACTION;
    when OTHERS => null;
    end case;
  end process;

  process(reset, clock, EA)
  begin
    if reset = '1' then
      credito <= (others => '0');
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
      when DEV_ONE =>
        credito <= credito - 1;
      when OTHERS => null;
      end case;
    end if;
  end process;

  BACON <= '1' when EA = Sbacon else '0';
  ATUM <= '1' when EA = Satum else '0';
  GREEN <= '1' when EA = Sgreen else '0';
  D100 <= '1' when EA = SDEV or EA = DEV_ONE else '0';

  busy <= '0' when EA = ACTION else '1';
end architecture sanduba;
