entity attr8 is
end entity;

architecture test of attr8 is
begin

    process is
        type myint is range 1 to 3;
        variable x : integer;
    begin
        assert myint'val(1) = 1;
        assert myint'val(2) = 2;
        x := 1;
        assert myint'val(x) = 1;
        x := 2;
        assert myint'val(x) = 2;
        wait;
    end process;

end architecture;
