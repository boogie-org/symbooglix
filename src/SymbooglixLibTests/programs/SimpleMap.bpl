procedure main()
{
    var m:[bv8]bv32;
    var a:bv32;
    var index:bv8;
    assume (forall x:bv8 :: m[x] == 0bv32);
    a := m[0bv8];
    assert {:symbooglix_bp "check_read_map"} true;

    m[3bv8] := 12bv32;
    assert {:symbooglix_bp "check_write_literal"} true;
    assert a != m[0bv8];

    m[1bv8] := a;
    assert {:symbooglix_bp "check_write_from_map"} true;

    m[index] := 7bv32;
    assert {:symbooglix_bp "check_write_symbolic_index"} true;
}
