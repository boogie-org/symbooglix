// Bitvector functions
function {:bvbuiltin "bvadd"} bv8add(bv8,bv8) returns(bv8);

procedure main()
{
    var m:[bv8][bv8]bv32;
    var m2:[bv8]bv32;
    var m3:[bv8][bv8]bv32;
    var m4:[bv8,bv8]bv32;
    var index:bv8;
    var index2:bv8;
    var a:bv32;
    assume (forall x:bv8, y:bv8 :: m[x][y] == 0bv32);

    a := m[0bv8][1bv8];
    assert {:symbooglix_bp "check_read"} true;

    m[0bv8][2bv8] := 17bv32;
    assert {:symbooglix_bp "check_write"} true;

    m4[1bv8, 2bv8] := 12bv32;
    assert {:symbooglix_bp "check_write2"} true;

    a := m[index][ bv8add(index,1bv8)];
    assert {:symbooglix_bp "check_symbolic_read"} true;

    m[1bv8] := m2;
    assert {:symbooglix_bp "check_map_assign"} true;

    m := m3;
    assert {:symbooglix_bp "check_multidim_map_assign"} true;

}

