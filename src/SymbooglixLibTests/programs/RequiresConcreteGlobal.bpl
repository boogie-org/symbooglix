var a:bv8;

// Bitvector functions
function {:bvbuiltin "bvsub"} bv8sub(bv8,bv8) returns(bv8);

procedure main()
requires a == 2bv8;
{
    var x:bv8;
    x := 7bv8;
    assert {:symbooglix_bp "now_concrete"} true;
    assert a == 2bv8;
    assert bv8sub(a,x) == 251bv8;
    assert {:symbooglix_bp "reachable"} true;
}
