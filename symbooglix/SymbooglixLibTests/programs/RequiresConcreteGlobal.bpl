var a:bv8;

// Bitvector functions
function {:bvbuiltin "bvsub"} bv8sub(bv8,bv8) returns(bv8);

procedure main()
requires a == 7bv8;
{
    var x:bv8;
    x := 7bv8;
    assert {:symbooglix_bp "now_concrete"} true;
    assert a == 7bv8;
    assert bv8sub(a,x) == 0bv8;
    assert {:symbooglix_bp "reached"} true;
}