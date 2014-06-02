function {:bvbuiltin "bvugt"} bv8ugt(bv8,bv8) returns(bool);

procedure main(a:bv8)
requires bv8ugt(a, 2bv8);
{
    assert {:symbooglix_bp "reachable"} true;
}
