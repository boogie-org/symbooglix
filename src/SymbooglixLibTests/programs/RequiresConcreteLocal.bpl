procedure main(a:bv8)
requires a == 2bv8;
{
    assert {:symbooglix_bp "now_concrete"} true;
    assert a == 2bv8;
    assert {:symbooglix_bp "reachable"} true;
}
