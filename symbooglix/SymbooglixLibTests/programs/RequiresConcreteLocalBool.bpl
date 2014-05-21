procedure main(a:bool) returns (r:bool)
requires (a == true);
{
    assert {:symbooglix_bp "now_concrete"} true;
    assert a == true;
    assert {:symbooglix_bp "reachable"} true;
}
