procedure foo(x:int) returns (r:int)
requires x > 5;
{
    r := x + 5;
    assert {:symbooglix_bp "in_foo"} true;
}

procedure main(x:int)
{
    var r:int;
    call r := foo(x);
    assert r >= 10;
    assert {:symbooglix_bp "past_assertion"} true;
}
