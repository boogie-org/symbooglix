procedure main()
{
    var temp:int;
    call foo(temp);
    assert {:symbooglix_bp "unreachable"} false;
}

procedure foo(x:int);
requires x < 0;
requires x > 0;
